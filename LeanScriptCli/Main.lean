import LeanScriptCli.Frontend
import LeanScriptCli.Check
import LeanScript.Term.Pretty
import LeanScript.Term.Optimize.Basic
import LeanScript.Term.Optimize.FloatReassoc
import LeanScript.Term.Ownership.Walk
import JsTerm.Lower.FromTerm
import JsTerm.Print.Mini
import JsTerm.Print.Share
import JsTerm.Lower.Module
import JsTerm.Lower.ShareConsts
import JsTerm.Lower.Ident
import LanguageJavascriptCommon.Unicode

/-!
# `leanscript`: Lean to JavaScript

```
leanscript [options] FILE.lean|Module.Name ...
```

For each file (or module, looked up as `Module/Name.lean` in the project root and in
`Tests/`), the tool elaborates the file, and for each public total function of it that
`LeanScript.Term` supports — a **non-recursive** or **structurally recursive** definition:

1. reads its definition (`Expr`) and translates it to a closed `LeanScript.Term`
   (`#leanscript_to_term`), evaluated to a value;
2. optimises it (`Term.optimizeN`, proved to preserve `Term.eval`: `Term.optimizeN_eval`);
3. converts it to the JavaScript grammar `JsTerm` at each of the two presets
   (`MoreJs.JsConfig.presetPBO`, `MoreJs.JsConfig.presetFaithful`; `MoreJs.termToJs`);
4. shares the constants of the functions of a module (`MoreJs.hoistConsts`: a constructor
   without fields, a closure that captures nothing, … is built once, at the top of the module)
   and lists the operations of the runtime it calls (`MoreJs.mkModule`);
5. prints it with `LanguageJavascriptMini` (`MoreJs.JsModule.toJs`).

A definition by well-founded recursion, and a member of a `mutual` block, is not translated
for now (it is listed with the reason): `Term` has no general recursion.  (The translation of
such definitions through their *open definition*, `LeanScript.Cli.openDef`, and the binding
of the recursive calls in the JavaScript, `LeanScriptCli/RecCalls.lean_`, are disabled.)

It writes, next to the file (or in `--out-dir`), where `FILE` is the path without `.lean`:

* `FILE-Term-unoptimized.txt`: the translations, as translated;
* `FILE-Term-optimized.txt`: the translations, optimised;
* `FILE-pbo.js`, `FILE-faithful.js`: the JavaScript modules: the import of the runtime
  functions they call, from `runtime.js` of the project (or `--runtime`), by a path relative
  to the output file; the constants they share; then one `export const f = (…) => …` per
  translated function.

A literal that does not fit in the representation the preset gives its type (a `Nat` above
`2^53 - 1` where `Nat` is a `number`) is an error: the tool reports it and exits with a
failure.

Every file lists the functions that were not translated, with the reason; the JavaScript
files start with their configuration.
-/

open Lean LeanScript LeanScript.Cli MoreJs

/-- The options of the command line. -/
structure CliOptions where
  outDir : Option System.FilePath := none
  rounds : Nat := 3
  only : List String := []
  quiet : Bool := false
  check : Bool := false
  /-- Write nothing for a file without a public total *function* (a candidate
      with at least one value parameter), and remove the outputs an earlier run of the tool
      wrote for it. -/
  functionsOnly : Bool := false
  /-- Write nothing for a file without any public total definition (a function or a
      constant, `JsFun.isConst`), and remove the outputs an earlier run of the tool wrote
      for it. -/
  skipEmpty : Bool := false
  /-- The runtime the JavaScript imports (default: `runtime.js` in the project). -/
  runtime : Option System.FilePath := none
  /-- How the constructors without fields of a union are represented, at both presets
      (`JsConfig.nullaryRepr`: objects `{ tag: i }` by default, or the numbers `i`). -/
  nullary : NullaryRepr := .cells
  /-- Re-associate float chains before and after optimising (`Term.floatReassoc`), as the legacy
      backend does: **changes results** (IEEE arithmetic is not associative), so off by
      default. -/
  floatReassoc : Bool := false
  /-- (Internal, `LeanScript.Cli.panicsOf`.)  Mark each evaluation of a check on the standard
      error, for the parent process to see which calls make Lean panic. -/
  probePanics : Bool := false
  inputs : List String := []

/-- The presets every file is converted at, with the name of their outputs. -/
def presets : List (String × JsConfig) :=
  [("pbo", JsConfig.presetPBO), ("faithful", JsConfig.presetFaithful)]

/-- The usage text. -/
def usage : String := "usage: leanscript [options] FILE.lean|Module.Name ...

Translates the public total functions of each Lean file that LeanScript.Term supports
(non-recursive or structurally recursive definitions) to JavaScript, and writes next to the
file (FILE is its path without `.lean`):
  FILE-Term-unoptimized.txt   the translations to LeanScript.Term
  FILE-Term-optimized.txt     the same, optimised (Term.optimizeN)
  FILE-pbo.js                 the JavaScript module, numbers instead of BigInt and a List
                              as a JavaScript array (preset pbo)
  FILE-faithful.js            the JavaScript module, BigInt everywhere and a List as
                              tagged cons cells { tag: 1, _1: head, _2: tail } (preset
                              faithful)

options:
  --out-dir=DIR               write the outputs to DIR instead of next to the file
  --runtime=FILE              the runtime the JavaScript imports (default: runtime.js in
                              the project); the imports refer to it by a path relative to
                              each output file
  --optimize-rounds=N         how many times to run the optimiser (default 3)
  --only=f,g                  translate only these definitions
  --check                     also write FILE-pbo.check.mjs and FILE-faithful.check.mjs:
                              calls of the exported functions on sample arguments,
                              compared with Lean's answers (run them with node)
  --functions-only            skip a file that has no public total function
                              (a definition with at least one value parameter), removing
                              the outputs an earlier run wrote for it
  --skip-empty                skip a file that has no public total definition at all
                              (a function, or a constant: a definition without
                              parameters, exported as `export const x = value;`),
                              removing the outputs an earlier run wrote for it
  --nullary=cells|int         how a constructor without fields of a union that also has
                              constructors with fields is written: { tag: i } (cells,
                              the default) or the number i (int); at both presets
  --float-reassoc             after optimising, re-associate every chain of Float (Float32)
                              additions and of multiplications from the left and fold
                              neighbouring literals (1.0 + (2.0 + x) + 3.0 is
                              3.0 + x + 3.0), as purescript-backend-optimizer does.
                              CHANGES RESULTS (IEEE arithmetic is not associative), so the
                              output no longer computes what Lean computes; off by default
  --quiet                     do not print the progress
  -h, --help                  this text"

/-- Parse the command line. -/
def parseArgs : List String → CliOptions → Except String CliOptions
  | [], o => pure { o with inputs := o.inputs.reverse }
  | a :: rest, o =>
    if a == "-h" || a == "--help" then throw usage
    else if a == "--quiet" then parseArgs rest { o with quiet := true }
    else if a == "--check" then parseArgs rest { o with check := true }
    else if a == "--functions-only" then parseArgs rest { o with functionsOnly := true }
    else if a == "--skip-empty" then parseArgs rest { o with skipEmpty := true }
    else if a == "--float-reassoc" then parseArgs rest { o with floatReassoc := true }
    else if a == "--probe-panics" then parseArgs rest { o with probePanics := true }
    else if a.startsWith "--" then
      match (a.drop 2).toString.splitOn "=" with
      | [k, v] =>
        if k == "out-dir" then parseArgs rest { o with outDir := some v }
        else if k == "runtime" then parseArgs rest { o with runtime := some v }
        else if k == "optimize-rounds" then
          match v.toNat? with
          | some n => parseArgs rest { o with rounds := n }
          | none => throw s!"not a number: `{v}`"
        else if k == "only" then parseArgs rest { o with only := v.splitOn "," }
        else if k == "nullary" then
          match (JsConfig.setKnob? {} "nullary" v).map (·.nullaryRepr) with
          | some r => parseArgs rest { o with nullary := r }
          | none => throw s!"not a representation of constructors without fields: `{v}` (cells or int)"
        else throw s!"unknown option or value: `{a}`\n\n{usage}"
      | _ => throw s!"unknown option: `{a}`\n\n{usage}"
    else parseArgs rest { o with inputs := a :: o.inputs }

/-- The file of an input: a path to a `.lean` file, or a module name looked up in the
    project root and in `Tests/`. -/
def resolveInput (a : String) : IO System.FilePath := do
  if a.endsWith ".lean" then return a
  let rel : System.FilePath := System.FilePath.mk ("/".intercalate (a.splitOn ".") ++ ".lean")
  let root ← projectRoot
  for dir in [(".": System.FilePath), root, root / "Tests"] do
    if ← (dir / rel).pathExists then return dir / rel
  throw (IO.userError s!"cannot find the module `{a}` (looked for {rel})")

/-- JavaScript's reserved words. -/
def jsReserved : List String :=
  ["break", "case", "catch", "class", "const", "continue", "debugger", "default", "delete",
   "do", "else", "enum", "export", "extends", "false", "finally", "for", "function", "if",
   "import", "in", "instanceof", "new", "null", "return", "super", "switch", "this", "throw",
   "true", "try", "typeof", "var", "void", "while", "with", "yield", "let", "static",
   "implements", "interface", "package", "private", "protected", "public", "await",
   "arguments", "eval", "undefined", "NaN", "Infinity"]

/-- Whether a name is not written as it is: a reserved word of JavaScript (`jsReserved`), or a
    global name the printed code reads (`MoreJs.jsReservedNames`: `Math`, `String`, `BigInt`…;
    the contextual keywords `async`, `of`, `get`, `set` are ordinary names). -/
def jsReservedIdent (s : String) : Bool :=
  jsReserved.contains s ||
    (MoreJs.jsReservedNames.contains s && !["async", "of", "get", "set"].contains s)

/-- Whether a character beyond ASCII may stand in an identifier: at its start (`ID_Start`) or
    after it (`ID_Continue`). -/
def jsIdChar (first : Bool) (c : Char) : Bool :=
  if first then Language.JavaScript.Unicode.isIdStart c
  else Language.JavaScript.Unicode.isIdContinue c

/-- A JavaScript identifier for a Lean name component or binder name (never containing `$`,
    which the generated names use): letters and digits are kept, other characters escaped by
    their code points (`a.b` is `a_x2eb`, `foo'` is `foo_x27`), and no two names get the same
    identifier (`MoreJs.Ident.ident_injective`). -/
def jsIdent (s : String) : String :=
  MoreJs.Ident.ident jsIdChar jsReservedIdent s

/-- A JavaScript name for a parameter: as `jsIdent`, but every other character is written `_`
    (`x'` is `x_`) — a parameter is local, and `dedupNames` makes the names of a function
    distinct. -/
def jsParamName (s : String) : String :=
  let s := String.ofList (s.toList.map fun c =>
    if c.isAlphanum || c == '_' || (c.toNat ≥ 128 && jsIdChar false c) then c else '_')
  let s := if s.isEmpty then "_" else s
  let s := if s.front.isDigit || (s.front.toNat ≥ 128 && !jsIdChar true s.front) then "_" ++ s
    else s
  if jsReservedIdent s then s ++ "_" else s

/-- Make parameter names distinct: a name met again (Lean allows two binders with the same
    name, and the anonymous binders of `Nat → Nat → Nat` are all `a`) gets a numeric suffix. -/
def dedupNames (ps : List String) : List String := Id.run do
  let mut seen : List String := []
  let mut out : Array String := #[]
  for p in ps do
    let mut q := p
    let mut i := 1
    while seen.contains q do
      q := s!"{p}{i}"
      i := i + 1
    seen := q :: seen
    out := out.push q
  return out.toList

/-- The JavaScript name of an exported function: the components of its Lean name, each made
    an identifier, joined by `$` (`ArrayTest.test1` is `ArrayTest$test1`; `jsIdent` never
    writes a `$`, so the separator cannot be confused with a part of a component). -/
def jsFunName (n : Name) : String :=
  MoreJs.Ident.name jsIdChar jsReservedIdent (n.components.map (·.toString (escape := false)))

/-- The path of an output file: the input path without `.lean`, then `suffix`. -/
def outPath (o : CliOptions) (file : System.FilePath) (suffix : String) : System.FilePath :=
  let base := file.withExtension ""
  let base := match o.outDir with
    | some d => d / (base.fileName.getD "out")
    | none => base
  System.FilePath.mk (base.toString ++ suffix)

/-- The suffixes of every output the tool writes (and of the outputs of its earlier versions,
    removed with `--functions-only` or `--skip-empty`). -/
def outputSuffixes : List String :=
  ["-Term-unoptimized.txt", "-Term-optimized.txt"] ++
  presets.flatMap (fun (p, _) => [s!"-JsTerm-{p}.txt", s!"-{p}.js", s!"-{p}.check.mjs"]) ++
  ["-JsTerm.txt", ".js", ".check.mjs"]

/-- One translated function: its translation (`term`), and the optimised translation with the
    versions of it that are generated (`optimized`: the first borrows every parameter, the
    others own some of them and update them in place, `LeanScript.Term.Ownership`). -/
structure Translated where
  name : Name
  ty : String
  params : List String
  term : ClosedTerm
  optimized : OwnedTerm

/-- The parameters a version owns, by name. -/
def ownedNames (params : List String) (v : OwnVersion) : List String :=
  (v.owned.zipIdx.filter (·.1)).map fun (_, i) => params.getD i s!"p{i}"

/-- What a version is, in words (a line of the comment above it). -/
def versionNote (params : List String) (v : OwnVersion) : String :=
  let ps := ", ".intercalate ((ownedNames params v).map fun p => s!"`{p}`")
  s!"owns {ps}: its caller gives {if (ownedNames params v).length == 1 then "it" else "them"} \
    up, and it may update {if (ownedNames params v).length == 1 then "it" else "them"} in place \
    ({v.cost.inPlace} update(s) in place, {v.cost.copies} cop{if v.cost.copies == 1 then "y" else "ies"} \
    of arrays)"

/-- Why a candidate is not translated for now, if it is not: `Term` supports non-recursive
    and structurally recursive definitions only. -/
def unsupportedRecursion? (n : Name) : MetaM (Option String) := do
  -- a member of a `mutual` block defined by structural recursion is a candidate (the
  -- translator reads the whole group, `LeanScript.TermElab.ToTerm`)
  if ← isWellFounded n then
    if (← recGroup n).size > 1 then
      return some "a member of a `mutual` block defined by well-founded recursion: only \
        non-recursive and structurally recursive definitions are translated (to `Term`)"
    return some "defined by well-founded recursion: only non-recursive and structurally \
      recursive definitions are translated (to `Term`)"
  return none

/-- The components of an absolute, normalised path (`.` and `..` resolved). -/
def pathComponents (p : System.FilePath) : List String :=
  (p.toString.splitOn "/").foldl (fun acc c =>
    if c.isEmpty || c == "." then acc
    else if c == ".." then acc.dropLast
    else acc ++ [c]) []

/-- The path of `target` relative to the directory `fromDir` (both absolute), as an import
    specifier: `./x`, `../../runtime`. -/
def relativePath (fromDir target : System.FilePath) : String :=
  let a := pathComponents fromDir
  let b := pathComponents target
  let common := (a.zip b).takeWhile (fun (x, y) => x == y) |>.length
  let ups := (a.drop common).map fun _ => ".."
  let rel := ups ++ b.drop common
  match rel with
  | [] => "."
  | ".." :: _ => "/".intercalate rel
  | _ => "./" ++ "/".intercalate rel

/-- The runtime, as an absolute path. -/
def runtimeOf (o : CliOptions) : IO System.FilePath := do
  let f ← match o.runtime with
    | some f => pure f
    | none => return (← IO.FS.realPath (← projectRoot)) / "runtime.js"
  if ← f.pathExists then IO.FS.realPath f else
    throw (IO.userError s!"the runtime {f} does not exist")

/-- The imports of a module that the runtime (its source `src`) does not export. -/
def missingExports (src : String) (imports : List String) : List String :=
  imports.filter fun n => (src.splitOn s!"export const {n} =").length < 2

/-- Process one file. -/
unsafe def processFile (o : CliOptions) (input : String) : IO Bool := do
  let file ← resolveInput input
  unless o.quiet do IO.eprintln s!"leanscript: elaborating {file}"
  let el ← elabFile file
  let (cands0, refused0) ← candidates el
  -- the recursive types the candidates mention, declared as the signature of the program
  let el ← autoSignature el cands0
  -- the definitions `Term` does not support are refused
  let mut refused : Array (Name × String) := refused0
  let mut cands : Array Name := #[]
  for n in cands0 do
    match ← runTermElab el (unsupportedRecursion? n) with
    | some why => refused := refused.push (n, why)
    | none => cands := cands.push n
  if o.functionsOnly || o.skipEmpty then
    let fns ← if o.functionsOnly then
        runTermElab el (cands.filterM fun n => return !(← paramNames n).isEmpty)
      else pure cands
    if fns.isEmpty then
      -- remove the outputs of an earlier run (only files this tool wrote)
      for suffix in outputSuffixes do
        let p := outPath o file suffix
        if ← p.pathExists then
          let txt ← IO.FS.readFile p
          if (txt.splitOn "generated by leanscript").length > 1 then IO.FS.removeFile p
      unless o.quiet do
        IO.eprintln s!"leanscript: {file}: skipped (no public non-recursive or structurally \
          recursive {if o.functionsOnly then "function" else "definition"})"
      return false
  let todo := if o.only.isEmpty then cands
    else cands.filter fun n => o.only.contains n.toString
  let mut done : Array Translated := #[]
  for n in todo do
    unless o.quiet do IO.eprintln s!"leanscript:   {n}"
    let r ← runTermElab el (do
        tryCatchRuntimeEx (do
          let ty ← typeString n
          let ct ← translate n
          let ps ← paramNames n
          return Except.ok (ct, ty, ps))
          (fun e => return Except.error (← e.toMessageData.toString)))
    match r with
    | .ok (ct, ty, ps) =>
      -- `--float-reassoc`: the chains are regrouped before optimising (as they are written,
      -- before `Neu.floatComm` commutes their operands) and again after (the chains inlining
      -- makes)
      let t := if o.floatReassoc then (ct.term.floatReassoc.optimizeN o.rounds).floatReassoc
        else ct.term.optimizeN o.rounds
      let opt : ClosedTerm := { ct with term := t }
      done := done.push { name := n, ty, params := dedupNames (ps.map jsParamName), term := ct,
                          optimized := opt.withOwnership }
    | .error e => refused := refused.push (n, e)
  -- the definitions that only rename one translated before them: another name of its function
  let aliases : List (String × String) ← runTermElab el do
    let mut acc : List (String × String) := []
    for (t, i) in done.toList.zipIdx do
      if let some c ← aliasOf? t.name ((done.toList.take i).map (·.name)).toArray then
        let some tc := done.find? (·.name == c) | continue
        -- the versions owning parameters are renamed one by one (the same, since the two
        -- definitions have the same translation)
        let sfx (x : Translated) := (x.optimized.versions.drop 1).map (·.suffix)
        if sfx t == sfx tc then
          acc := acc ++ ("" :: sfx t).map fun v => (jsFunName t.name ++ v, jsFunName c ++ v)
    return acc
  -- the translated definitions marked `@[noinline]`: a literal constant renaming one of them
  -- still refers to it (`aliasFuns`)
  let noInline : List String := (done.toList.filter fun t =>
      Lean.Compiler.hasNoInlineAttribute el.env t.name).map fun t => jsFunName t.name
  let oneLine (s : String) : String :=
    " ".intercalate (s.splitOn "\n" |>.map fun l => l.trimAscii.toString)
  let notTranslated (extra : Array (Name × String)) : List String :=
    (if refused.isEmpty && extra.isEmpty then [] else ["not translated:"]) ++
    (refused ++ extra).toList.map fun (n, why) => s!"  {n}: {oneLine why}"
  let missing : List String := if el.missing.isEmpty then [] else
    [s!"imports not found (left out): {", ".intercalate (el.missing.toList.map toString)}"]
  let comment (ls : List String) : String := String.join (ls.map fun l => s!"-- {l}\n")
  -- the `Term` files: no configuration (it only concerns the conversion to JavaScript)
  let termFile (opt : Bool) : String :=
    comment ([s!"{if opt then "The optimised translations" else "The translations"} of {file}, \
      generated by leanscript"] ++ missing ++ notTranslated #[]) ++
    "\n" ++ "\n".intercalate (done.toList.map fun t =>
      let ct := if opt then t.optimized.term else t.term
      -- the versions owning some parameters (`LeanScript.Term.Ownership`)
      let vs := if opt then t.optimized.versions.drop 1 else []
      let notes := String.join (vs.map fun v =>
        s!"-- version {jsFunName t.name ++ v.suffix}: {versionNote t.params v}\n")
      s!"-- {t.name} : {oneLine t.ty}\n{notes}{ct.term.pretty}\n")
  IO.FS.writeFile (outPath o file "-Term-unoptimized.txt") (termFile false)
  IO.FS.writeFile (outPath o file "-Term-optimized.txt") (termFile true)
  -- the calls of the checks that make Lean panic, with its message (`LeanScript.Cli.panicsOf`),
  -- found by a child process when the translations call `lean_panic_fn`
  let panics : Std.HashMap String (Std.HashMap String String) ← do
    let callsPanic := ((termFile true).splitOn "lean_panic_fn").length > 1
    if !o.check || o.probePanics || !callsPanic then
      pure {}
    else
      let tmp ← IO.FS.createTempDir
      let args : Array String :=
        #["--probe-panics", "--check", "--quiet", s!"--out-dir={tmp}",
          s!"--optimize-rounds={o.rounds}",
          s!"--nullary={match o.nullary with | .cells => "cells" | .smallInt => "int"}"] ++
        (if o.only.isEmpty then #[] else #[s!"--only={",".intercalate o.only}"]) ++
        (match o.runtime with | some r => #[s!"--runtime={r}"] | none => #[]) ++
        (if o.floatReassoc then #["--float-reassoc"] else #[]) ++ #[file.toString]
      let out ← IO.Process.output { cmd := (← IO.appPath).toString, args }
      IO.FS.removeDirAll tmp
      pure (panicsOf out.stderr)
  -- the JavaScript, at each preset
  let mut nExported := 0
  let mut nJsRefused := 0
  let rtFile ← runtimeOf o
  let rtSrc ← IO.FS.readFile rtFile
  let mut fatal : Array String := #[]
  for (preset, cfg) in presets do
    let cfg := { cfg with nullaryRepr := o.nullary }
    let mut funs : Array JsFun := #[]
    let mut jsRefused : Array (Name × String) := #[]
    let mut exported : Array (Name × String × Nat × List String × Bool) := #[]
    for t in done do
      match termToJs cfg (jsFunName t.name) t.name.toString t.params t.optimized.term with
      | .ok f =>
        funs := funs.push f
        -- the versions owning some parameters, after the one borrowing them all
        let mut sfxs : List String := []
        for v in t.optimized.versions.drop 1 do
          match termToJs cfg (jsFunName t.name ++ v.suffix) t.name.toString t.params
              t.optimized.term v.owned with
          | .ok fv =>
            funs := funs.push { fv with notes := [versionNote t.params v] }
            sfxs := sfxs ++ [v.suffix]
          | .error _ => pure ()
        let holdsArrays := (Own.fnParams t.optimized.term.τ).any Own.Ty.needsOwn
        exported := exported.push (t.name, jsFunName t.name, f.params.length, sfxs, holdsArrays)
      | .error e =>
        if isLiteralTooBig e then fatal := fatal.push s!"{t.name} (preset {preset}): {e}"
        jsRefused := jsRefused.push (t.name, e)
    -- functions that differ only in the literal initial value of their first variable share one
    -- worker (`JsTerm.Print.Share`: the `mutual` groups recursing on a `Nat`)
    -- (and a definition that only renames another one is another name of its function; the
    -- value of a constant reads the values of the constants before it by their names,
    -- `shareConstValues`)
    let m := mkModule cfg (shareConstValues (aliasFuns aliases (shareWorkers funs.toList) noInline))
    for n in missingExports rtSrc m.imports do
      fatal := fatal.push s!"preset {preset}: the runtime {rtFile} does not export {n}"
    let header (what : String) : List String :=
      [s!"{what} of {file} (preset {preset}), generated by leanscript",
        s!"configuration: {cfg.describe}"] ++
        (if o.floatReassoc then ["--float-reassoc: float chains re-associated; results may differ from Lean's"]
         else []) ++ missing ++ notTranslated jsRefused
    let jsPath := outPath o file s!"-{preset}.js"
    let jsDir ← IO.FS.realPath ((jsPath.parent.getD ".").toString |> fun s =>
      if s.isEmpty then "." else s)
    -- the grammar dump `FILE-JsTerm-{preset}.txt` is no longer written: remove a stale one
    let staleDump := outPath o file s!"-JsTerm-{preset}.txt"
    if ← staleDump.pathExists then IO.FS.removeFile staleDump
    IO.FS.writeFile jsPath (m.toJs (header "JavaScript") (relativePath jsDir rtFile))
    if o.check then
      let jsFile := jsPath.fileName.getD "out.js"
      if o.probePanics then probeMark s!"{probePreset}{preset}"
      let cases ← runTermElab el (do
        let mut acc : Array CheckCase := #[]
        for (n, jsName, arity, sfxs, twice) in exported do
          match ← checksOf cfg n jsName arity (versions := sfxs) (twice := twice)
              (probe := o.probePanics) (panics := panics.getD preset {}) with
          | some cs => acc := acc ++ cs.toArray
          | none => pure ()
        return acc)
      IO.FS.writeFile (outPath o file s!"-{preset}.check.mjs") (checkModule jsFile cases.toList)
      unless o.quiet do
        IO.eprintln s!"leanscript: {file} ({preset}): {cases.size} checks written"
    nExported := funs.size
    nJsRefused := max nJsRefused jsRefused.size
  unless o.quiet do
    IO.eprintln s!"leanscript: {file}: {nExported} exported, {refused.size + nJsRefused} not translated"
  unless fatal.isEmpty do
    throw (IO.userError ("\n".intercalate fatal.toList))
  return true

unsafe def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .error msg =>
    IO.eprintln msg
    return (if msg == usage then 0 else 1)
  | .ok o =>
    if o.inputs.isEmpty then
      IO.eprintln usage
      return 1
    initPath
    enableInitializersExecution
    let mut ok := true
    for i in o.inputs do
      try
        discard <| processFile o i
      catch e =>
        IO.eprintln s!"leanscript: {i}: {e}"
        ok := false
    -- stops the checks still running after their time budget (see `evalWithTimeout`)
    IO.Process.exit (if ok then 0 else 1)
