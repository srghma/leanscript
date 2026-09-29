import LeanScriptCli.Frontend
import LeanScriptCli.Check
import LeanScript.Term.Pretty
import LeanScript.Term.Optimize.Basic
import JsTerm.Lower.FromTerm
import JsTerm.Print.Mini
import JsTerm.Lower.Module

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
  /-- The runtime the JavaScript imports (default: `runtime.js` in the project). -/
  runtime : Option System.FilePath := none
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

/-- A JavaScript identifier for a Lean name component or binder name (never containing `$`,
    which the generated names use). -/
def jsIdent (s : String) : String :=
  let s := String.ofList (s.toList.map fun c => if c.isAlphanum || c == '_' then c else '_')
  let s := if s.isEmpty then "_" else s
  let s := if (s.front).isDigit then "_" ++ s else s
  if jsReserved.contains s then s ++ "_" else s

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
  "$".intercalate (n.components.map fun c => jsIdent (c.toString (escape := false)))

/-- The path of an output file: the input path without `.lean`, then `suffix`. -/
def outPath (o : CliOptions) (file : System.FilePath) (suffix : String) : System.FilePath :=
  let base := file.withExtension ""
  let base := match o.outDir with
    | some d => d / (base.fileName.getD "out")
    | none => base
  System.FilePath.mk (base.toString ++ suffix)

/-- The suffixes of every output the tool writes (and of the outputs of its earlier versions,
    removed with `--functions-only`). -/
def outputSuffixes : List String :=
  ["-Term-unoptimized.txt", "-Term-optimized.txt"] ++
  presets.flatMap (fun (p, _) => [s!"-JsTerm-{p}.txt", s!"-{p}.js", s!"-{p}.check.mjs"]) ++
  ["-JsTerm.txt", ".js", ".check.mjs"]

/-- One translated function. -/
structure Translated where
  name : Name
  ty : String
  params : List String
  term : ClosedTerm
  optimized : ClosedTerm

/-- Why a candidate is not translated for now, if it is not: `Term` supports non-recursive
    and structurally recursive definitions only. -/
def unsupportedRecursion? (n : Name) : MetaM (Option String) := do
  if (← recGroup n).size > 1 then
    return some "a member of a `mutual` block: only non-recursive and structurally recursive \
      definitions are translated (to `Term`)"
  if ← isWellFounded n then
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
  -- the definitions `Term` does not support are refused
  let mut refused : Array (Name × String) := refused0
  let mut cands : Array Name := #[]
  for n in cands0 do
    match ← runTermElab el (unsupportedRecursion? n) with
    | some why => refused := refused.push (n, why)
    | none => cands := cands.push n
  if o.functionsOnly then
    let fns ← runTermElab el (cands.filterM fun n => return !(← paramNames n).isEmpty)
    if fns.isEmpty then
      -- remove the outputs of an earlier run (only files this tool wrote)
      for suffix in outputSuffixes do
        let p := outPath o file suffix
        if ← p.pathExists then
          let txt ← IO.FS.readFile p
          if (txt.splitOn "generated by leanscript").length > 1 then IO.FS.removeFile p
      unless o.quiet do
        IO.eprintln s!"leanscript: {file}: skipped (no public non-recursive or structurally \
          recursive function)"
      return false
  let todo := if o.only.isEmpty then cands
    else cands.filter fun n => o.only.contains n.toString
  let mut done : Array Translated := #[]
  for n in todo do
    unless o.quiet do IO.eprintln s!"leanscript:   {n}"
    let r ← runTermElab el (do
        tryCatchRuntimeEx (do
          let ty ← typeString n
          let ps ← paramNames n
          let ct ← translate n
          return Except.ok (ct, ty, ps))
          (fun e => return Except.error (← e.toMessageData.toString)))
    match r with
    | .ok (ct, ty, ps) =>
      let opt : ClosedTerm := { ct with term := ct.term.optimizeN o.rounds }
      done := done.push { name := n, ty, params := dedupNames (ps.map jsIdent), term := ct,
                          optimized := opt }
    | .error e => refused := refused.push (n, e)
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
      let ct := if opt then t.optimized else t.term
      s!"-- {t.name} : {oneLine t.ty}\n{ct.term.pretty}\n")
  IO.FS.writeFile (outPath o file "-Term-unoptimized.txt") (termFile false)
  IO.FS.writeFile (outPath o file "-Term-optimized.txt") (termFile true)
  -- the JavaScript, at each preset
  let mut nExported := 0
  let mut nJsRefused := 0
  let rtFile ← runtimeOf o
  let rtSrc ← IO.FS.readFile rtFile
  let mut fatal : Array String := #[]
  for (preset, cfg) in presets do
    let mut funs : Array JsFun := #[]
    let mut jsRefused : Array (Name × String) := #[]
    let mut exported : Array (Name × String × Nat) := #[]
    for t in done do
      match termToJs cfg (jsFunName t.name) t.name.toString t.params t.optimized with
      | .ok f =>
        funs := funs.push f
        exported := exported.push (t.name, jsFunName t.name, f.params.length)
      | .error e =>
        if isLiteralTooBig e then fatal := fatal.push s!"{t.name} (preset {preset}): {e}"
        jsRefused := jsRefused.push (t.name, e)
    let m := mkModule cfg funs.toList
    for n in missingExports rtSrc m.imports do
      fatal := fatal.push s!"preset {preset}: the runtime {rtFile} does not export {n}"
    let header (what : String) : List String :=
      [s!"{what} of {file} (preset {preset}), generated by leanscript",
        s!"configuration: {cfg.describe}"] ++ missing ++ notTranslated jsRefused
    let jsPath := outPath o file s!"-{preset}.js"
    let jsDir ← IO.FS.realPath ((jsPath.parent.getD ".").toString |> fun s =>
      if s.isEmpty then "." else s)
    -- the grammar dump `FILE-JsTerm-{preset}.txt` is no longer written: remove a stale one
    let staleDump := outPath o file s!"-JsTerm-{preset}.txt"
    if ← staleDump.pathExists then IO.FS.removeFile staleDump
    IO.FS.writeFile jsPath (m.toJs (header "JavaScript") (relativePath jsDir rtFile))
    if o.check then
      let jsFile := jsPath.fileName.getD "out.js"
      let cases ← runTermElab el (do
        let mut acc : Array CheckCase := #[]
        for (n, jsName, arity) in exported do
          match ← checksOf cfg n jsName arity with
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
