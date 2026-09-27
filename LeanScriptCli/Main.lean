import LeanScriptCli.Frontend
import LeanScriptCli.Check
import LeanScript.Term.Pretty
import LeanScript.Term.Optimize
import MoreJsTy.FromTerm
import MoreJsTy.PrintMini

/-!
# `leanscript`: Lean to JavaScript

```
leanscript [options] FILE.lean|Module.Name ...
```

For each file (or module, looked up as `Module/Name.lean` in the project root and in
`Tests/`), the tool elaborates the file, and for each public, structurally total function
of it:

1. reads its definition (`Expr`) and translates it to a closed `LeanScript.Term`
   (`#leanscript_to_term`), evaluated to a value;
2. optimises it (`Term.optimizeN`, proved to preserve `Term.eval`: `Term.optimizeN_eval`);
3. converts it to the JavaScript grammar `MoreJsTy` at the chosen configuration
   (`MoreJs.termToJs`);
4. prints it with `LanguageJavascriptMini` (`MoreJs.JsModule.toJs`).

It writes, next to the file (or in `--out-dir`), where `FILE` is the path without `.lean`:

* `FILE-Term-unoptimized.txt`: the translations, as translated;
* `FILE-Term-optimized.txt`: the translations, optimised;
* `FILE-MoreJsTy.txt`: the JavaScript grammar, with the layout of every binder;
* `FILE.js`: the JavaScript module: the runtime helpers it needs, then one
  `export function` per translated function.

Every file starts with the configuration, and lists the functions that were not
translated, with the reason.
-/

open Lean LeanScript LeanScript.Cli MoreJs

/-- The options of the command line. -/
structure CliOptions where
  cfg : JsConfig := {}
  outDir : Option System.FilePath := none
  rounds : Nat := 3
  only : List String := []
  quiet : Bool := false
  check : Bool := false
  inputs : List String := []

/-- The usage text. -/
def usage : String := "usage: leanscript [options] FILE.lean|Module.Name ...

Translates the public, structurally total functions of each Lean file to JavaScript, and
writes next to the file (FILE is its path without `.lean`):
  FILE-Term-unoptimized.txt   the translations to LeanScript.Term
  FILE-Term-optimized.txt     the same, optimised (Term.optimizeN)
  FILE-MoreJsTy.txt           the JavaScript grammar, with the layout of every binder
  FILE.js                     the JavaScript module

options:
  --preset=faithful|pbo       a whole configuration (default: faithful, BigInt everywhere)
  --nat=num|bigint            how Nat is represented (also --int, --uint64, --int64, --bitvec)
  --array-fixed-int=typed|generic, --array-float=typed|generic,
  --array-uint64=typed|generic, --array-int64=typed|generic,
  --array-bitvec=round-up|exact|generic, --array-bool=uint8|generic,
  --array-char=uint32|generic how arrays of leaves are represented
  --out-dir=DIR               write the outputs to DIR instead of next to the file
  --optimize-rounds=N         how many times to run the optimiser (default 3)
  --only=f,g                  translate only these definitions
  --check                     also write FILE.check.mjs: calls of the exported functions on
                              sample arguments, compared with Lean's answers (run it with node)
  --quiet                     do not print the progress
  -h, --help                  this text"

/-- Parse the command line. -/
def parseArgs : List String → CliOptions → Except String CliOptions
  | [], o => pure { o with inputs := o.inputs.reverse }
  | a :: rest, o =>
    if a == "-h" || a == "--help" then throw usage
    else if a == "--quiet" then parseArgs rest { o with quiet := true }
    else if a == "--check" then parseArgs rest { o with check := true }
    else if a.startsWith "--" then
      match (a.drop 2).toString.splitOn "=" with
      | [k, v] =>
        if k == "preset" then
          match JsConfig.ofPresetName? v with
          | some c => parseArgs rest { o with cfg := c }
          | none => throw s!"unknown preset `{v}`"
        else if k == "out-dir" then parseArgs rest { o with outDir := some v }
        else if k == "optimize-rounds" then
          match v.toNat? with
          | some n => parseArgs rest { o with rounds := n }
          | none => throw s!"not a number: `{v}`"
        else if k == "only" then parseArgs rest { o with only := v.splitOn "," }
        else match o.cfg.setKnob? k v with
          | some c => parseArgs rest { o with cfg := c }
          | none => throw s!"unknown option or value: `{a}`\n\n{usage}"
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

/-- The characters a JavaScript identifier may contain (a conservative set). -/
def jsIdentChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '$'

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

/-- The JavaScript name of an exported function: the components of its Lean name joined by
    `_`. -/
def jsFunName (n : Name) : String :=
  jsIdent ("_".intercalate (n.components.map fun c => c.toString (escape := false)))

/-- The path of an output file: the input path without `.lean`, then `suffix`. -/
def outPath (o : CliOptions) (file : System.FilePath) (suffix : String) : System.FilePath :=
  let base := file.withExtension ""
  let base := match o.outDir with
    | some d => d / (base.fileName.getD "out")
    | none => base
  System.FilePath.mk (base.toString ++ suffix)

/-- One translated function. -/
structure Translated where
  name : Name
  ty : String
  params : List String
  term : ClosedTerm
  optimized : ClosedTerm

/-- Process one file. -/
unsafe def processFile (o : CliOptions) (input : String) : IO Bool := do
  let file ← resolveInput input
  unless o.quiet do IO.eprintln s!"leanscript: elaborating {file}"
  let el ← elabFile file
  let (cands, refused0) ← candidates el
  let cands := if o.only.isEmpty then cands
    else cands.filter fun n => o.only.contains n.toString
  let mut refused : Array (Name × String) := refused0
  let mut done : Array Translated := #[]
  for n in cands do
    unless o.quiet do IO.eprintln s!"leanscript:   {n}"
    let r ← runTermElab el (do
        tryCatchRuntimeEx (do
          let ct ← translate n
          let ty ← typeString n
          let ps ← paramNames n
          return Except.ok (ct, ty, ps))
          (fun e => return Except.error (← e.toMessageData.toString)))
    match r with
    | .ok (ct, ty, ps) =>
      let opt : ClosedTerm := { ct with term := ct.term.optimizeN o.rounds }
      done := done.push { name := n, ty, params := dedupNames (ps.map jsIdent), term := ct, optimized := opt }
    | .error e => refused := refused.push (n, e)
  -- the JavaScript
  let mut funs : Array JsFun := #[]
  let mut helpers : Array JsHelper := #[]
  let mut jsRefused : Array (Name × String) := #[]
  let mut exported : Array (Name × String × Nat) := #[]
  for t in done do
    match termToJs o.cfg (jsFunName t.name) t.name.toString t.params t.optimized with
    | .ok (f, hs) =>
      funs := funs.push f
      exported := exported.push (t.name, jsFunName t.name, f.params.length)
      helpers := hs.foldl addHelper helpers
    | .error e => jsRefused := jsRefused.push (t.name, e)
  let m : JsModule := { config := o.cfg, helpers := helpers.toList, funs := funs.toList }
  -- the header of every output
  let oneLine (s : String) : String := " ".intercalate (s.splitOn "\n" |>.map fun l => l.trimAscii.toString)
  let header (what : String) (extra : Array (Name × String)) : List String :=
    [s!"{what} of {file}, generated by leanscript", s!"configuration: {o.cfg.describe}"] ++
    (if el.missing.isEmpty then [] else
      [s!"imports not found (left out): {", ".intercalate (el.missing.toList.map toString)}"]) ++
    (if refused.isEmpty && extra.isEmpty then [] else ["not translated:"]) ++
    (refused ++ extra).toList.map fun (n, why) => s!"  {n}: {oneLine why}"
  let comment (ls : List String) : String := String.join (ls.map fun l => s!"-- {l}\n")
  let termFile (opt : Bool) : String :=
    comment (header (if opt then "The optimised translations" else "The translations") #[]) ++
    "\n" ++ "\n".intercalate (done.toList.map fun t =>
      let ct := if opt then t.optimized else t.term
      s!"-- {t.name} : {oneLine t.ty}\n{ct.term.pretty}\n")
  IO.FS.writeFile (outPath o file "-Term-unoptimized.txt") (termFile false)
  IO.FS.writeFile (outPath o file "-Term-optimized.txt") (termFile true)
  IO.FS.writeFile (outPath o file "-MoreJsTy.txt")
    (String.join ((header "The JavaScript grammar" jsRefused).map fun l => s!"// {l}\n") ++
      "\n" ++ m.pretty)
  IO.FS.writeFile (outPath o file ".js") (m.toJs (header "JavaScript" jsRefused))
  if o.check then
    let jsFile := (outPath o file ".js").fileName.getD "out.js"
    let cases ← runTermElab el (do
      let mut acc : Array CheckCase := #[]
      for (n, jsName, arity) in exported do
        match ← checksOf o.cfg n jsName arity with
        | some cs => acc := acc ++ cs.toArray
        | none => pure ()
      return acc)
    IO.FS.writeFile (outPath o file ".check.mjs") (checkModule jsFile cases.toList)
    unless o.quiet do
      IO.eprintln s!"leanscript: {file}: {cases.size} checks written"
  unless o.quiet do
    IO.eprintln s!"leanscript: {file}: {funs.size} exported, {refused.size + jsRefused.size} not translated"
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
