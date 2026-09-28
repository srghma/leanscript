import LeanScriptCli.Frontend
import LeanScriptCli.Check
import LeanScriptCli.RecCalls
import LeanScript.Term.Pretty
import LeanScript.Term.Optimize.Basic
import MoreJsTy.FromTerm
import MoreJsTy.PrintMini

/-!
# `leanscript`: Lean to JavaScript

```
leanscript [options] FILE.lean|Module.Name ...
```

For each file (or module, looked up as `Module/Name.lean` in the project root and in
`Tests/`), the tool elaborates the file, and for each public total function of it
(structurally recursive, or defined by well-founded recursion):

1. reads its definition (`Expr`) and translates it to a closed `LeanScript.Term`
   (`#leanscript_to_term`), evaluated to a value.  A function defined by well-founded
   recursion whose recursive calls are not all on subvalues, a member of a `mutual` block,
   and a function calling such functions are translated through their *open definition*
   (`LeanScript.Cli.openDef`): the `Term` is a function of the recursive functions called
   (`g_rec`), and the function is its fixed point;
2. optimises it (`Term.optimizeN`, proved to preserve `Term.eval`: `Term.optimizeN_eval`);
3. converts it to the JavaScript grammar `MoreJsTy` at the chosen configuration
   (`MoreJs.termToJs`);
4. prints it with `LanguageJavascriptMini` (`MoreJs.JsModule.toJs`).  For an open
   definition, the exported function binds each `g_rec` to the exported function `g`
   itself, and calls through it are made direct (`LeanScript.Cli.bindRecCalls`).

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
  /-- Write nothing for a file without a public total *function* (a candidate
      with at least one value parameter), and remove the outputs an earlier run of the tool
      wrote for it. -/
  functionsOnly : Bool := false
  inputs : List String := []

/-- The usage text. -/
def usage : String := "usage: leanscript [options] FILE.lean|Module.Name ...

Translates the public total functions of each Lean file (structurally recursive or defined by
well-founded recursion) to JavaScript, and
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

/-- The JavaScript name of the parameter of an open definition that stands for the recursive
    function `g`. -/
def recJsName (g : Name) : String := jsFunName g ++ "$rec"

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
  /-- Empty for a function translated directly.  For a function translated through its open
      definition (`LeanScript.Cli.openDef`: well-founded recursion, a `mutual` block, calls of
      such functions), the recursive functions it is abstracted over: `term` is the
      translation of the open definition, a function of one argument per function here
      (then of the parameters), and the function is its fixed point. -/
  recRefs : Array Name := #[]

/-- Process one file. -/
unsafe def processFile (o : CliOptions) (input : String) : IO Bool := do
  let file ← resolveInput input
  unless o.quiet do IO.eprintln s!"leanscript: elaborating {file}"
  let el ← elabFile file
  let (cands0, refused0) ← candidates el
  let cands := cands0
  if o.functionsOnly then
    let fns ← runTermElab el (cands0.filterM fun n => return !(← paramNames n).isEmpty)
    if fns.isEmpty then
      -- remove the outputs of an earlier run (only files this tool wrote)
      for suffix in ["-Term-unoptimized.txt", "-Term-optimized.txt", "-MoreJsTy.txt", ".js",
          ".check.mjs"] do
        let p := outPath o file suffix
        if ← p.pathExists then
          let txt ← IO.FS.readFile p
          if (txt.splitOn "generated by leanscript").length > 1 then IO.FS.removeFile p
      unless o.quiet do
        IO.eprintln s!"leanscript: {file}: skipped (no public total function)"
      return false
  let cands := if o.only.isEmpty then cands
    else cands.filter fun n => o.only.contains n.toString
  let mut refused : Array (Name × String) := refused0
  let mut done : Array Translated := #[]
  -- the functions whose calls are read through open definitions: those defined by
  -- well-founded recursion and the members of `mutual` blocks
  let recSet ← runTermElab el (cands0.filterM fun n => do
    if ← isWellFounded n then return true
    return (← recGroup n).size > 1)
  for n in cands do
    unless o.quiet do IO.eprintln s!"leanscript:   {n}"
    let r ← runTermElab el (do
        tryCatchRuntimeEx (do
          let ty ← typeString n
          let ps ← paramNames n
          let group ← recGroup n
          -- the recursive functions it calls: itself first, then the others
          let among := #[n] ++ (recSet ++ group).foldl
            (fun acc g => if g == n || acc.contains g then acc else acc.push g) #[]
          let refs ← unfoldRefs n among
          let refsRec := refs.filter fun g => recSet.contains g || (group.contains g && group.size > 1)
          let direct : Elab.TermElabM ClosedTerm := translate n
          let viaOpen : Elab.TermElabM (ClosedTerm × Array Name) := do
            let ct ← translate (← openDef n refs)
            return (ct, refs)
          let (ct, rs) ← if refsRec.isEmpty then pure ((← direct), #[])
            else if refs == #[n] && group.size == 1 then
              -- well-founded, calling only itself: its recursion may still be read as a
              -- structural one on a subvalue; if not, as a fixed point
              tryCatchRuntimeEx (return ((← direct), #[])) (fun _ => viaOpen)
            else viaOpen
          return Except.ok (ct, ty, ps, rs))
          (fun e => return Except.error (← e.toMessageData.toString)))
    match r with
    | .ok (ct, ty, ps, rs) =>
      let opt : ClosedTerm := { ct with term := ct.term.optimizeN o.rounds }
      done := done.push { name := n, ty, params := dedupNames (ps.map jsIdent), term := ct,
                          optimized := opt, recRefs := rs }
    | .error e =>
      unless o.quiet do
        if recSet.contains n then IO.eprintln s!"leanscript:   {n}: not translated (open definition): {e}"
      refused := refused.push (n, e)
  -- the JavaScript
  let mut funs : Array JsFun := #[]
  let mut helpers : Array JsHelper := #[]
  let mut jsRefused : Array (Name × String) := #[]
  let mut exported : Array (Name × String × Nat) := #[]
  let mut conv : Array (Translated × JsFun × List JsHelper) := #[]
  for t in done do
    let names := t.recRefs.toList.map (recJsName ·) ++ t.params
    match termToJs o.cfg (jsFunName t.name) t.name.toString names t.optimized with
    | .ok (f, hs) => conv := conv.push (t, f, hs)
    | .error e => jsRefused := jsRefused.push (t.name, e)
  -- an open definition needs every function it is abstracted over exported, with at least
  -- one parameter (a refusal can make another one refused: repeat until none is)
  let arityOf (cs : Array (Translated × JsFun × List JsHelper)) (g : Name) : Option Nat :=
    (cs.find? (·.1.name == g)).map fun (t, f, _) => f.params.length - t.recRefs.size
  let mut changed := true
  while changed do
    changed := false
    let mut kept := #[]
    for c@(t, f, _) in conv do
      let why? : Option String :=
        if t.recRefs.isEmpty then none
        -- (a function calling itself needs a parameter of its own; a constant calling other
        -- recursive functions, `def c := g 3`, is exported as a function of no parameter)
        else if f.params.length ≤ t.recRefs.size && t.recRefs.contains t.name then
          some "its JavaScript takes no parameter of its own, so it cannot be called recursively"
        else match t.recRefs.find? (fun g => (arityOf conv g).all (· == 0)) with
          | some g => some s!"it calls `{g}`, which is not translated to JavaScript"
          | none => none
      match why? with
      | some why =>
        jsRefused := jsRefused.push (t.name, why)
        changed := true
      | none => kept := kept.push c
    conv := kept
  for (t, f, hs) in conv do
    let k := t.recRefs.size
    let f := if k == 0 then f else
      let recs := (f.params.take k).zip t.recRefs.toList |>.map fun ((x, ty), g) =>
        (x, ty, jsFunName g, (arityOf conv g).getD 1)
      { f with params := f.params.drop k, body := bindRecCalls recs f.body }
    funs := funs.push f
    exported := exported.push (t.name, jsFunName t.name, f.params.length)
    helpers := hs.foldl addHelper helpers
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
      let recNote := if t.recRefs.isEmpty then "" else
        let args := ", ".intercalate (t.recRefs.toList.map fun g => s!"`{g}`")
        s!"-- recursive ({t.name}.leanscript_open): `{t.name}` is the function below applied to \
          {args} (its first {t.recRefs.size} parameter(s))\n"
      s!"-- {t.name} : {oneLine t.ty}\n{recNote}{ct.term.pretty}\n")
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
