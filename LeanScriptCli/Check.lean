import Lean
import JsTerm.Ty.Config

/-!
# Differential checks of the generated JavaScript against Lean

With `--check`, `leanscript` writes, next to `FILE.js`, a module `FILE.check.mjs` that calls
the exported functions on sample arguments and compares each answer with the one **Lean**
gives for the same call (computed by the tool with `Lean.Meta.evalExpr`, in the environment
of the elaborated file).  `node FILE.check.mjs` prints the checks and exits with a non-zero
status when one fails.

Only functions whose parameters and result are all of a *sample type* are checked: `Nat`,
`Int`, `Bool`, `String`, `Char`, `Float`, the fixed-width integers (`UInt8` … `UInt64`,
`Int8` … `Int64`), and `Array` and `List` of `Nat`, `Int`, `Bool` or
`String` (a list is a JavaScript array, or cons cells under `ListRepr.taggedUnion`; either is
printed as its array, `#[…]`), structures of such fields (a structure of one field is unboxed:
its sample is its field's), and some unions.
A value is compared through its printed form (`toString` in Lean; the same format computed
in JavaScript), except a `Float`, which is compared bit for bit (`Float.toBits`).
-/

open Lean Meta MoreJs

namespace LeanScript.Cli

/-- The types the checks can produce samples of and compare. -/
inductive SType where
  | nat | int | bool | string | char | float
  /-- `UInt8`, `UInt16`, `UInt32`, `UInt64` (`bits` is the width). -/
  | uint (bits : Nat)
  /-- `Int8`, `Int16`, `Int32`, `Int64` (`bits` is the width). -/
  | sint (bits : Nat)
  | arr (t : SType)
  | list (t : SType)
  /-- A value of a structure-like type (one constructor, no index, not recursive) of two or
      more fields, all of sample types other than `Float` (`Int × Int`, a `Box2 Int`): a
      JavaScript record `{ _1: …, _2: … }`.  `ind` is the type, `ctor` its constructor applied
      to the parameters. -/
  | record (ind : Name) (ctor : Expr) (fields : List SType)
  /-- A value of a structure-like type (one constructor, no index, not recursive) of exactly one
      field, of a sample type other than `Float` and a union (`structure NewTypeInt where val : Int`): the
      structure is unboxed, its JavaScript value is the field's.  `ind` is the type, `ctor` its
      constructor applied to the parameters. -/
  | wrap (ind : Name) (ctor : Expr) (field : SType)
  /-- A value of a (recursive) inductive type of two or more constructors, one of them at
      least with fields, each field the type itself (`none`) or of a sample type among `Nat`,
      `Int`, `Bool`, `String`, `Char` (`Expr`, `Tree Nat`): a JavaScript union
      `{ tag: i, _1: …, … }`.  `ctors` are the constructors applied to the parameters.  Only a
      parameter can have this type (a result is not compared). -/
  | tree (ctors : List (Expr × List (Option SType)))
  deriving Inhabited, BEq

mutual

/-- The sample type of the inductive type `e` (of declaration `ind`), when it is a union whose
    fields are itself or leaves (`SType.tree`). -/
partial def treeOf? (e : Expr) (ind : InductiveVal) (lvls : List Level) :
    MetaM (Option SType) := do
  unless ind.ctors.length ≥ 2 && ind.numIndices == 0 && e.getAppNumArgs == ind.numParams do
    return none
  let mut out : Array (Expr × List (Option SType)) := #[]
  for c in ind.ctors do
    let ctor := mkAppN (mkConst c lvls) e.getAppArgs
    let fs? ← forallTelescopeReducing (← inferType ctor) fun xs _ => do
      let mut fs : Array (Option SType) := #[]
      for x in xs do
        let t ← instantiateMVars (← inferType x)
        if t.hasAnyFVar (fun _ => true) then return none
        if t == e then fs := fs.push none
        else
          let some ft ← stypeOf? t | return none
          unless [SType.nat, .int, .bool, .string, .char].contains ft do return none
          fs := fs.push (some ft)
      return some fs.toList
    let some fs := fs? | return none
    out := out.push (ctor, fs)
  unless out.any (!·.2.isEmpty) do return none
  return some (.tree out.toList)

/-- The sample type of a Lean type, if it is one. -/
partial def stypeOf? (e : Expr) : MetaM (Option SType) := do
  let e ← instantiateMVars e
  if e.isConstOf ``Nat then return some .nat
  if e.isConstOf ``Int then return some .int
  if e.isConstOf ``Bool then return some .bool
  if e.isConstOf ``String then return some .string
  if e.isConstOf ``Char then return some .char
  if e.isConstOf ``Float then return some .float
  for (n, b) in [(``UInt8, 8), (``UInt16, 16), (``UInt32, 32), (``UInt64, 64)] do
    if e.isConstOf n then return some (.uint b)
  for (n, b) in [(``Int8, 8), (``Int16, 16), (``Int32, 32), (``Int64, 64)] do
    if e.isConstOf n then return some (.sint b)
  if e.isAppOfArity ``Array 1 then
    match ← stypeOf? e.appArg! with
    | some t@SType.nat | some t@SType.int | some t@SType.bool | some t@SType.string =>
      return some (.arr t)
    | _ => return none
  if e.isAppOfArity ``List 1 then
    match ← stypeOf? e.appArg! with
    | some t@SType.nat | some t@SType.int | some t@SType.bool | some t@SType.string =>
      return some (.list t)
    | _ => return none
  -- a structure-like type of two or more fields of sample types
  let some (c, lvls) := e.getAppFn.const? | return none
  let some (.inductInfo ind) := (← getEnv).find? c | return none
  if let some t ← treeOf? e ind lvls then return some t
  unless ind.ctors.length == 1 && ind.numIndices == 0 && !ind.isRec &&
    e.getAppNumArgs == ind.numParams do return none
  let ctor := mkAppN (mkConst ind.ctors.head! lvls) e.getAppArgs
  let fields? ← forallTelescopeReducing (← inferType ctor) fun xs _ => do
    let mut out : Array SType := #[]
    for x in xs do
      let t ← inferType x
      -- a field that depends on another one (a proof about it, an index) is left out of the
      -- JavaScript value: no sample
      if t.hasAnyFVar (fun _ => true) then return none
      match ← stypeOf? t with
      | some .float | none => return none
      | some ft => out := out.push ft
    return some out.toList
  match fields? with
  | some [f] => if f matches .tree _ then return none else return some (.wrap c ctor f)
  | some fs => if fs.length ≥ 2 then return some (.record c ctor fs) else return none
  | none => return none

end

/-- A JavaScript string literal. -/
def jsStringLit (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    if c == '"' then out := out ++ "\\\""
    else if c == '\\' then out := out ++ "\\\\"
    else if c == '\n' then out := out ++ "\\n"
    else if c.toNat < 32 then out := out ++ s!"\\u{String.ofList ((Nat.toDigits 16 c.toNat).leftpad 4 '0')}"
    else out := out.push c
  return out ++ "\""

/-- An integer literal in the representation the configuration gives the type. -/
def intLit (big : Bool) (i : Int) : String :=
  if big then s!"{i}n" else toString i

/-- A sample: the Lean argument and its JavaScript spelling. -/
structure Sample where
  lean : Expr
  js : String
  deriving Inhabited

/-- The samples of a type (few and small: the functions are called on every combination). -/
partial def samplesOf (cfg : JsConfig) : SType → List Sample
  | .nat => [0, 1, 2, 5, 13].map fun n => ⟨mkNatLit n, intLit (cfg.natRepr == .bigint) n⟩
  | .int => [(-7 : Int), -1, 0, 1, 2, 3, 12].map fun i => ⟨toExpr i, intLit (cfg.intRepr == .bigint) i⟩
  | .bool => [⟨toExpr false, "false"⟩, ⟨toExpr true, "true"⟩]
  -- the fixed-width integers: small ones, and the edges of the range (which overflow at the
  -- first addition) below 64 bits, where they are JavaScript numbers at every preset
  | .uint b =>
    let big := b == 64 && cfg.uint64Repr == .bigint
    let ns : List Nat := [0, 1, 2, 5, 13] ++ (if b < 64 then [2 ^ b - 1] else [])
    ns.map fun n => ⟨uintExpr b n, intLit big n⟩
  | .sint b =>
    let big := b == 64 && cfg.int64Repr == .bigint
    let is : List Int := [-7, -1, 0, 3, 12] ++
      (if b < 64 then [-(2 : Int) ^ (b - 1), 2 ^ (b - 1) - 1] else [])
    is.map fun i => ⟨sintExpr b i, intLit big i⟩
  | .string => ["", "a", "hello world", "héllo, wörld", "abcabc"].map fun s =>
      ⟨toExpr s, jsStringLit s⟩
  | .char => ['a', 'z', ' ', 'é'].map fun c => ⟨toExpr c, jsStringLit (String.singleton c)⟩
  | .float =>
    -- `Float.ofScientific m s e` is `m * 10^-e` (`s = true`) or `m * 10^e`
    let f (m : Nat) (s : Bool) (e : Nat) (js : String) : Sample :=
      ⟨mkApp3 (mkConst ``Float.ofScientific) (mkNatLit m) (toExpr s) (mkNatLit e), js⟩
    [f 0 false 0 "0", f 5 true 1 "0.5", f 1 false 0 "1", f 2 false 0 "2", f 3 false 0 "3",
      f 225 true 2 "2.25", f 3 false 1 "30",
      ⟨mkApp (mkConst ``Float.neg) (mkApp3 (mkConst ``Float.ofScientific) (mkNatLit 15)
        (toExpr true) (mkNatLit 1)), "-1.5"⟩]
  | .arr t => (listSamples cfg t true).map fun l =>
      ⟨mkApp2 (mkConst ``List.toArray [.zero]) (elemTy t) l.lean, l.js⟩
  | .list t => listSamples cfg t (cfg.listRepr == .stdListToJsArray)
  | .record _ ctor fs =>
    -- a few records, the samples of each field taken at shifted positions
    let fss := fs.map (samplesOf cfg)
    (List.range 3).map fun i =>
      let picks : List Sample := fss.zipIdx.map fun (ss, j) => ss[(i + j) % ss.length]!
      ⟨mkAppN ctor (picks.map (·.lean)).toArray,
       "{ " ++ ", ".intercalate (picks.zipIdx.map fun (x, j) => s!"_{j + 1}: {x.js}") ++ " }"⟩
  | .wrap _ ctor t => (samplesOf cfg t).map fun x => ⟨mkApp ctor x.lean, x.js⟩
  | .tree ctors =>
    -- the values of depth at most 2 (the leaves taken among their first two samples), the
    -- smallest first, at most `treeCap` of them
    let grow (vs : List Sample) : List Sample :=
      vs ++ (treeLayer cfg ctors vs).filter fun v => !vs.any (·.js == v.js)
    (grow (grow (grow []))).take treeCap
where
  /-- The values built by one constructor on top of the values `sub` (the leaves among their
      first two samples), at every constructor. -/
  treeLayer (cfg : JsConfig) (ctors : List (Expr × List (Option SType))) (sub : List Sample) :
      List Sample :=
    ctors.zipIdx.flatMap fun ((ctor, fs), i) =>
      let choices : List (List Sample) := fs.map fun
        | none => sub
        | some t => (samplesOf cfg t).take 2
      let picks : List (List Sample) := choices.foldr
        (fun cs acc => cs.flatMap fun c => acc.map (c :: ·)) [[]]
      picks.map fun xs =>
        ⟨mkAppN ctor (xs.map (·.lean)).toArray,
         if xs.isEmpty then
           (if cfg.nullaryRepr == .smallInt then toString i else s!"\{ tag: {i} }")
         else s!"\{ tag: {i}, " ++
           ", ".intercalate (xs.zipIdx.map fun (x, j) => s!"_{j + 1}: {x.js}") ++ " }"⟩
  /-- The most samples of a `SType.tree`. -/
  treeCap : Nat := 48
  /-- The samples of `List t`, spelled as a JavaScript array (`array`) or as the cons cells of
      `ListRepr.taggedUnion` (`{ tag: 1, _1: x, _2: … { tag: 0 } }`). -/
  listSamples (cfg : JsConfig) (t : SType) (array : Bool) : List Sample :=
    let elems := samplesOf cfg t
    let mk (xs : List Sample) : Sample :=
      ⟨xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [.zero]) (elemTy t) x.lean acc)
          (mkApp (mkConst ``List.nil [.zero]) (elemTy t)),
       if array then "[" ++ ", ".intercalate (xs.map (·.js)) ++ "]"
       else xs.foldr (fun x acc => s!"\{ tag: 1, _1: {x.js}, _2: {acc} }") "{ tag: 0 }"⟩
    [mk [], mk (elems.take 1), mk (elems.take 3), mk (elems.reverse.take 4)]
  /-- The Lean value `n` of `UInt{b}`. -/
  uintExpr (b n : Nat) : Expr :=
    match b with
    | 8 => toExpr n.toUInt8 | 16 => toExpr n.toUInt16 | 32 => toExpr n.toUInt32
    | _ => toExpr n.toUInt64
  /-- The Lean value `i` of `Int{b}`. -/
  sintExpr (b : Nat) (i : Int) : Expr :=
    match b with
    | 8 => toExpr i.toInt8 | 16 => toExpr i.toInt16 | 32 => toExpr i.toInt32
    | _ => toExpr i.toInt64
  /-- The Lean type of the elements of an array or a list sample. -/
  elemTy : SType → Expr
    | .nat => mkConst ``Nat | .int => mkConst ``Int | .bool => mkConst ``Bool
    | _ => mkConst ``String

/-- All combinations of samples of the parameter types, at most `cap` of them, spread over
    the space (each list is walked with a stride so that not only the first samples of the
    first parameter are used), then ordered from the smallest up (by the sum of the
    positions of the samples in their lists, which list the small samples first). -/
def combos (cfg : JsConfig) (ts : List SType) (cap : Nat := 24) : List (List Sample) :=
  let all : List (Nat × List Sample) := ts.foldr (fun t acc =>
    ((samplesOf cfg t).zipIdx).flatMap fun (s, i) => acc.map fun (k, ss) => (i + k, s :: ss))
    [(0, [])]
  let picked := if all.length ≤ cap then all
    else
      let stride := all.length / cap + 1
      (List.range all.length).filterMap fun i =>
        if i % stride == 0 then all[i]? else none
  (picked.mergeSort fun a b => a.1 ≤ b.1).map (·.2)

/-- A check: the JavaScript call and the answer Lean gives, printed. -/
structure CheckCase where
  call : String
  expected : String
  isFloat : Bool
  /-- The JavaScript expression computing the value, when it is not `M.call`. -/
  expr : Option String := none

/-- Run `f ()` on a thread of its own, waiting at most `ms` milliseconds for it: `none` when
    it has not finished by then (it may not terminate, or its answer may be astronomically
    large, as for `ack 13 13`).  A call that timed out keeps running in the background: the
    tool ends with `IO.Process.exit`, which stops it. -/
def evalWithTimeout (f : Unit → String) (ms : UInt32) : IO (Option String) := do
  let go ← IO.mkRef ()
  let work ← IO.asTask (prio := .dedicated) (do
    let u ← go.get
    return some (f u))
  let timer ← IO.asTask (do IO.sleep ms; return (none : Option String))
  let r ← IO.waitAny [work, timer]
  match r with
  | .ok v => return v
  | .error _ => return none

/-! ## Panics

Lean's `panic!` prints its message on the standard error of the process (from the runtime, not
through `IO`) and goes on with the default value, while the JavaScript throws the message
(`lean_panic_fn`).  So when the translation of a file calls `lean_panic_fn`, the tool computes
the expected answers a second time in a child process (`--probe-panics`), which marks each
evaluation on its standard error (`probeMark`); the lines `PANIC at …` printed between the
marks of a call are the message of a panic of Lean in it (`panicsOf`), and the call is then
expected to throw that message (`threw: PANIC at …`). -/

/-- The mark printed on the standard error before the evaluation of a call (followed by the
    call). -/
def probeCase : String := "@@leanscript-probe-case@@ "

/-- The mark printed on the standard error after the evaluation of a call. -/
def probeEnd : String := "@@leanscript-probe-end@@"

/-- The mark printed on the standard error before the checks of a preset (followed by it). -/
def probePreset : String := "@@leanscript-probe-preset@@ "

/-- Print a mark of `--probe-panics` on its own line of the standard error. -/
def probeMark (m : String) : IO Unit := do
  let e ← IO.getStderr
  e.putStr s!"\n{m}\n"
  e.flush

/-- The panics of Lean, read off the standard error of a child process run with
    `--probe-panics`: for each preset, each call during which Lean printed a line `PANIC at …`,
    and that line (the first one). -/
def panicsOf (stderr : String) : Std.HashMap String (Std.HashMap String String) := Id.run do
  let mut out : Std.HashMap String (Std.HashMap String String) := {}
  let mut preset := ""
  let mut call : Option String := none
  let mut msg : Option String := none
  for l in stderr.splitOn "\n" do
    if l.startsWith probePreset then
      preset := (l.drop probePreset.length).toString
    else if l.startsWith probeCase then
      call := some (l.drop probeCase.length).toString
      msg := none
    else if l == probeEnd then
      if let (some c, some m) := (call, msg) then
        out := out.insert preset ((out.getD preset {}).insert c m)
      call := none
    else if call.isSome && msg.isNone && l.startsWith "PANIC at " then
      msg := some l
  return out

/-- The JavaScript spelling of a call of a function exported with `arity` parameters: the
    first `arity` arguments in one call, the others one at a time (the exported function
    returns a curried function then).  A definition without parameters is exported as a
    constant (`JsFun.isConst`): it is read, not called. -/
def jsCall (jsName : String) (arity : Nat) (args : List String) : String :=
  if arity == 0 && args.isEmpty then jsName else
  let first := args.take arity
  let rest := args.drop arity
  s!"{jsName}({", ".intercalate first})" ++ String.join (rest.map fun a => s!"({a})")

/-- The Lean expression printing the value `e` of the sample type `t` as the check module
    prints the JavaScript value (`show`): `toString`, of the bits of a `Float`, of the array
    of a `List`, and `{a, b}` for a record. -/
partial def showExpr (t : SType) (e : Expr) : MetaM Expr := do
  match t with
  | .float => mkAppM ``toString #[mkApp (mkConst ``Float.toBits) e]
  | .list _ => mkAppM ``toString #[← mkAppM ``List.toArray #[e]]
  | .record ind _ fs =>
    let parts ← fs.zipIdx.mapM fun (ft, i) => showExpr ft (.proj ind i e)
    let app (a b : Expr) : MetaM Expr := mkAppM ``HAppend.hAppend #[a, b]
    let body ← match parts with
      | [] => pure (toExpr "")
      | q :: qs => qs.foldlM (fun acc q => do app (← app acc (toExpr ", ")) q) q
    app (← app (toExpr "{") body) (toExpr "}")
  | .wrap ind _ t => showExpr t (.proj ind 0 e)
  | _ => mkAppM ``toString #[e]

/-- The checks of one function: `none` when its type is not one of sample types.  Each
    expected answer is computed by Lean with a time budget of `timeoutMs` milliseconds; the
    samples are tried from the smallest up, and the first call over budget ends the checks of
    the function (a larger sample would not be faster). -/
unsafe def checksOf (cfg : JsConfig) (n : Name) (jsName : String) (arity : Nat)
    (timeoutMs : UInt32 := 2000) (versions : List String := []) (twice : Bool := false)
    (probe : Bool := false) (panics : Std.HashMap String String := {}) :
    MetaM (Option (List CheckCase)) := do
  let ci ← getConstInfo n
  let some (ps, res) ← forallTelescope ci.type (fun xs r => do
      let mut ps : Array SType := #[]
      for x in xs do
        let some t ← stypeOf? (← inferType x) | return none
        ps := ps.push t
      if r.hasAnyFVar (fun _ => true) then return none
      let some rt ← stypeOf? r | return none
      if rt matches .tree _ then return none
      return some (ps.toList, rt))
    | return none
  let mut out : Array CheckCase := #[]
  let cap := if ps.any (· matches .tree _) then 48 else 24
  for args in combos cfg ps cap do
    let app := mkAppN (mkConst n (ci.levelParams.map fun _ => .zero)) (args.map (·.lean)).toArray
    let shown ← showExpr res app
    let thunkTy := mkForall `u .default (mkConst ``Unit) (mkConst ``String)
    let thunk := mkLambda `u .default (mkConst ``Unit) shown
    let f? ← try
        some <$> evalExpr (Unit → String) thunkTy thunk
      catch _ => pure none
    let some f := f? | continue
    let label := jsCall jsName arity (args.map (·.js))
    if probe then probeMark s!"{probeCase}{label}"
    -- a call known to make Lean panic (`panic!`: it prints the message and goes on with the
    -- default) is not evaluated again: the JavaScript throws the same message (`lean_panic_fn`)
    let r ← match panics.get? label with
      | some msg => pure (some s!"threw: {msg}")
      | none => evalWithTimeout f timeoutMs
    if probe then probeMark probeEnd
    match r with
    | some e =>
      -- a 64-bit answer outside `±(2^53 - 1)` where the preset makes the type a number: the
      -- JavaScript throws by design ("integer overflow … use the bigint representation"),
      -- there is no answer to compare
      let num64 := match res with
        | .uint 64 => cfg.uint64Repr == .num
        | .sint 64 => cfg.int64Repr == .num
        | _ => false
      let tooBig : Bool := match e.toInt? with
        | some i => decide (i.natAbs > 2 ^ 53 - 1)
        | none => false
      if num64 && tooBig then continue
      let js := args.map (·.js)
      out := out.push { call := jsCall jsName arity js, expected := e, isFloat := res == .float }
      -- the versions owning some parameters (`LeanScript.Term.Ownership`): the same answer on
      -- arguments nobody else holds (each call builds its own)
      for sfx in versions do
        out := out.push { call := jsCall (jsName ++ sfx) arity js, expected := e,
                          isFloat := res == .float }
      -- the version borrowing its parameters leaves them alone: called twice on the same
      -- arguments, it answers the same
      if twice && !js.isEmpty then
        let xs := (List.range js.length).map fun i => s!"a{i}"
        let call := jsCall jsName arity xs
        out := out.push { call := s!"{jsCall jsName arity js} twice", expected := e,
                          isFloat := res == .float,
                          expr := some s!"(({", ".intercalate xs}) => (M.{call}, M.{call}))\
                            ({", ".intercalate js})" }
    | none => break
  return some out.toList

/-- The JavaScript prelude of a check module: printing values as Lean's `toString` does. -/
def checkPrelude : String := "
function show(v) {
  if (Array.isArray(v) || ArrayBuffer.isView(v)) return \"#[\" + [...v].map(show).join(\", \") + \"]\";
  // a list of cons cells (`ListRepr.taggedUnion`) is shown as its elements
  if (v !== null && typeof v === \"object\" && (v.tag === 0 || v.tag === 1)) {
    const a = [];
    for (; v.tag === 1; v = v._2) a.push(v._1);
    return show(a);
  }
  // a record (a structure-like type) is shown as its fields: `{a, b}`
  if (v !== null && typeof v === \"object\" && !(\"tag\" in v) && \"_1\" in v) {
    const fs = [];
    for (let i = 1; (\"_\" + i) in v; i++) fs.push(show(v[\"_\" + i]));
    return \"{\" + fs.join(\", \") + \"}\";
  }
  return String(v);
}
function floatBits(x) {
  return String(new BigUint64Array(new Float64Array([x]).buffer)[0]);
}
function isNaNBits(s) {
  const b = BigInt(s);
  return ((b >> 52n) & 0x7ffn) === 0x7ffn && (b & 0xfffffffffffffn) !== 0n;
}
let passed = 0, failed = 0;
function check(label, thunk, expected, isFloat) {
  let got;
  try {
    const v = thunk();
    got = isFloat ? floatBits(v) : show(v);
    // NaN payloads differ between platforms: any NaN matches any NaN
    if (isFloat && Number.isNaN(v) && isNaNBits(expected)) got = expected;
  } catch (e) {
    got = \"threw: \" + e.message;
  }
  if (got === expected) passed++;
  else {
    failed++;
    console.log(`FAIL ${label}: expected ${JSON.stringify(expected)}, got ${JSON.stringify(got)}`);
  }
}
"

/-- The check module of a file. -/
def checkModule (jsFile : String) (cases : List CheckCase) : String :=
  s!"// Differential checks of {jsFile} against Lean, generated by leanscript --check\n" ++
  s!"import * as M from \"./{jsFile}\";\n" ++ checkPrelude ++ "\n" ++
  String.join (cases.map fun c =>
    s!"check({jsStringLit c.call}, () => {c.expr.getD s!"M.{c.call}"}, \
      {jsStringLit c.expected}, {c.isFloat});\n") ++
  "\nconsole.log(`" ++ jsFile ++ ": ${passed} passed, ${failed} failed`);\n" ++
  "if (failed > 0) process.exit(1);\n"

end LeanScript.Cli
