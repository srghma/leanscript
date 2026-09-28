import Lean
import JsTerm.Config

/-!
# Differential checks of the generated JavaScript against Lean

With `--check`, `leanscript` writes, next to `FILE.js`, a module `FILE.check.mjs` that calls
the exported functions on sample arguments and compares each answer with the one **Lean**
gives for the same call (computed by the tool with `Lean.Meta.evalExpr`, in the environment
of the elaborated file).  `node FILE.check.mjs` prints the checks and exits with a non-zero
status when one fails.

Only functions whose parameters and result are all of a *sample type* are checked: `Nat`,
`Int`, `Bool`, `String`, `Char`, `Float`, and `Array` and `List` of `Nat`, `Int`, `Bool` or
`String` (a list is a JavaScript array, and is printed as its array, `#[…]`).
A value is compared through its printed form (`toString` in Lean; the same format computed
in JavaScript), except a `Float`, which is compared bit for bit (`Float.toBits`).
-/

open Lean Meta MoreJs

namespace LeanScript.Cli

/-- The types the checks can produce samples of and compare. -/
inductive SType where
  | nat | int | bool | string | char | float
  | arr (t : SType)
  | list (t : SType)
  deriving Inhabited, BEq

/-- The sample type of a Lean type, if it is one. -/
partial def stypeOf? (e : Expr) : MetaM (Option SType) := do
  let e ← instantiateMVars e
  if e.isConstOf ``Nat then return some .nat
  if e.isConstOf ``Int then return some .int
  if e.isConstOf ``Bool then return some .bool
  if e.isConstOf ``String then return some .string
  if e.isConstOf ``Char then return some .char
  if e.isConstOf ``Float then return some .float
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
  return none

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

/-- The samples of a type (few and small: the functions are called on every combination). -/
partial def samplesOf (cfg : JsConfig) : SType → List Sample
  | .nat => [0, 1, 2, 5, 13].map fun n => ⟨mkNatLit n, intLit (cfg.natRepr == .bigint) n⟩
  | .int => [(-7 : Int), -1, 0, 3, 12].map fun i => ⟨toExpr i, intLit (cfg.intRepr == .bigint) i⟩
  | .bool => [⟨toExpr false, "false"⟩, ⟨toExpr true, "true"⟩]
  | .string => ["", "a", "hello world", "héllo, wörld", "abcabc"].map fun s =>
      ⟨toExpr s, jsStringLit s⟩
  | .char => ['a', 'z', ' ', 'é'].map fun c => ⟨toExpr c, jsStringLit (String.singleton c)⟩
  | .float =>
    -- `Float.ofScientific m s e` is `m * 10^-e` (`s = true`) or `m * 10^e`
    let f (m : Nat) (s : Bool) (e : Nat) (js : String) : Sample :=
      ⟨mkApp3 (mkConst ``Float.ofScientific) (mkNatLit m) (toExpr s) (mkNatLit e), js⟩
    [f 0 false 0 "0", f 5 true 1 "0.5", f 225 true 2 "2.25", f 3 false 1 "30",
      ⟨mkApp (mkConst ``Float.neg) (mkApp3 (mkConst ``Float.ofScientific) (mkNatLit 15)
        (toExpr true) (mkNatLit 1)), "-1.5"⟩]
  | .arr t => (samplesOf cfg (.list t)).map fun l =>
      ⟨mkApp2 (mkConst ``List.toArray [.zero]) (elemTy t) l.lean, l.js⟩
  | .list t =>
    let elems := samplesOf cfg t
    let mk (xs : List Sample) : Sample :=
      ⟨xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [.zero]) (elemTy t) x.lean acc)
          (mkApp (mkConst ``List.nil [.zero]) (elemTy t)),
       "[" ++ ", ".intercalate (xs.map (·.js)) ++ "]"⟩
    [mk [], mk (elems.take 1), mk (elems.take 3), mk (elems.reverse.take 4)]
where
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

/-- The JavaScript spelling of a call of a function exported with `arity` parameters: the
    first `arity` arguments in one call, the others one at a time (the exported function
    returns a curried function then). -/
def jsCall (jsName : String) (arity : Nat) (args : List String) : String :=
  let first := args.take arity
  let rest := args.drop arity
  s!"{jsName}({", ".intercalate first})" ++ String.join (rest.map fun a => s!"({a})")

/-- The checks of one function: `none` when its type is not one of sample types.  Each
    expected answer is computed by Lean with a time budget of `timeoutMs` milliseconds; the
    samples are tried from the smallest up, and the first call over budget ends the checks of
    the function (a larger sample would not be faster). -/
unsafe def checksOf (cfg : JsConfig) (n : Name) (jsName : String) (arity : Nat)
    (timeoutMs : UInt32 := 2000) : MetaM (Option (List CheckCase)) := do
  let ci ← getConstInfo n
  let some (ps, res) ← forallTelescope ci.type (fun xs r => do
      let mut ps : Array SType := #[]
      for x in xs do
        let some t ← stypeOf? (← inferType x) | return none
        ps := ps.push t
      if r.hasAnyFVar (fun _ => true) then return none
      let some rt ← stypeOf? r | return none
      return some (ps.toList, rt))
    | return none
  let mut out : Array CheckCase := #[]
  for args in combos cfg ps do
    let app := mkAppN (mkConst n (ci.levelParams.map fun _ => .zero)) (args.map (·.lean)).toArray
    let shown ← match res with
      | .float => mkAppM ``toString #[mkApp (mkConst ``Float.toBits) app]
      | .list _ => do mkAppM ``toString #[← mkAppM ``List.toArray #[app]]
      | _ => mkAppM ``toString #[app]
    let thunkTy := mkForall `u .default (mkConst ``Unit) (mkConst ``String)
    let thunk := mkLambda `u .default (mkConst ``Unit) shown
    let f? ← try
        some <$> evalExpr (Unit → String) thunkTy thunk
      catch _ => pure none
    let some f := f? | continue
    match ← evalWithTimeout f timeoutMs with
    | some e =>
      out := out.push { call := jsCall jsName arity (args.map (·.js)),
                        expected := e, isFloat := res == .float }
    | none => break
  return some out.toList

/-- The JavaScript prelude of a check module: printing values as Lean's `toString` does. -/
def checkPrelude : String := "
function show(v) {
  if (Array.isArray(v) || ArrayBuffer.isView(v)) return \"#[\" + [...v].map(show).join(\", \") + \"]\";
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
    s!"check({jsStringLit c.call}, () => M.{c.call}, {jsStringLit c.expected}, {c.isFloat});\n") ++
  "\nconsole.log(`" ++ jsFile ++ ": ${passed} passed, ${failed} failed`);\n" ++
  "if (failed > 0) process.exit(1);\n"

end LeanScript.Cli
