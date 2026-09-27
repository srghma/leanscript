import Lean
import MoreJsTy.Config

/-!
# Differential checks of the generated JavaScript against Lean

With `--check`, `leanscript` writes, next to `FILE.js`, a module `FILE.check.mjs` that calls
the exported functions on sample arguments and compares each answer with the one **Lean**
gives for the same call (computed by the tool with `Lean.Meta.evalExpr`, in the environment
of the elaborated file).  `node FILE.check.mjs` prints the checks and exits with a non-zero
status when one fails.

Only functions whose parameters and result are all of a *sample type* are checked: `Nat`,
`Int`, `Bool`, `String`, `Char`, `Float`, and `Array` of `Nat`, `Int`, `Bool` or `String`.
A value is compared through its printed form (`toString` in Lean; the same format computed
in JavaScript), except a `Float`, which is compared bit for bit (`Float.toBits`).
-/

open Lean Meta MoreJs

namespace LeanScript.Cli

/-- The types the checks can produce samples of and compare. -/
inductive SType where
  | nat | int | bool | string | char | float
  | arr (t : SType)
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
def samplesOf (cfg : JsConfig) : SType → List Sample
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
  | .arr t =>
    let elems := samplesOf cfg t
    let mk (xs : List Sample) : Sample :=
      let elemTy : Expr := match t with
        | .nat => mkConst ``Nat | .int => mkConst ``Int | .bool => mkConst ``Bool
        | _ => mkConst ``String
      ⟨mkApp2 (mkConst ``List.toArray [.zero]) elemTy
        (xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [.zero]) elemTy x.lean acc)
          (mkApp (mkConst ``List.nil [.zero]) elemTy)),
       "[" ++ ", ".intercalate (xs.map (·.js)) ++ "]"⟩
    [mk [], mk (elems.take 1), mk (elems.take 3), mk (elems.reverse.take 4)]

/-- All combinations of samples of the parameter types, at most `cap` of them, spread over
    the space (each list is walked with a stride so that not only the first samples of the
    first parameter are used). -/
def combos (cfg : JsConfig) (ts : List SType) (cap : Nat := 24) : List (List Sample) :=
  let all := ts.foldr (fun t acc =>
    (samplesOf cfg t).flatMap fun s => acc.map (s :: ·)) [[]]
  if all.length ≤ cap then all
  else
    let stride := all.length / cap + 1
    (List.range all.length).filterMap fun i =>
      if i % stride == 0 then all[i]? else none

/-- A check: the JavaScript call and the answer Lean gives, printed. -/
structure CheckCase where
  call : String
  expected : String
  isFloat : Bool

/-- The checks of one function: `none` when its type is not one of sample types. -/
unsafe def checksOf (cfg : JsConfig) (n : Name) (jsName : String) : MetaM (Option (List CheckCase)) := do
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
      | _ => mkAppM ``toString #[app]
    let expected ← try
        some <$> evalExpr String (mkConst ``String) shown
      catch _ => pure none
    if let some e := expected then
      out := out.push { call := s!"{jsName}({", ".intercalate (args.map (·.js))})",
                        expected := e, isFloat := res == .float }
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
