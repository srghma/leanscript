module

import Spec.RunSpec
import TermTests.ToTerm.TcoTest
import TermTests.ToTerm.WhileTest
import TermTests.Datatypes.QuotientTest
import TermTests.Datatypes.RoseVariantsTest
import TermTests.Optimize.WFTermTest
import LeanScript.Term.Optimize.Basic
import JsTerm.Lower.FromTerm
import JsTerm.Lower.Module
import JsTerm.Syntax.Pretty

/-!
# The expensive checks of `TyTests`/`TermTests`, run compiled

Each check here was an `example : t.run args = v := by kernel_rfl` (or `rfl`) in a test file:
the kernel evaluates `Term.eval` by unfolding the structural recursors of the term families
(`Term.brecOn`, with its `below` tuples) and every `natIter` step, which took from half a
second to many seconds per check (`WhileTest.bits 1000`: ~18 s).  Here the same translated
terms are evaluated by the compiled `Term.eval` (a few microseconds each), and the answer is
compared with the expected value and, when there is one, with the compiled Lean function the
term was translated from.

The file where each check comes from has a comment `-- (moved to Tests/Main.lean …)` at its old
place.  Run with `lake test` (or `lake exe tests`; `--help` lists the options of `Spec`).
-/

open Spec Spec.Assert LeanScript

/-- `name`: the translation computes `expected`. -/
def checkNat (name : String) (expected actual : Nat) : SpecM Unit Unit :=
  it name (assertEq name expected actual)

/-- `name`: the translation computes `expected`, and so does the Lean function. -/
def checkNat₂ (name : String) (expected lean actual : Nat) : SpecM Unit Unit :=
  it name do
    assertEq s!"{name} (Lean function)" expected lean
    assertEq s!"{name} (translation)" expected actual

section Tco
open Tco

/-- `Tests/TermTests/ToTerm/TcoTest.lean`: higher-order and tail-recursive functions. -/
def tcoSpec : Spec := describe "TcoTest" do
  checkNat₂ "ackInner (· + 2) 3" 9 (ackInner (fun x => x + 2) 3)
    ((ackInnerT (Δ := DSig.nil)).run (fun x => x + 2 : Nat → Nat) (3 : Nat))
  checkNat₂ "ack2 2 3" 9 (ack2 2 3) ((ack2T (Δ := DSig.nil)).run (2 : Nat) (3 : Nat))
  checkNat₂ "hyperLoop (2 * ·) 5 1" 32 (hyperLoop (fun x => 2 * x) 5 1)
    ((hyperLoopT (Δ := DSig.nil)).run (fun x => 2 * x : Nat → Nat) (5 : Nat) (1 : Nat))
  checkNat₂ "hyperTCO 1 2 3" 5 (hyperTCO 1 2 3)
    ((hyperTCOT (Δ := DSig.nil)).run (1 : Nat) (2 : Nat) (3 : Nat))
  checkNat₂ "hyperWhile 1 2 3" 5 (hyperWhile 1 2 3)
    ((hyperWhileT (Δ := DSig.nil)).run (1 : Nat) (2 : Nat) (3 : Nat))
  checkNat₂ "hyperTCO 3 2 3" 8 (hyperTCO 3 2 3)
    ((hyperTCOT (Δ := DSig.nil)).run (3 : Nat) (2 : Nat) (3 : Nat))
  checkNat₂ "hyperWhile 3 2 3" 8 (hyperWhile 3 2 3)
    ((hyperWhileT (Δ := DSig.nil)).run (3 : Nat) (2 : Nat) (3 : Nat))
  checkNat₂ "iter (· + 3) 4 1" 13 (iter (fun x => x + 3) 4 1)
    ((iterT (Δ := DSig.nil)).run (fun x => x + 3 : Nat → Nat) (4 : Nat) (1 : Nat))
  checkNat₂ "stepSum 2 30" 26 (stepSum 2 30) ((stepSumT (Δ := DSig.nil)).run (2 : Nat) (30 : Nat))
  checkNat₂ "stepSum 5 12" 24 (stepSum 5 12) ((stepSumT (Δ := DSig.nil)).run (5 : Nat) (12 : Nat))
  checkNat₂ "stepSum 7 3" 0 (stepSum 7 3) ((stepSumT (Δ := DSig.nil)).run (7 : Nat) (3 : Nat))
  -- a larger input than the kernel could take
  checkNat₂ "hyperTCO 3 2 10" (hyperTCO 3 2 10) (hyperTCO 3 2 10)
    ((hyperTCOT (Δ := DSig.nil)).run (3 : Nat) (2 : Nat) (10 : Nat))

end Tco

section While
open WhileTest

/-- `Tests/TermTests/ToTerm/WhileTest.lean`: `while` loops with a bound. -/
def whileSpec : Spec := describe "WhileTest" do
  checkNat₂ "sumDown 10" 55 (sumDown 10) ((sumDownT (Δ := DSig.nil)).run (10 : Nat))
  checkNat₂ "bits 1000" 10 (bits 1000) ((bitsT (Δ := DSig.nil)).run (1000 : Nat))
  checkNat₂ "pow2 10" 1024 (pow2 10) ((pow2T (Δ := DSig.nil)).run (10 : Nat))
  checkNat₂ "countBy3 10" 14 (countBy3 10) ((countBy3T (Δ := DSig.nil)).run (10 : Nat))
  checkNat₂ "isqrtUp 50" 8 (isqrtUp 50) ((isqrtUpT (Δ := DSig.nil)).run (50 : Nat))
  checkNat₂ "firstMultiple 100 7" 98 (firstMultiple 100 7)
    ((firstMultipleT (Δ := DSig.nil)).run (100 : Nat) (7 : Nat))

end While

section Quotient
open QuotientTest

/-- `Tests/TermTests/Datatypes/QuotientTest.lean`: quotients are their representatives. -/
def quotientSpec : Spec := describe "QuotientTest" do
  -- the fold is `Comp.array_foldl` over the array of the representatives
  checkNat "S.odds (3, #[1, 2, 5])" 3
    ((sOddsT (Δ := DSig.nil)).run ((3 : Nat), (#[1, 2, 5] : Array Nat)))

end Quotient

section Rose
open RoseVariantsTest

/-- `Tests/TermTests/Datatypes/RoseVariantsTest.lean`: `RoseF`, children as a function on `Fin n`. -/
def roseSpec : Spec := describe "RoseVariantsTest" do
  checkNat₂ "roseFv.size" 9 roseFv.size (roseFSizeT.run roseFT.run)
  checkNat₂ "roseFv.depth" 2 roseFv.depth (roseFDepthT.run roseFT.run)
  checkNat₂ "roseFv.mirror.size" 9 roseFv.mirror.size (roseFSizeT.run (roseFMirrorT.run roseFT.run))
  checkNat₂ "(RoseF.fan 5).size" 6 (RoseF.fan 5).size (roseFSizeT.run (roseFFanT.run (5 : Nat)))

end Rose

/-- The optimiser (`Term.optimize`, run three times) on the same programs: the optimised
    translations compute the same answers (`Term.optimizeN_run` proves it for all inputs; here
    it is checked on values, compiled). -/
def optimizeSpec : Spec := describe "Term.optimize" do
  checkNat "ack2 2 3" 9 (((Tco.ack2T (Δ := DSig.nil)).optimizeN 3).run (2 : Nat) (3 : Nat))
  checkNat "hyperTCO 3 2 3" 8
    (((Tco.hyperTCOT (Δ := DSig.nil)).optimizeN 3).run (3 : Nat) (2 : Nat) (3 : Nat))
  checkNat "hyperWhile 3 2 3" 8
    (((Tco.hyperWhileT (Δ := DSig.nil)).optimizeN 3).run (3 : Nat) (2 : Nat) (3 : Nat))
  checkNat "stepSum 2 30" 26 (((Tco.stepSumT (Δ := DSig.nil)).optimizeN 3).run (2 : Nat) (30 : Nat))
  checkNat "bits 1000" 10 (((WhileTest.bitsT (Δ := DSig.nil)).optimizeN 3).run (1000 : Nat))
  checkNat "firstMultiple 100 7" 98
    (((WhileTest.firstMultipleT (Δ := DSig.nil)).optimizeN 3).run (100 : Nat) (7 : Nat))
  checkNat "S.odds (3, #[1, 2, 5])" 3
    (((QuotientTest.sOddsT (Δ := DSig.nil)).optimizeN 3).run ((3 : Nat), (#[1, 2, 5] : Array Nat)))
  checkNat "roseFv.size" 9
    ((RoseVariantsTest.roseFSizeT.optimizeN 3).run (RoseVariantsTest.roseFT.optimizeN 3).run)

section MoreJsTests
open MoreJs

/-- `uint53` numbers and generic arrays of them, for the hand-written blocks below. -/
abbrev tN : JsTy := .terminal .uint53
abbrev tA : JsTy := .array tN

/-- The signature of the hand-written terms below: no declared datatype. -/
abbrev S : JsSig := {}

/-- The literal `1`. -/
def one {S : JsSig} {C M : List JsTy} : JsExpr S C M tN := .lit (.uint53 1 (by decide))

/-- A signature of one declared datatype, `D0 := nil | cons (h : uint53) (t : D0)` (a user's
    list of numbers): its body is the anonymous union of arities `[0, 2]` whose recursive
    field is `obj (decl 0) []`. -/
def myListSig : JsSig := { decls := #[.obj (.union [0, 2]) [tN, .obj (.decl 0) []]] }

/-- `(x) => fold(cons(1, fold(nil)))`, over `myListSig`: the casts print as nothing. -/
def myListFun : JsFun where
  name := "f"
  leanName := "f"
  sig := myListSig
  params := [("x", tN)]
  ret := .obj (.decl 0) []
  body := .ret (.fold 0 (.union_mk (id := .union [0, 2]) (.succ .zero)
    (.cons (.cvar .zero) (.cons (.fold 0 (.union_mk (id := .union [0, 2]) .zero .nil)) .nil))))

/-- The conversion to the JavaScript grammar (`MoreJs.termToJs`) at both presets: the types
    the configuration chooses, the typed operations of the externs, and the shape of the functions it produces.  (The generated JavaScript
    itself is run against Lean by `scripts/leanscript-snapshots.sh`.) -/
def moreJsSpec : Spec := describe "JsTerm" do
  let faithful : JsConfig := {}
  let pbo := JsConfig.presetPBO
  it "Nat is a BigInt (faithful) or a checked UInt53 (pbo)" do
    assertEq "faithful" "nat(bigint)" (lowerScalarPrim faithful .nat).pretty
    assertEq "pbo" "uint53(number)" (lowerScalarPrim pbo .nat).pretty
    assertEq "Float.Model" "float" (lowerScalarPrim faithful .floatModel).pretty
    assertEq "Float32.Model" "float32" (lowerScalarPrim pbo .float32Model).pretty
  it "records and unions are objects" do
    let r : JsExpr S [] [] (.obj (.record 2) [tN, .terminal .bool]) :=
      .record_mk (.cons one (.cons (.lit (.bool true)) .nil))
    assertEq "record" "{ _1: 1, _2: true }" (r.pretty "")
    let u0 : JsExpr S [] [] (.obj (.union [0, 1]) [tN]) := .union_mk .zero .nil
    let u1 : JsExpr S [] [] (.obj (.union [0, 1]) [tN]) := .union_mk (.succ .zero) (.cons one .nil)
    assertEq "nullary constructor" "{ tag: 0 }" (u0.pretty "")
    assertEq "constructor" "{ tag: 1, _1: 1 }" (u1.pretty "")
    assertEq "record type" "{ _1: nat(bigint), _2: boolean }"
      (JsTy.record [.terminal .bigint_nat, .terminal .bool]).pretty
    assertEq "typed array type" "Uint8Array<uint8>" (JsTy.typedArray .uint8).pretty
    assertEq "BitVec 12 in a Uint16Array" "Uint16Array"
      (JsTypedElem.bitvec 12 (by decide) (by decide)).kind.ctorName
  it "object types are nominal: an identity and arguments" do
    -- `Option String` and `Option Nat` share the anonymous declaration `union [0, 1]`
    let optS : LeanScript.Ty [] := .union (.two .nullary (.fields (.one .string)))
    let optN : LeanScript.Ty [] := .union (.two .nullary (.fields (.one .nat)))
    assertEq "Option String" (repr (JsObjId.union [0, 1])).pretty
      (match lowerTy pbo optS with | .obj id _ => (repr id).pretty | _ => "?")
    assertEq "Option Nat" (repr (JsObjId.union [0, 1])).pretty
      (match lowerTy pbo optN with | .obj id _ => (repr id).pretty | _ => "?")
    assertEq "constructors of Option String" "[[], [string]]"
      (toString ((S.ctorsOf (.union [0, 1]) [.terminal .string]).map fun (cs : List JsTy) => cs.map JsTy.pretty))
    -- the prelude's `List α` is one declaration at every element type
    assertEq "cons cells" "[[], [uint53(number), ConsList<uint53(number)>]]"
      (toString ((S.ctorsOf .consList [tN]).map fun (cs : List JsTy) => cs.map JsTy.pretty))
    -- a declared datatype is read from the signature, and one layer in/out prints as nothing
    assertEq "a declaration's constructors" "[[], [uint53(number), D0]]"
      (toString ((myListSig.ctorsOf (.decl 0) []).map fun (cs : List JsTy) => cs.map JsTy.pretty))
    assertEq "the module of the function imports nothing" ([] : List String)
      (mkModule pbo [myListFun]).imports
    assertEq "the dump shows the casts" "fold<D0>({ tag: 1, _1: c0, _2: fold<D0>({ tag: 0 }) })"
      (match myListFun.body with | .ret e => e.pretty "" | _ => "?")
  it "an extern is an operation named after its types" do
    let big : JsTy := .terminal .bigint_nat
    let args {σ : JsTy} : JsArgs S [σ, σ] [] [σ, σ] := .cons (.cvar (.succ .zero)) (.cons (.cvar .zero) .nil)
    let shown {C M : List JsTy} {τ : JsTy} (e : Except String (JsExpr S C M τ)) : String :=
      match e with
      | .ok e => e.pretty ""
      | .error msg => s!"error: {msg}"
    assertEq "Nat.div (bigint)" "bigint_nat__lean_nat_div(c1, c0)"
      (shown (lowerExtern "lean_nat_div" args : Except String (JsExpr S [big, big] [] big)))
    assertEq "Nat.div (uint53)" "uint53__lean_nat_div(c1, c0)"
      (shown (lowerExtern "lean_nat_div" args : Except String (JsExpr S [tN, tN] [] tN)))
    assertEq "Nat.land (bigint): inlined" "inline:bigint_nat__lean_nat_land(c1, c0)"
      (shown (lowerExtern "lean_nat_land" args : Except String (JsExpr S [big, big] [] big)))
    assertEq "Nat.land (uint53): the runtime" "uint53__lean_nat_land(c1, c0)"
      (shown (lowerExtern "lean_nat_land" args : Except String (JsExpr S [tN, tN] [] tN)))
    -- `Array.set` (`lean_array_fset`, the bound proved) has its own operation, which does not
    -- check the bound
    let fsetArgs : JsArgs S [tN, tN, tA] [] [tA, tN, tN] :=
      .cons (.cvar (.succ (.succ .zero))) (.cons (.cvar (.succ .zero)) (.cons (.cvar .zero) .nil))
    assertEq "Array.set" "uint53__lean_array_fset_immutable(c2, c1, c0)"
      (shown (lowerExtern "lean_array_fset" fsetArgs : Except String (JsExpr S [tN, tN, tA] [] tA)))
    assertEq "no operation" true
      ((shown (lowerExtern "lean_no_such_extern" args : Except String (JsExpr S [tN, tN] [] tN))).startsWith
        "error: the extern lean_no_such_extern has no operation")
  it "operations carry their effects" do
    -- a `uint53` addition throws past `2^53`, a `BigInt` one never throws; only the `_mutable`
    -- updates are effectful
    let effects {σs : List JsTy} {τ : JsTy} (name : String) : String :=
      match JsOp.lookup name σs τ with
      | some ⟨e, t, _⟩ => s!"{repr e} {repr t}"
      | none => "none"
    assertEq "uint53 add" "MoreJs.Effectfulness.pure MoreJs.MayThrow.mayThrow"
      (effects (σs := [tN, tN]) (τ := tN) "lean_nat_add")
    assertEq "bigint add" "MoreJs.Effectfulness.pure MoreJs.MayThrow.doesntThrow"
      (effects (σs := [.terminal .bigint_nat, .terminal .bigint_nat]) (τ := .terminal .bigint_nat)
        "lean_nat_add")
    let m : JsOpImported .effectful .doesntThrow [tA, tN] tA := .array__lean_array_push_mutable tN
    assertEq "push, mutable" "array__lean_array_push_mutable" m.runtimeName
    assertEq "names of the runtime" "string__lean_string_utf8_get_opt__String_Pos_Raw_get$3F"
      (jsSafeName "string__lean_string_utf8_get_opt__String_Pos_Raw_get?")
  it "number literals are the shortest decimal that reads back" do
    assertEq "0.1" "0.1" (numberSource 0.1)
    assertEq "-2.5" "-2.5" (numberSource (-2.5))
    assertEq "subnormal" "5e-324" (numberSource 5e-324)
    assertEq "2^53" "9007199254740992" (numberSource 9007199254740992.0)
    assertEq "2^53 + 2" "9007199254740994" (numberSource 9007199254740994.0)
    assertEq "1e21" "1e+21" (numberSource 1e21)
    assertEq "NaN" "NaN" (numberSource (0.0 / 0.0))
    assertEq "Infinity" "Infinity" (numberSource (1.0 / 0.0))
    assertEq "-Infinity" "-Infinity" (numberSource (-1.0 / 0.0))
    assertEq "-0" "-0" (numberSource (-0.0))
    assertEq "0" "0" (numberSource 0.0)
    assertEq "1.5e-7" "1.5e-7" (numberSource 1.5e-7)
    assertEq "0.000001" "0.000001" (numberSource 0.000001)
    assertEq "123.456" "123.456" (numberSource 123.456)
    assertEq "1.7976931348623157e+308" "1.7976931348623157e+308" (numberSource 1.7976931348623157e308)
    -- `String(Math.fround(0.1))` in JavaScript
    assertEq "Float32 0.1" "0.10000000149011612" (float32Source 0.1)
  it "a literal too big for a number is an error of the conversion" do
    match primLit pbo .nat (2 ^ 60) with
    | .error e => assertEq "too big" true (isLiteralTooBig e)
    | .ok _ => assertEq "too big" "an error" "a literal"
    match primLit faithful .nat (2 ^ 60) with
    | .ok ⟨t, l⟩ => assertEq "a BigInt" "1152921504606846976n" (l.shape.pretty ++ "" ++
        (if t == JsTerminalTy.bigint_nat then "" else "?"))
    | .error e => assertEq "a BigInt" "a literal" e
  it "every array update has an immutable and a mutable version" do
    -- by name: each `…_mutable` operation has its `…_immutable` one, and each `…_immutable` one
    -- has its `…_mutable` one, except `push` / `pop` on a typed array (which cannot grow or
    -- shrink)
    let names := JsOpImported.names.toList
    let imm := names.filter fun (n : String) => n.endsWith "_immutable"
    let mut' := names.filter fun (n : String) => n.endsWith "_mutable"
    let base (suffix n : String) : String := (n.dropEnd suffix.length).toString
    assertEq "the immutable updates"
      ["array__lean_array_pop_immutable", "array__lean_array_push_immutable",
       "bigint_nat__lean_array_fset_immutable", "bigint_nat__lean_array_fswap_immutable",
       "bigint_nat__lean_array_set_immutable", "bigint_nat__lean_array_swap_immutable",
       "typedArray__lean_array_pop_immutable", "typedArray__lean_array_push_immutable",
       "uint53__lean_array_fset_immutable", "uint53__lean_array_fswap_immutable",
       "uint53__lean_array_set_immutable", "uint53__lean_array_swap_immutable"]
      (imm.toArray.qsort (· < ·)).toList
    assertEq "a mutable update without its immutable one" ([] : List String)
      (mut'.filter fun n => !imm.contains (base "_mutable" n ++ "_immutable"))
    assertEq "an immutable update without its mutable one"
      ["typedArray__lean_array_push_immutable", "typedArray__lean_array_pop_immutable"]
      (imm.filter fun n => !mut'.contains (base "_immutable" n ++ "_mutable"))
    -- `toMutable?` pairs them, and only the mutable one is effectful
    let pairName {e : Effectfulness} {t : MayThrow} {σs : List JsTy} {τ : JsTy}
        (op : JsOpImported e t σs τ) : String :=
      match op.toMutable? with
      | some ⟨_, m⟩ => s!"{op.name} {repr e} -> {m.name}"
      | none => s!"{op.name} {repr e} -> none"
    assertEq "push" "array__lean_array_push_immutable MoreJs.Effectfulness.pure -> array__lean_array_push_mutable"
      (pairName (.array__lean_array_push_immutable tN))
    assertEq "typed push" "typedArray__lean_array_push_immutable MoreJs.Effectfulness.pure -> none"
      (pairName (.typedArray__lean_array_push_immutable .uint8))
    assertEq "fset" "uint53__lean_array_fset_immutable MoreJs.Effectfulness.pure -> uint53__lean_array_fset_mutable"
      (pairName (.uint53__lean_array_fset_immutable (.generic tN)))
    assertEq "fswap, typed" "bigint_nat__lean_array_fswap_immutable MoreJs.Effectfulness.pure -> bigint_nat__lean_array_fswap_mutable"
      (pairName (.bigint_nat__lean_array_fswap_immutable (.typed .uint8)))
    assertEq "a mutable one is effectful" "uint53__lean_array_set_mutable MoreJs.Effectfulness.effectful -> none"
      (pairName (.uint53__lean_array_set_mutable (.generic tN)))
  it "the immutable array updates of runtime.js copy, the mutable ones update in place (needs node)" do
    -- each case: an update, its arguments after the array, and the array it is applied to
    let cases : List (String × String × String) := [
      ("array__lean_array_push", "5", "[1, 2, 3]"),
      ("array__lean_array_pop", "", "[1, 2, 3]"),
      ("bigint_nat__lean_array_set", "1n, 9", "[1, 2, 3]"),
      ("bigint_nat__lean_array_set", "7n, 9", "[1, 2, 3]"),
      ("uint53__lean_array_set", "2, 9", "new Uint8Array([1, 2, 3])"),
      ("bigint_nat__lean_array_swap", "0n, 2n", "[1, 2, 3]"),
      ("uint53__lean_array_swap", "0, 5", "[1, 2, 3]"),
      ("bigint_nat__lean_array_fset", "0n, 9", "new Float64Array([1, 2, 3])"),
      ("uint53__lean_array_fset", "2, 9", "[1, 2, 3]"),
      ("bigint_nat__lean_array_fswap", "0n, 1n", "[1, 2, 3]"),
      ("uint53__lean_array_fswap", "1, 2", "new Int32Array([1, 2, 3])")]
    let cwd ← IO.currentDir
    let names := cases.foldl (fun (acc : List String) (c : String × String × String) =>
      acc ++ [c.1 ++ "_immutable", c.1 ++ "_mutable"]) []
    let names := names.foldl (fun (acc : List String) n => if acc.contains n then acc else acc ++ [n]) []
    -- prints, per case: whether the immutable one left its argument alone, whether it returned
    -- a new array (or its argument, unchanged, out of bounds), whether the mutable one returned
    -- its argument, and whether the two agree
    let check (c : String × String × String) : String :=
      let (f, args, arr) := c
      let args := if args.isEmpty then "" else ", " ++ args
      s!"\{ const a = {arr}; const before = Array.from(a).join(); " ++
      s!"const r = {f}_immutable(a{args}); " ++
      s!"const b = {arr}; const m = {f}_mutable(b{args}); " ++
      "console.log([Array.from(a).join() === before, r !== a || Array.from(r).join() === before, m === b, " ++
      "Array.from(r).join() === Array.from(m).join(), r.constructor === m.constructor].join()); }
"
    let script := s!"import \{ {", ".intercalate names} } from {(s!"file://{cwd}/runtime.js").quote};\n" ++
      String.join (cases.map check)
    let out ← try
        some <$> IO.Process.output { cmd := "node", args := #["--input-type=module", "-e", script] }
      catch _ => pure none
    match out with
    | none => pure ()  -- no `node`: nothing to run
    | some out =>
      assertEq "node" "" (if out.exitCode == 0 then "" else out.stderr)
      let lines := (out.stdout.splitOn "\n").filter (· ≠ "")
      assertEq "one line per case" cases.length lines.length
      for (c, got) in cases.zip lines do
        assertEq s!"{c.1}({c.2.2}, {c.2.1})" "true,true,true,true,true" got
  it "runtime.js exports every imported operation" do
    let src ← IO.FS.readFile "runtime.js"
    let missing := JsOpImported.names.toList.filter fun n =>
      (src.splitOn s!"export const {jsSafeName n} =").length < 2
    assertEq "missing" ([] : List String) missing
  it "the version constants of runtime.js are the ones of this Lean" do
    let src ← IO.FS.readFile "runtime.js"
    let has (decl : String) : Bool := (src.splitOn decl).length > 1
    for decl in [
        s!"export const bigint_nat__lean_version_get_major = () => () => {Lean.version.major}n;",
        s!"export const uint53__lean_version_get_minor = () => () => {Lean.version.minor};",
        s!"export const uint53__lean_version_get_patch = () => () => {Lean.version.patch};",
        s!"export const bool__lean_version_get_is_release = () => () => {Lean.version.isRelease};",
        s!"export const string__lean_version_get_special_desc = () => () => {Lean.version.specialDesc.quote};",
        s!"export const string__lean_get_githash = () => () => {Lean.githash.quote};",
        s!"export const string__lean_system_platform_target = () => () => {System.Platform.target.quote};"] do
      assertEq decl true (has decl)
  it "runtime.js computes what Lean computes (needs node)" do
    -- each case: a JavaScript expression over the runtime, and what Lean computes, as
    -- JavaScript's `String(v)` writes it
    let pair (a b : String) : String := a ++ "," ++ b
    -- the bits of a `float32` result, as a `Float32Array` stores them
    let f32Bits (e : String) : String := s!"new Uint32Array(new Float32Array([{e}]).buffer)[0]"
    let cases : List (String × String) := [
      ("bigint_nat__lean_string_hash(\"hello\")", toString "hello".hash),
      ("bigint_nat__lean_string_hash(\"héllo€😀\")", toString "héllo€😀".hash),
      -- a hash past `2^53` does not fit in a `uint53`: a `RangeError`, never a wrong number
      ("(() => { try { return uint53__lean_string_hash(\"\"); } catch (e) { return e.name; } })()",
        if "".hash.toNat ≤ 2 ^ 53 - 1 then toString "".hash else "RangeError"),
      ("bigint_nat__lean_uint64_mix_hash(1n, 2n)", toString (mixHash 1 2)),
      ("float__lean_float_to_string(0.1)", toString (0.1 : Float)),
      ("float__lean_float_to_string(-2.5e-7)", toString (-2.5e-7 : Float)),
      ("float__lean_float_to_string(1e300)", toString (1e300 : Float)),
      ("float__lean_float_to_string(1/0)", toString (1.0 / 0.0 : Float)),
      ("float32__lean_float32_to_string(Math.fround(0.1))", toString (0.1 : Float32)),
      ("(r => r._1 + ',' + r._2)(bigint_int__lean_float_frexp(12.5))",
        pair (numberSource (12.5 : Float).frExp.1) (toString (12.5 : Float).frExp.2)),
      ("bigint_int__lean_float_scaleb(1.5, 10n)", numberSource ((1.5 : Float).scaleB 10)),
      ("float__lean_float_to_uint8(300.7)", toString (300.7 : Float).toUInt8),
      ("float__lean_float_to_uint8(-5)", toString (-5.0 : Float).toUInt8),
      ("bigint_nat__lean_float_to_bits__Float_toBits(-2.5)", toString (-2.5 : Float).toBits),
      ("string__lean_string_utf8_prev__String_Pos_Raw_prev(\"aé€\", 6)",
        toString (String.Pos.Raw.prev "aé€" ⟨6⟩).byteIdx),
      ("string__lean_string_utf8_get_opt__String_Pos_Raw_get$3F(\"aé\", 2).tag",
        if (String.Pos.Raw.get? "aé" ⟨2⟩).isSome then "1" else "0"),
      -- a 64-bit integer to a `Float32` rounds once: `2^63 + 2^39 + 1` is just above the
      -- midpoint of two floats (rounding to a double first would land on the midpoint)
      (f32Bits "bigint_nat__lean_uint64_to_float32(9223372586610589697n)",
        toString (9223372586610589697 : UInt64).toFloat32.toBits),
      (f32Bits "bigint_nat__lean_uint64_to_float32(9223372586610589696n)",
        toString (9223372586610589696 : UInt64).toFloat32.toBits),
      (f32Bits "bigint_nat__lean_uint64_to_float32(18446744073709551615n)",
        toString (18446744073709551615 : UInt64).toFloat32.toBits),
      (f32Bits "bigint_nat__lean_uint64_to_float32(16777217n)",
        toString (16777217 : UInt64).toFloat32.toBits),
      (f32Bits "bigint_int__lean_int64_to_float32(-4611686293305294849n)",
        toString (-4611686293305294849 : Int64).toFloat32.toBits),
      (f32Bits "bigint_int__lean_int64_to_float32(-9223372036854775808n)",
        toString (-9223372036854775808 : Int64).toFloat32.toBits),
      (f32Bits "bigint_int__lean_int64_to_float32(-16777219n)",
        toString (-16777219 : Int64).toFloat32.toBits)]
    let cwd ← IO.currentDir
    let names := ["bigint_nat__lean_string_hash", "uint53__lean_string_hash",
      "bigint_nat__lean_uint64_mix_hash", "float__lean_float_to_string",
      "float32__lean_float32_to_string", "bigint_int__lean_float_frexp",
      "bigint_int__lean_float_scaleb", "float__lean_float_to_uint8",
      "bigint_nat__lean_float_to_bits__Float_toBits",
      "string__lean_string_utf8_prev__String_Pos_Raw_prev",
      "string__lean_string_utf8_get_opt__String_Pos_Raw_get$3F",
      "bigint_nat__lean_uint64_to_float32", "bigint_int__lean_int64_to_float32"]
    let script := s!"import \{ {", ".intercalate names} } from {(s!"file://{cwd}/runtime.js").quote};\n" ++
      String.join (cases.map fun (c : String × String) => s!"console.log(String({c.1}));\n")
    let out ← try
        some <$> IO.Process.output { cmd := "node", args := #["--input-type=module", "-e", script] }
      catch _ => pure none
    match out with
    | none => pure ()  -- no `node`: nothing to compare with
    | some out =>
      assertEq "node" "" (if out.exitCode == 0 then "" else out.stderr)
      let lines := (out.stdout.splitOn "\n").filter (· ≠ "")
      assertEq "one line per case" cases.length lines.length
      for ((js, expected), got) in cases.zip lines do
        assertEq js expected got
  it "List is tagged cons cells (faithful) or a JavaScript array (pbo)" do
    let listNat : LeanScript.Ty [] := .list .nat
    assertEq "faithful" "ConsList<nat(bigint)>" (lowerTy faithful listNat).pretty
    assertEq "pbo" "List<uint53(number)>" (lowerTy pbo listNat).pretty
    assertEq "default is faithful's" ListRepr.taggedUnion ({} : JsConfig).listRepr
    assertEq "knob" (some ListRepr.stdListToJsArray) ((faithful.setKnob? "list" "array").map JsConfig.listRepr)
    assertEq "described" true ((faithful.describe.splitOn "list=tagged").length > 1)
    assertEq "described (pbo)" true ((pbo.describe.splitOn "list=array").length > 1)
    -- a user datatype shaped like a list is a datatype (a tagged union), whatever `listRepr`
    let myList : LeanScript.Ty [2] := .data (.here ⟨0, by decide⟩)
    assertEq "a datatype does not depend on listRepr" (lowerTy faithful myList).pretty
      (lowerTy pbo myList).pretty
  it "an extern on lists converts cons cells at its boundary" do
    let lc : JsTy := .consList tN
    let shown {C M : List JsTy} {τ : JsTy} (e : Except String (JsExpr S C M τ)) : String :=
      match e with
      | .ok e => e.pretty ""
      | .error msg => s!"error: {msg}"
    let arg {σ : JsTy} : JsArgs S [σ] [] [σ] := .cons (.cvar .zero) .nil
    assertEq "List.toArray" "inline:array__lean_array_mk(consList__to_array(c0))"
      (shown (lowerExtern "lean_array_mk" arg : Except String (JsExpr S [lc] [] tA)))
    assertEq "Array.toList" "consList__of_array(inline:array__lean_array_to_list(c0))"
      (shown (lowerExtern "lean_array_to_list" arg : Except String (JsExpr S [tA] [] lc)))
    -- the elements of a polymorphic operation are passed as they are
    let ll : JsTy := .consList lc
    assertEq "Array (List Nat) → List (List Nat)"
      "consList__of_array(inline:array__lean_array_to_list(c0))"
      (shown (lowerExtern "lean_array_to_list" arg : Except String (JsExpr S [.array lc] [] ll)))
    -- the grammar is not rewritten: a round trip through the array layout is written as it is
    -- (every optimisation is done on `Term`)
    let rt : JsExpr S [lc] [] lc := (JsExpr.toArrayList (.cvar .zero)).ofArrayList
    assertEq "round trip" "consList__of_array(consList__to_array(c0))" (rt.pretty "")
  it "the cons cells of runtime.js (needs node)" do
    let cwd ← IO.currentDir
    let names := ["consList__of_array", "consList__of_array_onto", "consList__to_array",
      "consList__append"]
    let src ← IO.FS.readFile "runtime.js"
    for n in names do
      assertEq s!"exports {n}" true ((src.splitOn s!"export const {n} =").length > 1)
    let script := s!"import \{ {", ".intercalate names} } from {(s!"file://{cwd}/runtime.js").quote};\n" ++
      "const t = consList__of_array([3, 4]);\n" ++
      "const l = consList__of_array_onto([1, 2], t);\n" ++
      "console.log(JSON.stringify(consList__of_array([])));\n" ++
      "console.log(JSON.stringify(consList__of_array([7])));\n" ++
      "console.log(consList__to_array(l).join());\n" ++
      "console.log(l._2._2 === t);\n" ++
      "console.log(consList__to_array(consList__of_array([])).length);\n" ++
      "const u = consList__append(consList__of_array([0]), l);\n" ++
      "console.log(consList__to_array(u).join(), u._2 === l, consList__append(l, consList__of_array([])) === l);\n"
    let out ← try
        some <$> IO.Process.output { cmd := "node", args := #["--input-type=module", "-e", script] }
      catch _ => pure none
    match out with
    | none => pure ()  -- no `node`: nothing to run
    | some out =>
      assertEq "node" "" (if out.exitCode == 0 then "" else out.stderr)
      assertEq "output" ["{\"tag\":0}", "{\"tag\":1,\"_1\":7,\"_2\":{\"tag\":0}}", "1,2,3,4", "true", "0",
        "0,1,2,3,4 true true"]
        ((out.stdout.splitOn "\n").filter (· ≠ ""))
  let conv (cfg : JsConfig) (name : String) (ps : List String) (ct : ClosedTerm) :
      IO JsFun :=
    match termToJs cfg name name ps ct with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"{name}: {e}")
  for (cfgName, cfg) in [("faithful", faithful), ("pbo", pbo)] do
    it s!"ack2 converts ({cfgName})" do
      let f ← conv cfg "ack2" ["m", "n"] ⟨[], .nil, _, _, Tco.ack2T⟩
      -- `ack2` is `fun m => nat_rec …` (a function of `n`): uncurried, the exported function
      -- takes both parameters of its type
      assertEq "parameters" ["m", "n"] (f.params.map (fun (p : String × JsTy) => p.1))
      assertEq "exported" true ((f.pretty.splitOn "export const ack2 = (m : ").length > 1)
    it s!"hyperWhile converts to loops ({cfgName})" do
      let f ← conv cfg "hyperWhile" ["n", "a", "b"] ⟨[], .nil, _, _, Tco.hyperWhileT⟩
      assertEq "a for loop" true ((f.pretty.splitOn "for (").length > 1)
    it s!"bits converts ({cfgName})" do
      let f ← conv cfg "bits" ["n"] ⟨[], .nil, _, _, WhileTest.bitsT⟩
      assertEq "result type" (lowerScalarPrim cfg .nat).pretty f.ret.pretty
    it s!"folds of declared datatypes are mutually recursive local functions ({cfgName})" do
      let has (f : JsFun) (s : String) : Bool := (f.pretty.splitOn s).length > 1
      -- `RoseA := node (Array RoseA)`: the array of children is mapped by a loop
      let rA ← conv cfg "roseASize" ["r"] ⟨_, RoseVariantsTest.Prog.Δ, _, _, RoseVariantsTest.roseASizeT⟩
      assertEq "RoseA: the functions of the fold" true (has rA "const go0 = (v)")
      assertEq "RoseA: the children mapped by a loop" true (has rA "array__lean_array_push_mutable")
      -- `RoseF := node (m : Nat) (Fin m → RoseF)`: two members (`Option RoseF`, `RoseF`), a
      -- function field mapped by a lambda
      let rF ← conv cfg "roseFSize" ["r"] ⟨_, RoseVariantsTest.Prog.Δ, _, _, RoseVariantsTest.roseFSizeT⟩
      assertEq "RoseF: two mutually recursive functions" true (has rF "const go1 = (v)")
      -- `RoseL := node (List RoseL)` and `T5 := node (Array (Option T5 × Nat))`
      let rL ← conv cfg "roseLSize" ["r"] ⟨_, RoseVariantsTest.Prog.Δ, _, _, RoseVariantsTest.roseLSizeT⟩
      assertEq "RoseL: two mutually recursive functions" true (has rL "const go1 = (v)")
      let t5 ← conv cfg "t5Sum" ["t"] ⟨_, RoseVariantsTest.Prog.Δ, _, _, RoseVariantsTest.t5SumT⟩
      assertEq "T5: three members" true (has t5 "const go2 = (v)")

end MoreJsTests

section WFTerm
open WFTermTest

/-- `name`: the program computes `expected`, before and after optimisation. -/
def checkNatOpt (name : String) (expected run optimized : Nat) : SpecM Unit Unit :=
  it name do
    assertEq s!"{name} (run)" expected run
    assertEq s!"{name} (optimized)" expected optimized

/-- `Tests/TermTests/Optimize/WFTermTest.lean`: programs with well-founded recursion (`WFTerm`), run by
the total evaluator `WFProgram.run` (no fuel), before and after `WFProgram.optimize`. -/
def wfTermSpec : Spec := describe "WFTerm" do
  checkNatOpt "gcd 48 18" 6 (natOf (gcdProg 48 18).run.1) (natOf (gcdProg 48 18).optimize.run.1)
  checkNatOpt "gcd 1071 462" (Nat.gcd 1071 462) (natOf (gcdProg 1071 462).run.1)
    (natOf (gcdProg 1071 462).optimize.run.1)
  checkNatOpt "gcd (fib 90) (fib 89)" 1 (natOf (gcdProg 2880067194370816120 1779979416004714189).run.1)
    (natOf (gcdProg 2880067194370816120 1779979416004714189).optimize.run.1)
  checkNatOpt "ack 2 3" 9 (natOf (ackProg 2 3).run.1) (natOf (ackProg 2 3).optimize.run.1)
  checkNatOpt "ack 3 3" 61 (natOf (ackProg 3 3).run.1) (natOf (ackProg 3 3).optimize.run.1)
  checkNatOpt "countdown 100000 (joinrec)" 7 (natOf (countdown 100000).run.1)
    (natOf (countdown 100000).optimize.run.1)
  it "map (gcd · 12) [8, 9, 10]" do
    assertEq "run" [4, 3, 2] ((gcdMap.run.1 : List (Ty.Den D .nat)).map natOf)
    assertEq "optimized" [4, 3, 2] ((gcdMap.optimize.run.1 : List (Ty.Den D .nat)).map natOf)

end WFTerm

def spec : Spec := do
  tcoSpec
  whileSpec
  quotientSpec
  roseSpec
  optimizeSpec
  moreJsSpec
  wfTermSpec

public def main (args : List String) : IO UInt32 :=
  runSpecFromArgsAndReturnExitCode args spec
