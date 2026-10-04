module

import Spec.RunSpec
import TermTests.ToTerm.TcoTest
import TermTests.ToTerm.WhileTest
import TermTests.Datatypes.QuotientTest
import TermTests.Datatypes.RoseVariantsTest
import TermTests.Optimize.WFTermTest
import TermTests.Optimize.AppendTest
import TermTests.Optimize.ArithTest
import TermTests.Optimize.CseTest
import TermTests.Optimize.FloatCommTest
import TermTests.Optimize.MergeTestTest
import TermTests.Optimize.SinkLetTest
import TermTests.Optimize.FunctionComposeTest
import TermTests.Optimize.FunctionCompose02Test
import TermTests.Optimize.FunctionCompose03Test
import TermTests.ToTerm.PolymorphismTest
import LeanScript.Term.Pretty
import LeanScript.Term.Optimize.Basic
import JsTerm.Lower.FromTerm
import JsTerm.Lower.Module
import JsTerm.Lower.Ident
import JsTerm.Syntax.Pretty
import RuntimeSpec.InlineShift

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

/-- `Tests/TermTests/Optimize/AppendTest.lean`: the optimiser regroups chains of `++` to the
    right, drops empty literals and merges neighbouring literals (`Term.appendWalk`); the
    optimised statements, printed, and their values (compiled). -/
def appendSpec : Spec := describe "Term.appendWalk" do
  it "AssocArrayAppend.ArrayTest.test1: one literal in front, one at the end" do
    assertEq "printed" ("val k1 [1] : ((Array String) → (Array String)) := " ++
      "fun x2 [ω] : (Array String) => (closed)\n  ret lean_array_append(lean_array_append(" ++
      "lean_array_append(lean_array_append(lean_array_append(#[\"a\", \"b\"], x2), x2), x2), " ++
      "x2), #[\"c\", \"d\"])\nret k1")
      ((AppendTest.arrTest1T (Δ := DSig.nil)).optimizeN 3).pretty
    assertEq "value" (AppendTest.arrTest1 #["x", "y"])
      (((AppendTest.arrTest1T (Δ := DSig.nil)).optimizeN 3).run #["x", "y"])
  it "AssocArrayAppend.ArrayTest.test3: literals between the operands are merged" do
    assertEq "printed" ("val k1 [1] : ((Array String) → (Array String)) := " ++
      "fun x2 [ω] : (Array String) => (closed)\n  ret lean_array_append(lean_array_append(" ++
      "lean_array_append(lean_array_append(lean_array_append(lean_array_append(" ++
      "lean_array_append(lean_array_append(lean_array_append(lean_array_append(" ++
      "#[\"a\", \"b\"], x2), x2), x2), x2), #[\"c\", \"d\", \"e\"]), x2), x2), x2), x2), " ++
      "#[\"f\", \"g\"])\nret k1")
      ((AppendTest.arrTest3T (Δ := DSig.nil)).optimizeN 3).pretty
    assertEq "value" (AppendTest.arrTest3 #["x"])
      (((AppendTest.arrTest3T (Δ := DSig.nil)).optimizeN 3).run #["x"])
  it "empty literals are dropped" do
    assertEq "printed" ("val k1 [1] : ((Array Nat) → (Array Nat)) := " ++
      "fun x2 [1] : (Array Nat) => (closed)\n  ret lean_array_append(" ++
      "lean_array_append(#[1, 2], x2), #[3])\nret k1")
      ((AppendTest.arrEmptyT (Δ := DSig.nil)).optimizeN 3).pretty
    assertEq "value" (AppendTest.arrEmpty #[7, 8])
      (((AppendTest.arrEmptyT (Δ := DSig.nil)).optimizeN 3).run (#[7, 8] : Array Nat))

/-- `Tests/TermTests/Optimize/AppendTest.lean`, `knownLit`: the operand of an append that names
    a `val` of a constant array literal is the literal itself (`Term.knownLits`), and the `val`
    is dropped. -/
def knownLitSpec : Spec := describe "Term.knownLits" do
  it "AppendTest.knownLit: the literal written in place" do
    let t := AppendTest.knownLitT (Δ := DSig.nil)
    -- the translation names the literal, and appends the name
    assertEq "a val of the literal" true ((t.pretty.splitOn ":= #[\"h\"]").length > 1)
    assertEq "no append starts with the literal" false
      ((t.pretty.splitOn "lean_array_append(#[\"h\"]").length > 1)
    -- `Term.knownLits` alone writes it in place
    assertEq "Term.knownLits" true
      ((t.knownLits.pretty.splitOn "lean_array_append(#[\"h\"], ").length > 1)
    assertEq "printed" ("val k1 [1] : ((String × (Array String)) → (String × (Array String))) := " ++
      "fun x2 [1] : (String × (Array String)) => (closed)\n" ++
      "  let ⟨f3 [1] : String, f4 [1] : (Array String)⟩ := x2\n" ++
      "  ret ⟨lean_string_append__String_append(\"h\", f3), lean_array_append(#[\"h\"], f4)⟩\n" ++
      "ret k1") (t.optimizeN 3).pretty
    assertEq "value" (AppendTest.knownLit ⟨"x", #["y"]⟩).a
      (((AppendTest.knownLitT (Δ := DSig.nil)).optimizeN 3).run ("x", #["y"])).2

/-- `Tests/TermTests/Optimize/ArithTest.lean`: the optimiser folds the literals of chains of
    `+` and `*`, counts the copies of an unknown in a sum (`x * k`) and in a product (`x ^ k`)
    and combines the operands from the left (`Term.arithWalk`); the optimised statements, printed, and their values (compiled). -/
def arithSpec : Spec := describe "Term.arithWalk" do
  it "AssocIntOps.test1: 1 + (((((2 + x) + x) + x) + x) + 3) + 4 is x * 4 + 10" do
    assertEq "printed" ("val k1 [1] : (Int → Int) := fun x2 [1] : Int => (closed)\n" ++
      "  ret lean_int_add(lean_int_mul(x2, 4), 10)\nret k1")
      ((ArithTest.test1T (Δ := DSig.nil)).optimizeN 3).pretty
    for x in [(-7 : Int), 0, 12] do
      assertEq s!"value at {x}" (ArithTest.test1 x) (((ArithTest.test1T (Δ := DSig.nil)).optimizeN 3).run x)
  it "AssocIntOps.test3: two chains, x * 8 + 28" do
    for x in [(-7 : Int), 0, 12] do
      assertEq s!"value at {x}" (ArithTest.test3 x) (((ArithTest.test3T (Δ := DSig.nil)).optimizeN 3).run x)
  it "AssocIntOps.test5: 1 * (2 * (x * (x * (x * (x * 3))))) * 4 is x ^ 4 * 24" do
    assertEq "printed" ("val k1 [1] : (Int → Int) := fun x2 [1] : Int => (closed)\n" ++
      "  ret lean_int_mul(lean_int_pow(x2, 4), 24)\nret k1")
      ((ArithTest.test5T (Δ := DSig.nil)).optimizeN 3).pretty
    for x in [(-7 : Int), 0, 12] do
      assertEq s!"value at {x}" (ArithTest.test5 x) (((ArithTest.test5T (Δ := DSig.nil)).optimizeN 3).run x)
  it "UInt8: the literals are folded modulo 2^8" do
    assertEq "printed" ("val k1 [1] : (UInt8 → UInt8) := fun x2 [1] : UInt8 => (closed)\n" ++
      "  ret lean_uint8_add(x2, 144)\nret k1")
      ((ArithTest.wrap8T (Δ := DSig.nil)).optimizeN 3).pretty
    for x in [(0 : UInt8), 55, 56, 255] do
      assertEq s!"value at {x}" (ArithTest.wrap8 x) (((ArithTest.wrap8T (Δ := DSig.nil)).optimizeN 3).run x)
  it "two unknowns are counted separately" do
    assertEq "printed" ("val k1 [1] : (Nat → (Nat → Nat)) := fun x2 [ω] : Nat => (closed)\n" ++
      "  val k3 [1] : (Nat → Nat) := fun x4 [1] : Nat => (open)\n" ++
      "    ret lean_nat_add(lean_nat_add(lean_nat_mul(x2, 3), lean_nat_mul(x4, 2)), 1)\n" ++
      "  ret k3\nret k1")
      ((ArithTest.twoVarsT (Δ := DSig.nil)).optimizeN 3).pretty
    assertEq "value" (ArithTest.twoVars 5 7) (((ArithTest.twoVarsT (Δ := DSig.nil)).optimizeN 3).run (5 : Nat) (7 : Nat))
  it "Nat: three copies of an unknown in a product are a power, two stay" do
    assertEq "printed" ("val k1 [1] : (Nat → Nat) := fun x2 [ω] : Nat => (closed)\n" ++
      "  ret lean_nat_add(lean_nat_mul(lean_nat_pow(x2, 3), 7), lean_nat_mul(x2, x2))\nret k1")
      ((ArithTest.natCubeT (Δ := DSig.nil)).optimizeN 3).pretty
    for x in [(0 : Nat), 1, 5, 12] do
      assertEq s!"value at {x}" (ArithTest.natCube x) (((ArithTest.natCubeT (Δ := DSig.nil)).optimizeN 3).run x)

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
def myListSig : JsSig := { decls := #[.obj (.union [0, 2] .cells) [tN, .obj (.decl 0) []]] }

/-- `(x) => fold(cons(1, fold(nil)))`, over `myListSig`: the casts print as nothing. -/
def myListFun : JsFun where
  name := "f"
  leanName := "f"
  sig := myListSig
  params := [("x", tN)]
  ret := .obj (.decl 0) []
  body := .ret (.fold 0 (.union_mk (id := .union [0, 2] .cells) (.succ .zero)
    (.cons (.cvar .zero) (.cons (.fold 0 (.union_mk (id := .union [0, 2] .cells) .zero .nil)) .nil))))

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
    let u0 : JsExpr S [] [] (.obj (.union [0, 1] .cells) [tN]) := .union_mk .zero .nil
    let u1 : JsExpr S [] [] (.obj (.union [0, 1] .cells) [tN]) := .union_mk (.succ .zero) (.cons one .nil)
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
    assertEq "Option String" (repr (JsObjId.union [0, 1] .cells)).pretty
      (match lowerTy pbo optS with | .obj id _ => (repr id).pretty | _ => "?")
    assertEq "Option Nat" (repr (JsObjId.union [0, 1] .cells)).pretty
      (match lowerTy pbo optN with | .obj id _ => (repr id).pretty | _ => "?")
    assertEq "constructors of Option String" "[[], [string]]"
      (toString ((S.ctorsOf (.union [0, 1] .cells) [.terminal .string]).map fun (cs : List JsTy) => cs.map JsTy.pretty))
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
  it "canonical layout ids: datatypes of equal layouts share one id (proposal R)" do
    let d (i : Nat) : JsTy := .obj (.decl i) []
    let lst (e : JsTy) (i : Nat) : JsTy := .obj (.union [0, 2] .cells) [e, d i]
    -- `D0 := nil | cons N D0`, `D1` the same, `D2 := nil | cons string D2`, `D3 := nil | cons
    -- N D1` (a list of `N` whose tail is a `D1`: the same infinite tree), `D4 := leaf | node D4
    -- N D5`, `D5 := leaf | node D5 N D4` (two mutually recursive trees of one layout)
    let tree (i j : Nat) : JsTy := .obj (.union [0, 3] .cells) [d i, tN, d j]
    let bodies : Array JsTy := #[lst tN 0, lst tN 1, lst (.terminal .string) 2, lst tN 1,
      tree 4 5, tree 5 4]
    let cls := canonDecls bodies
    assertEq "classes" [0, 0, 2, 0, 4, 4] ((List.range 6).map (classOf cls))
    assertEq "the classes are a bisimulation" true (isBisim bodies (refineClasses bodies))
    -- `canonDecls_sound`: the unfoldings agree (here at depth 3)
    assertEq "D3 unfolds as D0" true
      (JsTy.unfoldDecls bodies 3 (d 3) == JsTy.unfoldDecls bodies 3 (d 0))
    assertEq "D2 does not unfold as D0" false
      (JsTy.unfoldDecls bodies 3 (d 2) == JsTy.unfoldDecls bodies 3 (d 0))
    -- the configuration that `termToJs` sets: every datatype named by its canonical id
    let cfg : JsConfig := { declCanon := cls }
    let dataTy (i : Fin 7) : LeanScript.Ty [6] := .data (.here i)
    assertEq "D1 is named D0" (d 0).pretty (lowerTy cfg (dataTy 1)).pretty
    assertEq "D5 is named D4" (d 4).pretty (lowerTy cfg (dataTy 5)).pretty
  it "the representation of a union is part of its identity (proposal S)" do
    let small : JsConfig := { pbo with nullaryRepr := .smallInt }
    let optN : LeanScript.Ty [] := .union (.two .nullary (.fields (.one .nat)))
    let pairs : LeanScript.Ty [] := .union (.two (.fields (.one .nat)) (.fields (.one .string)))
    assertEq "Option Nat, numbers" (repr (JsObjId.union [0, 1] .smallIntNullary)).pretty
      (match lowerTy small optN with | .obj id _ => (repr id).pretty | _ => "?")
    assertEq "Option Nat, cells (the default)" (repr (JsObjId.union [0, 1] .cells)).pretty
      (match lowerTy pbo optN with | .obj id _ => (repr id).pretty | _ => "?")
    -- a union whose constructors all have fields has nothing to change
    assertEq "no constructor without fields" (repr (JsObjId.union [1, 1] .cells)).pretty
      (match lowerTy small pairs with | .obj id _ => (repr id).pretty | _ => "?")
    let sid : JsObjId := .union [0, 1] .smallIntNullary
    let n0 : JsExpr S [] [] (.obj sid [tN]) := .union_mk .zero .nil
    let n1 : JsExpr S [] [] (.obj sid [tN]) := .union_mk (.succ .zero) (.cons one .nil)
    assertEq "nullary constructor: a number" "0" (n0.pretty "")
    assertEq "constructor with fields: an object" "{ tag: 1, _1: 1 }" (n1.pretty "")
    assertEq "the type" "(0 | { tag: 1, _1: uint53(number) })" (JsTy.obj sid [tN]).pretty
    -- the operations of the catalogue answer cells: the answer is converted
    let str : JsTy := .terminal .string
    let args : JsArgs S [str, tN] [] [str, tN] := .cons (.cvar .zero) (.cons (.cvar (.succ .zero)) .nil)
    let shown {C M : List JsTy} {τ : JsTy} (e : Except String (JsExpr S C M τ)) : String :=
      match e with
      | .ok e => e.pretty ""
      | .error msg => s!"error: {msg}"
    assertEq "String.get?, cells"
      "string__lean_string_utf8_get_opt__String_Pos_Raw_get?(c0, c1)"
      (shown (lowerExtern "lean_string_utf8_get_opt__String_Pos_Raw_get?" args :
        Except String (JsExpr S [str, tN] [] (.obj (.union [0, 1] .cells) [str]))))
    assertEq "String.get?, numbers"
      "obj__nullary_to_int(string__lean_string_utf8_get_opt__String_Pos_Raw_get?(c0, c1))"
      (shown (lowerExtern "lean_string_utf8_get_opt__String_Pos_Raw_get?" args :
        Except String (JsExpr S [str, tN] [] (.obj (.union [0, 1] .smallIntNullary) [str]))))
    assertEq "the configuration line" true
      ((small.describe.splitOn "nullary=int").length > 1 && (pbo.describe.splitOn "nullary").length == 1)
  it "the conversions of unions of runtime.js (needs node)" do
    let cwd ← IO.currentDir
    let names := JsListOp.runtimeNames
    let src ← IO.FS.readFile "runtime.js"
    for n in names do
      assertEq s!"exports {n}" true ((src.splitOn s!"export const {n} =").length > 1)
    let script := s!"import \{ {", ".intercalate names} } from {(s!"file://{cwd}/runtime.js").quote};\n" ++
      "console.log(JSON.stringify([obj__nullary_to_int({ tag: 0 }), obj__nullary_to_int({ tag: 2 }), obj__nullary_to_int({ tag: 1, _1: 'a' })]));\n" ++
      "console.log(JSON.stringify([obj__nullary_to_cells(0), obj__nullary_to_cells(2), obj__nullary_to_cells({ tag: 1, _1: 'a' })]));\n"
    let out ← try
        some <$> IO.Process.output { cmd := "node", args := #["--input-type=module", "-e", script] }
      catch _ => pure none
    match out with
    | none => pure ()  -- no `node`: nothing to run
    | some out =>
      assertEq "node" "" (if out.exitCode == 0 then "" else out.stderr)
      assertEq "output" ["[0,2,{\"tag\":1,\"_1\":\"a\"}]", "[{\"tag\":0},{\"tag\":2},{\"tag\":1,\"_1\":\"a\"}]"]
        ((out.stdout.splitOn "\n").filter (· ≠ ""))
  -- `--check` on `RecData` evaluates its checks in Lean (about 18 s alone), so under a parallel
  -- load the default 30 s are not enough.
  it "constructors without fields as numbers: the generated code runs (needs node and leanscript)"
      (timeoutMs? := some 120000) do
    -- `leanscript --nullary=int` on programs over declared datatypes, `Option`s and lists, and
    -- the differential checks it writes run against Lean's answers
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/nullary-int"
    IO.FS.createDirAll dir
    for file in ["RecData", "ListRepr"] do
      let args := #["--quiet", "--check", "--nullary=int", s!"--out-dir={dir}",
        s!"Tests/SnapshotsMy/{file}.lean"]
      let out ← IO.Process.output { cmd := bin.toString, args }
      assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
      for preset in ["pbo", "faithful"] do
        let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
        assertEq s!"{file}-{preset}: the configuration" true ((js.splitOn "nullary=int").length > 1)
        let run ← IO.Process.output { cmd := "node", args := #[s!"{file}-{preset}.check.mjs"], cwd := dir }
        assertEq s!"{file}-{preset}: node" "" (if run.exitCode == 0 then "" else run.stderr)
        assertEq s!"{file}-{preset}: no check failed" true
          ((run.stdout.splitOn " 0 failed").length > 1 && (run.stdout.splitOn "FAIL").length == 1)
    -- a user's list: `nil` is `0` and is tested by `=== 0`
    let js ← IO.FS.readFile s!"{dir}/RecData-pbo.js"
    assertEq "a nullary constructor is tested by ===" true ((js.splitOn " === 0").length > 1)
    assertEq "no nullary constructor is an object" 1 (js.splitOn "{ tag: 0 }").length
  it "the fall-through of a decision tree is written once (needs node and leanscript)" do
    -- `CaseHeuristics`: the last pattern `_, _ => …` of each match is copied into every branch
    -- of the decision tree; it is written once, after the tests (`JsTerm.Lower.ShareTail`), and
    -- the arms that are the same are tested once (`groupedChain`).  The differential checks
    -- compare every answer with Lean's.
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/shareTail"
    IO.FS.createDirAll dir
    let file := "CaseHeuristics"
    let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    for preset in ["pbo", "faithful"] do
      let run ← IO.Process.output { cmd := "node", args := #[s!"{file}-{preset}.check.mjs"], cwd := dir }
      assertEq s!"{file}-{preset}: node" "" (if run.exitCode == 0 then "" else run.stderr)
      assertEq s!"{file}-{preset}: no check failed" true
        ((run.stdout.splitOn " 0 failed").length > 1 && (run.stdout.splitOn "FAIL").length == 1)
    let js ← IO.FS.readFile s!"{dir}/{file}-pbo.js"
    let body (f : String) : String :=
      ((js.splitOn s!"export const {f} ").getD 1 "").splitOn "export const" |>.headD ""
    -- `testPB`: its fall-through `_, .zero => 3 | _, _ => 4` once, and no test of a tag twice
    assertEq "testPB: the fall-through once" 2 ((body "testPB").splitOn "a1.tag === 0").length
    assertEq "testPB: `4` returned once" 2 ((body "testPB").splitOn " 4;").length
    -- `testPBA`, `testPBAN`: `_, _ => 4` once
    for f in ["testPBA", "testPBAN"] do
      assertEq s!"{f}: `return 4` once" 2 ((body f).splitOn "return 4;").length
      assertEq s!"{f}: no test of the same tag twice" 1 ((body f).splitOn "? 4 : 4").length
  it "a shared tail never tests again what its jumps already tested (needs node and leanscript)" do
    -- `CaseMulti`: `match x, y with | 1, 1 | 1, 2 | 1, 3 | _, 4 | 1, 5 | _, 2 | _, _`.  A jump to a
    -- shared tail that the tests around it specialise runs those tests again (`retestCost`):
    -- on every input, the generated function makes no more comparisons than
    -- purescript-backend-optimizer's (`legacy-backend/CaseMulti.js`), and answers what Lean does.
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/caseMulti"
    IO.FS.createDirAll dir
    let file := "CaseMulti"
    let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    let xs : List Int := [0, 1, 2]
    let ys : List Int := [0, 1, 2, 3, 4, 5, 6]
    let lean (x y : Int) : String :=
      match x, y with
      | 1, 1 => "1.1"
      | 1, 2 => "1.2"
      | 1, 3 => "1.3"
      | _, 4 => "_.4"
      | 1, 5 => "1.5"
      | _, 2 => "_.2"
      | _, _ => "_._"
    let count (js : String) (curried : String) : IO (List (List String)) := do
      let args := #["scripts/count-comparisons.mjs", js, "test1", curried, toString xs, toString ys]
      let run ← IO.Process.output { cmd := "node", args }
      if run.exitCode != 0 then throw (IO.userError run.stderr)
      return ((run.stdout.splitOn "\n").filter (· != "")).map (fun (l : String) => l.splitOn ",")
    let pbo ← count "Tests/SnapshotsPBOPure/legacy-backend/CaseMulti.js" "1"
    for preset in ["pbo", "faithful"] do
      let ours ← count s!"{dir}/{file}-{preset}.js" "0"
      assertEq s!"{file}-{preset}: every pair run" (xs.length * ys.length) ours.length
      for (o, p) in ours.zip pbo do
        match o, p with
        | [x, y, r, n], [_, _, _, m] =>
          let expected := lean x.toInt! y.toInt!
          assertEq s!"{file}-{preset}: test1 {x} {y}" expected r
          assertEq s!"{file}-{preset}: test1 {x} {y} makes at most PBO's {m} comparisons" true
            (n.toNat! ≤ m.toNat!)
        | _, _ => assertEq s!"{file}-{preset}: a line of the counts" ["x", "y", "r", "n"] o
  it "a structure of one field is its field: matching on it is one comparison per arm (needs node and leanscript)" do
    -- `CaseNewtype`: `NewTypeInt` has one field, so its JavaScript value is the `Int` itself;
    -- `match v.val with` and `match v with | ⟨1⟩ …` both test it once per arm, as
    -- purescript-backend-optimizer does (`legacy-backend/CaseNewtype.js`): on every input the
    -- generated functions make no more comparisons than PBO's, and answer what Lean does.  The
    -- differential checks try every arm too (`SType.wrap`, and `1`, `2` among the `Int` samples).
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/caseNewtype"
    IO.FS.createDirAll dir
    let file := "CaseNewtype"
    let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    let xs : List Int := [-1, 0, 1, 2, 3, 4, 12]
    let lean (x : Int) : String :=
      match x with
      | 1 => "1"
      | 2 => "2"
      | 3 => "3"
      | _ => "catch"
    let count (js f : String) : IO (List (List String)) := do
      let args := #["scripts/count-comparisons.mjs", js, f, "0", toString xs]
      let run ← IO.Process.output { cmd := "node", args }
      if run.exitCode != 0 then throw (IO.userError run.stderr)
      return ((run.stdout.splitOn "\n").filter (· != "")).map (fun (l : String) => l.splitOn ",")
    for preset in ["pbo", "faithful"] do
      let run ← IO.Process.output { cmd := "node", args := #[s!"{file}-{preset}.check.mjs"], cwd := dir }
      assertEq s!"{file}-{preset}: node" "" (if run.exitCode == 0 then "" else run.stderr)
      assertEq s!"{file}-{preset}: checks run, none failed" true
        ((run.stdout.splitOn " 0 failed").length > 1 && (run.stdout.splitOn " 0 passed").length == 1)
      for f in ["test1", "test2"] do
        let pbo ← count "Tests/SnapshotsPBOPure/legacy-backend/CaseNewtype.js" f
        let ours ← count s!"{dir}/{file}-{preset}.js" f
        assertEq s!"{file}-{preset}: {f} on every input" xs.length ours.length
        for (o, p) in ours.zip pbo do
          match o, p with
          | [x, r, n], [_, _, m] =>
            assertEq s!"{file}-{preset}: {f} {x}" (lean x.toInt!) r
            assertEq s!"{file}-{preset}: {f} {x} makes at most PBO's {m} comparisons" true
              (n.toNat! ≤ m.toNat!)
          | _, _ => assertEq s!"{file}-{preset}: a line of the counts" ["x", "r", "n"] o
      -- the value is the field itself: no `_1`, no record
      let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      assertEq s!"{file}-{preset}: no field read" 1 (js.splitOn "._1").length
  it "a match on float literals is one `===` per arm (needs node and leanscript)" do
    -- `CaseNumber`: `test1` tests `f == 1.0`, … with `if`s, `test2` matches `| 1.0 => …`, whose
    -- matcher decides `x = 1.0` (structural equality of floats).  Against a finite non-zero
    -- literal that is `x == 1.0` (`decide_float_eq_beq_of_finite`), so both are written as
    -- purescript-backend-optimizer writes its `test1` (`legacy-backend/CaseNumber.js`): on every
    -- input they make no more comparisons than PBO's and answer what Lean does.  The
    -- differential checks try every arm too (`1`, `2`, `3` among the `Float` samples).
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/caseNumber"
    IO.FS.createDirAll dir
    let file := "CaseNumber"
    let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    let xs : List Float := [-1.5, 0, 0.5, 1, 2, 2.25, 3, 4, 30]
    let lean : Float → String
      | 1.0 => "1"
      | 2.0 => "2"
      | 3.0 => "3"
      | _ => "catch"
    let count (js f : String) : IO (List (List String)) := do
      let args := #["scripts/count-comparisons.mjs", js, f, "0", toString xs]
      let run ← IO.Process.output { cmd := "node", args }
      if run.exitCode != 0 then throw (IO.userError run.stderr)
      return ((run.stdout.splitOn "\n").filter (· != "")).map (fun (l : String) => l.splitOn ",")
    let pbo ← count "Tests/SnapshotsPBOPure/legacy-backend/CaseNumber.js" "test1"
    for preset in ["pbo", "faithful"] do
      let run ← IO.Process.output { cmd := "node", args := #[s!"{file}-{preset}.check.mjs"], cwd := dir }
      assertEq s!"{file}-{preset}: node" "" (if run.exitCode == 0 then "" else run.stderr)
      assertEq s!"{file}-{preset}: checks run, none failed" true
        ((run.stdout.splitOn " 0 failed").length > 1 && (run.stdout.splitOn " 0 passed").length == 1)
      let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      assertEq s!"{file}-{preset}: test2 translated" true
        ((js.splitOn "export const test2 = ").length > 1)
      assertEq s!"{file}-{preset}: no bit pattern compared" 1 (js.splitOn "toBits").length
      for f in ["test1", "test2"] do
        let ours ← count s!"{dir}/{file}-{preset}.js" f
        assertEq s!"{file}-{preset}: {f} on every input" xs.length ours.length
        for ((o, p), x) in (ours.zip pbo).zip xs do
          match o, p with
          | [_, r, n], [_, _, m] =>
            assertEq s!"{file}-{preset}: {f} {x}" (lean x) r
            assertEq s!"{file}-{preset}: {f} {x} makes at most PBO's {m} comparisons" true
              (n.toNat! ≤ m.toNat!)
          | _, _ => assertEq s!"{file}-{preset}: a line of the counts" ["x", "r", "n"] o
  it "a panic! is thrown, with Lean's message, as a statement (needs node and leanscript)" do
    -- `CasePartial`: `| n => panic! ("mypanic " ++ toString n)`.  `panicCore` is the extern
    -- `lean_panic_fn`; the answer that is a panic becomes `throw new Error(msg)` in the
    -- conversion to JavaScript (`JsBlock.retOrRaise`), with the message Lean prints
    -- (`PANIC at test1 CasePartial:5:9: mypanic -7`, its literals merged into one); as
    -- purescript-backend-optimizer writes it (`legacy-backend/CasePartial.js`): on every input
    -- no more comparisons than PBO's.  The differential checks expect Lean's panics as throws of
    -- the same message (`LeanScript.Cli.panicsOf`).
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/casePartial"
    IO.FS.createDirAll dir
    let file := "CasePartial"
    let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    assertEq s!"{file}: no panic printed while checking" 1 (out.stderr.splitOn "PANIC").length
    let xs : List Int := [-7, -1, 0, 1, 2, 3, 4, 12]
    let lean (x : Int) : String :=
      match x with
      | 1 => "1"
      | 2 => "2"
      | 3 => "3"
      | n => s!"threw: PANIC at test1 CasePartial:5:9: mypanic {n}"
    let count (js : String) : IO (List (List String)) := do
      let args := #["scripts/count-comparisons.mjs", js, "test1", "0", toString xs]
      let run ← IO.Process.output { cmd := "node", args }
      if run.exitCode != 0 then throw (IO.userError run.stderr)
      return ((run.stdout.splitOn "\n").filter (· != "")).map (fun (l : String) => l.splitOn ",")
    let pbo ← count "Tests/SnapshotsPBOPure/legacy-backend/CasePartial.js"
    for preset in ["pbo", "faithful"] do
      let run ← IO.Process.output { cmd := "node", args := #[s!"{file}-{preset}.check.mjs"], cwd := dir }
      assertEq s!"{file}-{preset}: node" "" (if run.exitCode == 0 then "" else run.stderr)
      assertEq s!"{file}-{preset}: checks run, none failed" true
        ((run.stdout.splitOn " 0 failed").length > 1 && (run.stdout.splitOn " 0 passed").length == 1)
      let checks ← IO.FS.readFile s!"{dir}/{file}-{preset}.check.mjs"
      assertEq s!"{file}-{preset}: Lean's panics expected as throws" true
        ((checks.splitOn "threw: PANIC at test1 CasePartial:5:9: mypanic -7").length > 1)
      let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      assertEq s!"{file}-{preset}: thrown as a statement, the message one concatenation" true
        ((js.splitOn "throw new Error(\"PANIC at test1 CasePartial:5:9: mypanic \" + a);").length > 1)
      assertEq s!"{file}-{preset}: no call of the runtime" 1 (js.splitOn "import").length
      let ours ← count s!"{dir}/{file}-{preset}.js"
      assertEq s!"{file}-{preset}: test1 on every input" xs.length ours.length
      for (o, p) in ours.zip pbo do
        match o, p with
        | [x, r, n], [_, _, m] =>
          assertEq s!"{file}-{preset}: test1 {x}" (lean x.toInt!) r
          assertEq s!"{file}-{preset}: test1 {x} makes at most PBO's {m} comparisons" true
            (n.toNat! ≤ m.toNat!)
        | _, _ => assertEq s!"{file}-{preset}: a line of the counts" ["x", "r", "n"] o
  it "a test both arms of an if begin with is made first (needs node and leanscript)" do
    -- `CaseProduct`: `| ⟨1, 2, 3⟩ | ⟨_, 4, _⟩ | ⟨4, 5, 6⟩ | _`.  When the first field is not `1`,
    -- both arms of `if a == 4` begin with `if b == 4 then "2"`; that test is made first
    -- (`Term.shareTestWalk`), as purescript-backend-optimizer does
    -- (`legacy-backend/CaseProduct.js`): on every input no more comparisons than PBO's, fewer on
    -- some, and the answers of Lean.  `CaseRecord.test1` (`| {a := 1} | {b := 1} | {c := 1} |
    -- {a := 2, b := 2} | _`) becomes PBO's chain of tests the same way.
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/shareTest"
    IO.FS.createDirAll dir
    let count (js mode : String) (ts : List (List Int)) : IO (List (List String)) := do
      let args := #["scripts/count-comparisons.mjs", js, "test1", mode, toString ts]
      let run ← IO.Process.output { cmd := "node", args }
      if run.exitCode != 0 then throw (IO.userError run.stderr)
      return ((run.stdout.splitOn "\n").filter (· != "")).map (fun (l : String) => l.splitOn ",")
    let vs : List Int := [0, 1, 2, 3, 4, 5, 6]
    let tuples : List (List Int) := vs.flatMap fun a => vs.flatMap fun b => vs.map fun c => [a, b, c]
    let product (a b c : Int) : String :=
      match a, b, c with
      | 1, 2, 3 => "1"
      | _, 4, _ => "2"
      | 4, 5, 6 => "3"
      | _, _, _ => "catch"
    let record (a b c : Int) : String :=
      match a, b, c with
      | 1, _, _ => "0"
      | _, 1, _ => "1"
      | _, _, 1 => "2"
      | 2, 2, _ => "3"
      | _, _, _ => "catch"
    for (file, lean) in [("CaseProduct", product), ("CaseRecord", record)] do
      let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
      let out ← IO.Process.output { cmd := bin.toString, args }
      assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
      let pbo ← count s!"Tests/SnapshotsPBOPure/legacy-backend/{file}.js" "spread" tuples
      for preset in ["pbo", "faithful"] do
        let run ← IO.Process.output { cmd := "node", args := #[s!"{file}-{preset}.check.mjs"], cwd := dir }
        assertEq s!"{file}-{preset}: node" "" (if run.exitCode == 0 then "" else run.stderr)
        assertEq s!"{file}-{preset}: checks run, none failed" true
          ((run.stdout.splitOn " 0 failed").length > 1 && (run.stdout.splitOn " 0 passed").length == 1)
        let ours ← count s!"{dir}/{file}-{preset}.js" "record" tuples
        assertEq s!"{file}-{preset}: test1 on every input" tuples.length ours.length
        let mut total := 0
        let mut totalPbo := 0
        for ((o, p), t) in (ours.zip pbo).zip tuples do
          match o, p, t with
          | [x, r, n], [_, _, m], [a, b, c] =>
            assertEq s!"{file}-{preset}: test1 {x}" (lean a b c) r
            assertEq s!"{file}-{preset}: test1 {x} makes at most PBO's {m} comparisons" true
              (n.toNat! ≤ m.toNat!)
            total := total + n.toNat!
            totalPbo := totalPbo + m.toNat!
          | _, _, _ => assertEq s!"{file}-{preset}: a line of the counts" ["x", "r", "n"] o
        if file == "CaseProduct" then
          assertEq s!"{file}-{preset}: fewer comparisons than PBO in all ({total} < {totalPbo})"
            true (total < totalPbo)
  it "CaseRecord: every function gives Lean's answers, with at most PBO's comparisons (needs node and leanscript)" do
    -- `CaseRecord`: the six functions of `legacy-backend/CaseRecord.js`.  In `Test2.test2`, once
    -- `a.c == 2`, both arms of `if a.b == 1` test `d.e == 1 && d.f == 2`; `a.b` is tested in the
    -- answers instead (`Term.zipTestWalk`), so the test of `d` is written once, as
    -- purescript-backend-optimizer does.  On every input of a grid, each function gives Lean's
    -- answer and makes no more comparisons (equalities and orderings with a literal) than PBO's.
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/caseRecord"
    IO.FS.createDirAll dir
    let file := "CaseRecord"
    let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    let count (js fn mode tuples : String) : IO (List (List String)) := do
      let args := #["scripts/count-comparisons.mjs", js, fn, mode, tuples]
      let run ← IO.Process.output { cmd := "node", args }
      if run.exitCode != 0 then throw (IO.userError run.stderr)
      return ((run.stdout.splitOn "\n").filter (· != "")).map (fun (l : String) => l.splitOn ",")
    let js (xs : List Int) : String := "[" ++ ",".intercalate (xs.map toString) ++ "]"
    let vs : List Int := [0, 1, 2, 3]
    let ws : List Int := [-1, 0, 1, 2, 3]
    let abc : List (List Int) := vs.flatMap fun a => vs.flatMap fun b => vs.map fun c => [a, b, c]
    let ab : List (List Int) := ws.flatMap fun a => ws.map fun b => [a, b]
    let bcef : List (List Int) := vs.flatMap fun b => vs.flatMap fun c =>
      vs.flatMap fun e => vs.map fun f => [b, c, e, f]
    let flatJson (ts : List (List Int)) : String := "[" ++ ",".intercalate (ts.map js) ++ "]"
    let nestedJson (ts : List (List Int)) : String :=
      "[" ++ ",".intercalate (ts.map fun (t : List Int) => s!"[{js (t.take 2)},{js (t.drop 2)}]") ++ "]"
    let test1 : List Int → String
      | [1, _, _] => "0" | [_, 1, _] => "1" | [_, _, 1] => "2" | [2, 2, _] => "3" | _ => "catch"
    let test2 : List Int → String
      | [1, 2, 1, 2] => "1" | [_, 2, 1, 2] => "2" | [1, 2, _, _] => "3" | _ => "4"
    let test3 : List Int → String
      | [a, b] => toString (if a > 0 then a else if b > 1 then b else 3) | _ => "?"
    let test5 : List Int → String
      | [a, b] => toString (if a > 0 then a else if b > 0 then b else 0) | _ => "?"
    let cases : List (String × String × List (List Int) × String × String × (List Int → String)) :=
      [("test1", "test1", abc, flatJson abc, flatJson abc, test1),
       ("Test2$test2", "test2", bcef, nestedJson bcef, nestedJson bcef, test2),
       ("test3", "test3", ab, flatJson ab, flatJson ab, test3),
       ("test4", "test4", ab, flatJson ab, flatJson ab, test3),
       ("test5", "test5", ab, flatJson ab, flatJson ab, test5),
       ("test6", "test6", ab, flatJson ab, flatJson ab, test5)]
    for preset in ["pbo", "faithful"] do
      let run ← IO.Process.output { cmd := "node", args := #[s!"{file}-{preset}.check.mjs"], cwd := dir }
      assertEq s!"{file}-{preset}: node" "" (if run.exitCode == 0 then "" else run.stderr)
      let src ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      let lit := if preset == "pbo" then "" else "n"
      assertEq s!"{file}-{preset}: the test of `d` written once in Test2.test2" 2
        (src.splitOn s!"x._2._1 === 1{lit} && x._2._2 === 2{lit}").length
      for (ours, theirs, ts, ourJson, pboJson, lean) in cases do
        let pbo ← count "Tests/SnapshotsPBOPure/legacy-backend/CaseRecord.js" theirs "spread" pboJson
        let got ← count s!"{dir}/{file}-{preset}.js" ours "record" ourJson
        assertEq s!"{file}-{preset}: {ours} on every input" ts.length got.length
        for ((o, p), t) in (got.zip pbo).zip ts do
          match o, p with
          | [x, r, n], [_, r', m] =>
            assertEq s!"{file}-{preset}: {ours} {x}" (lean t) r
            assertEq s!"{file}-{preset}: PBO's {theirs} {x}" (lean t) r'
            assertEq s!"{file}-{preset}: {ours} {x} makes at most PBO's {m} comparisons" true
              (n.toNat! ≤ m.toNat!)
          | _, _ => assertEq s!"{file}-{preset}: a line of the counts" ["x", "r", "n"] o
  it "a join point taking apart the constructor its jumps pass is written at the jumps (needs node and leanscript)" do
    -- `CaseLeafTco`: `match arr[0]?, arr.back? with …` builds `some (arr[0])` or `none` into a
    -- join point that takes it apart at once; the arm of each constructor is written at its jump
    -- (`JoinInl`), so no option is built.  `test1FuelCalled` is `test1Fuel 1000000`: it is
    -- written as that call (`literalCalls`).  The differential checks compare every answer with
    -- Lean's.
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/joinInl"
    IO.FS.createDirAll dir
    let file := "CaseLeafTco"
    let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    for preset in ["pbo", "faithful"] do
      let run ← IO.Process.output { cmd := "node", args := #[s!"{file}-{preset}.check.mjs"], cwd := dir }
      assertEq s!"{file}-{preset}: node" "" (if run.exitCode == 0 then "" else run.stderr)
      assertEq s!"{file}-{preset}: no check failed" true
        ((run.stdout.splitOn " 0 failed").length > 1 && (run.stdout.splitOn "FAIL").length == 1)
      let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      assertEq s!"{file}-{preset}: no option built" 1 (js.splitOn "tag: 1").length
      assertEq s!"{file}-{preset}: no join point" 1 (js.splitOn "let x$").length
      assertEq s!"{file}-{preset}: test1FuelCalled calls test1Fuel" true
        ((js.splitOn "export const test1FuelCalled = (b, arr) => test1Fuel(1000000").length > 1)
  it "a conversion every path makes is made once, in front (needs node and leanscript)" do
    -- `CaseNamed`: every arm of `test1` converts `x` to a string, and the last arm of `test2`
    -- converts `a` twice (`toString a ++ toString a`); each conversion is made once, before the
    -- tests that need it (`Term.hoistWalk`).  Every arm answers what Lean does (the generated
    -- checks only try inputs that reach the last arm).
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/hoist"
    IO.FS.createDirAll dir
    let file := "CaseNamed"
    let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    let test1 (x : Int) : String :=
      match x with
      | 1 => toString x ++ toString x ++ toString x
      | 2 => toString x
      | n => "any: " ++ toString n ++ toString n ++ toString n
    let test2 (a b c : Int) : String :=
      match a, b, c with
      | 1, a, b => toString a ++ toString b ++ "1"
      | a, 1, b => toString a ++ toString b ++ "1"
      | a, b, 1 => toString a ++ toString b ++ "1"
      | a, b, c => toString a ++ toString a ++ toString b ++ toString b ++ toString c ++ toString c
    let xs : List Int := [1, 2, 3, -4]
    let triples : List (Int × Int × Int) :=
      [(1, 7, -8), (7, 1, -8), (7, -8, 1), (7, -8, 9), (1, 1, 1), (2, 1, 1)]
    for preset in ["pbo", "faithful"] do
      let run ← IO.Process.output { cmd := "node", args := #[s!"{file}-{preset}.check.mjs"], cwd := dir }
      assertEq s!"{file}-{preset}: node" "" (if run.exitCode == 0 then "" else run.stderr)
      assertEq s!"{file}-{preset}: no check failed" true
        ((run.stdout.splitOn " 0 failed").length > 1 && (run.stdout.splitOn "FAIL").length == 1)
      let lit (n : Int) : String := if preset == "faithful" then s!"{n}n" else toString n
      let calls := (xs.map fun x => s!"M.test1({lit x})") ++
        (triples.map fun (a, b, c) => s!"M.test2(\{ _1: {lit a}, _2: {lit b}, _3: {lit c} })")
      let script := s!"import * as M from {(s!"file://{dir}/{file}-{preset}.js").quote};\n" ++
        s!"console.log(JSON.stringify([{", ".intercalate calls}]));\n"
      let res ← IO.Process.output { cmd := "node", args := #["--input-type=module", "-e", script] }
      assertEq s!"{file}-{preset}: node (every arm)" "" (if res.exitCode == 0 then "" else res.stderr)
      let expected := (xs.map test1) ++ (triples.map fun (a, b, c) => test2 a b c)
      let shown := "[" ++ ",".intercalate (expected.map fun (s : String) => s.quote) ++ "]"
      assertEq s!"{file}-{preset}: every arm answers what Lean does" shown res.stdout.trimAscii.toString
      let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      let body (f : String) : String :=
        ((js.splitOn s!"export const {f} ").getD 1 "").splitOn "export const" |>.headD ""
      -- `test1`: `String(x)` once, before the tests
      assertEq s!"{file}-{preset}: test1 converts x once" 2 ((body "test1").splitOn "String(").length
      assertEq s!"{file}-{preset}: test1 converts x first" true
        (((body "test1").splitOn "\n").getD 1 "" |>.trimAscii.toString |>.startsWith "const x$1 = String(x);")
      -- `test2`: the last arm reads each conversion from a constant, and converts nothing
      let lastReturn := ((body "test2").splitOn "return ").getLast!
      assertEq s!"{file}-{preset}: test2's last arm converts nothing" 1 (lastReturn.splitOn "String(").length
      assertEq s!"{file}-{preset}: test2's last arm adds no field" 1 (lastReturn.splitOn "+ f$").length
  it "versions of local functions and owning closures update in place, never visibly (needs node and leanscript)" do
    -- `LocalFnInPlace`: local functions get one constant per version (`k_mut…` owns its array
    -- parameter), and a recursion with an array accumulator builds owning closures;
    -- `OwnershipAliasing`: programs where an update in place would be visible.  Their
    -- differential checks compare every answer with Lean's.
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/ownership"
    IO.FS.createDirAll dir
    for file in ["LocalFnInPlace", "OwnershipAliasing"] do
      let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"Tests/SnapshotsMy/{file}.lean"]
      let out ← IO.Process.output { cmd := bin.toString, args }
      assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
      for preset in ["pbo", "faithful"] do
        let run ← IO.Process.output { cmd := "node", args := #[s!"{file}-{preset}.check.mjs"], cwd := dir }
        assertEq s!"{file}-{preset}: node" "" (if run.exitCode == 0 then "" else run.stderr)
        assertEq s!"{file}-{preset}: no check failed" true
          ((run.stdout.splitOn " 0 failed").length > 1 && (run.stdout.splitOn "FAIL").length == 1)
    let js ← IO.FS.readFile s!"{dir}/LocalFnInPlace-pbo.js"
    assertEq "a version of a local function owning its array" true ((js.splitOn "const k_mut").length > 1)
    -- `test5`: the recursion on an array built here copies nothing
    let test5 := ((js.splitOn "export const test5 ").getD 1 "").splitOn "export const" |>.headD ""
    assertEq "test5 updates in place" true ((test5.splitOn "_mutable(").length > 1)
    assertEq "test5 never copies" 1 ((test5.splitOn "_immutable(").length + (test5.splitOn "[...").length - 1)
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
      ["array__lean_array_append_immutable", "array__lean_array_pop_immutable",
       "array__lean_array_push_immutable", "bigint_nat__lean_array_fset_immutable", "bigint_nat__lean_array_fswap_immutable",
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
    assertEq "append" "array__lean_array_append_immutable MoreJs.Effectfulness.pure -> array__lean_array_append_mutable"
      (pairName (.array__lean_array_append_immutable (.generic tN)))
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
      ("uint53__lean_array_fswap", "1, 2", "new Int32Array([1, 2, 3])"),
      ("array__lean_array_append", "[4, 5]", "[1, 2, 3]")]
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
  it "List.append on cons cells is written into the module, and answers what runtime.js does (needs node)" do
    let n := "consList__lean_list_append"
    assertEq "defined in the module" true (isLocalHelper n)
    let src ← IO.FS.readFile "runtime.js"
    assertEq "also in runtime.js" true ((src.splitOn s!"export const {n} =").length > 1)
    let cwd ← IO.currentDir
    let script := s!"import \{ {n} as rt, consList__of_array, consList__to_array } from {(s!"file://{cwd}/runtime.js").quote};\n" ++
      (localHelper? n).getD "" ++
      "const cases = [[[], []], [[1], []], [[], [2]], [[1, 2, 3], [4, 5]], [[7], [8]]];\n" ++
      "for (const [a, b] of cases) {\n" ++
      "  const xs = consList__of_array(a), ys = consList__of_array(b);\n" ++
      "  const l = consList__lean_list_append(xs, ys), r = rt(xs, ys);\n" ++
      "  console.log(consList__to_array(l).join(), consList__to_array(r).join(),\n" ++
      "    consList__to_array(xs).join() === a.join(), b.length === 0 || a.length === 0 || l._2 !== xs._2);\n" ++
      "}\n" ++
      "let big = consList__of_array([]);\n" ++
      "for (let i = 0; i < 200000; i++) big = { tag: 1, _1: i, _2: big };\n" ++
      "console.log(consList__to_array(consList__lean_list_append(big, consList__of_array([1]))).length);\n"
    let out ← try
        some <$> IO.Process.output { cmd := "node", args := #["--input-type=module", "-e", script] }
      catch _ => pure none
    match out with
    | none => pure ()  -- no `node`: nothing to run
    | some out =>
      assertEq "node" "" (if out.exitCode == 0 then "" else out.stderr)
      assertEq "output" ["  true true", "1 1 true true", "2 2 true true",
        "1,2,3,4,5 1,2,3,4,5 true true", "7,8 7,8 true true", "200001"]
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

namespace CaseRBT

/-! `Tests/SnapshotsPBOPure/CaseRedBlackTree.lean`, the reference the generated code is compared
with (`panic!` answers `default`, as it does in Lean: the unmatched trees answer `default`). -/

inductive Color where
  | Red
  | Black

inductive Tree where
  | Leaf
  | Node (color : Color) (l : Tree) (val : Nat) (r : Tree)

structure Result where
  i : Nat
  a : Tree
  x : Nat
  b : Tree
  y : Nat
  c : Tree
  z : Nat
  d : Tree

def test1 (t : Tree) : Result :=
  match t with
  | .Node .Black (.Node .Red (.Node .Red a x b) y c) z d => { i := 1, a, x, b, y, c, z, d }
  | .Node .Black (.Node .Red a x (.Node .Red b y c)) z d => { i := 2, a, x, b, y, c, z, d }
  | .Node .Black a x (.Node .Red (.Node .Red b y c) z d) => { i := 3, a, x, b, y, c, z, d }
  | .Node .Black a x (.Node .Red b y (.Node .Red c z d)) => { i := 4, a, x, b, y, c, z, d }
  | _ => { i := 0, a := .Leaf, x := 0, b := .Leaf, y := 0, c := .Leaf, z := 0, d := .Leaf }

/-- The shapes of the trees of depth at most `n`, with every value `0`. -/
def shapes : Nat → List Tree
  | 0 => [.Leaf]
  | n + 1 =>
    let sub := shapes n
    .Leaf :: [Color.Red, Color.Black].flatMap fun c =>
      sub.flatMap fun l => sub.map fun r => .Node c l 0 r

/-- The tree with its values numbered in order, from `k`; and the next number. -/
def number : Tree → Nat → Tree × Nat
  | .Leaf, k => (.Leaf, k)
  | .Node c l _ r, k =>
    let (l', k) := number l k
    let (r', k') := number r (k + 1)
    (.Node c l' k r', k')

def Tree.show : Tree → String
  | .Leaf => "L"
  | .Node c l v r => s!"N({match c with | .Red => "R" | .Black => "B"},{l.show},{v},{r.show})"

def Tree.json : Tree → String
  | .Leaf => "null"
  | .Node c l v r =>
    s!"[\"{match c with | .Red => "R" | .Black => "B"}\",{l.json},{v},{r.json}]"

def Result.show (r : Result) : String :=
  s!"{r.i};{r.a.show};{r.x};{r.b.show};{r.y};{r.c.show};{r.z};{r.d.show}"

end CaseRBT

/-- `CaseRedBlackTree`: the balancing patterns of a red-black tree. -/
def caseRedBlackTreeSpec : Spec := describe "CaseRedBlackTree" do
  it "every tree of depth ≤ 3 gets Lean's answer, with at most PBO's tests (needs node and leanscript)" do
    -- Lean's match compiler copies the tests of the right subtree (patterns 3 and 4) into every
    -- branch where patterns 1 and 2 fail, and rebuilds the left subtree from its fields
    -- (`Node Red l' x' r'`) instead of naming it.  The rebuilt subtree is the value taken apart
    -- (`knownCtorLvl?`, a boolean literal included when an enclosing `if` tested that field),
    -- so the copies are the same statements and are written once (`JsBlock.shareTails`), as
    -- purescript-backend-optimizer does (`legacy-backend/CaseRedBlackTree.js`).  On every tree
    -- of depth at most 3, `test1` gives Lean's answer (PBO's too, or PBO throws where Lean
    -- answers `default`), and reads no more tags and colours than PBO.
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/caseRedBlackTree"
    IO.FS.createDirAll dir
    let file := "CaseRedBlackTree"
    let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    let trees := (CaseRBT.shapes 3).map fun t => (CaseRBT.number t 1).1
    let json := "[" ++ ",".intercalate (trees.map CaseRBT.Tree.json) ++ "]"
    for preset in ["pbo", "faithful"] do
      let src ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      -- the default answer (a tree without a match) is written once, and so is each pattern
      let lit := if preset == "pbo" then "" else "n"
      assertEq s!"{file}-{preset}: one default answer" 2 (src.splitOn s!"_1: 0{lit},").length
      for i in [1, 2, 3, 4] do
        assertEq s!"{file}-{preset}: pattern {i} written once" 2
          (src.splitOn s!"_1: {i}{lit},").length
      let run ← IO.Process.output { cmd := "node", args := #["scripts/rbt-compare.mjs",
        s!"{dir}/{file}-{preset}.js", s!"Tests/SnapshotsPBOPure/legacy-backend/{file}.js", json] }
      assertEq s!"{file}-{preset}: node" "" (if run.exitCode == 0 then "" else run.stderr)
      let lines := (run.stdout.splitOn "\n").filter (· != "")
      assertEq s!"{file}-{preset}: every tree" trees.length lines.length
      let mut total := 0
      let mut totalPbo := 0
      for (t, l) in trees.zip lines do
        let expected := (CaseRBT.test1 t).show
        match l.splitOn "|" with
        | [o, p, n, m] =>
          assertEq s!"{file}-{preset}: test1 {t.show}" expected o
          assertEq s!"{file}-{preset}: PBO's test1 {t.show}" true
            (p == expected || ((CaseRBT.test1 t).i == 0 && p.startsWith "threw:"))
          assertEq s!"{file}-{preset}: test1 {t.show} makes at most PBO's {m} tests" true
            (n.toNat! ≤ m.toNat!)
          total := total + n.toNat!
          totalPbo := totalPbo + m.toNat!
        | _ => assertEq s!"{file}-{preset}: a line of the results" "ours|pbo|n|m" l
      assertEq s!"{file}-{preset}: at most PBO's tests in all ({total} ≤ {totalPbo})" true
        (total ≤ totalPbo)

/-- `CaseString`: a `match` on string literals. -/
def caseStringSpec : Spec := describe "CaseString" do
  it "test1 gives Lean's answers, with at most PBO's comparisons (needs node and leanscript)" do
    -- `| "foo" => "1" | "bar" => "2" | "" => "3" | _ => "catch"`: a chain of `===` tests with a
    -- string literal, in the order of the patterns, as purescript-backend-optimizer writes it
    -- (`legacy-backend/CaseString.js`).  On every input, `test1` gives Lean's answer (PBO's
    -- too) and makes no more comparisons than PBO's.  The differential checks call it on the
    -- literals of the patterns too (`LeanScript.Cli.stringLitsOf`), so each arm is taken.
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/caseString"
    IO.FS.createDirAll dir
    let file := "CaseString"
    let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    let lean (x : String) : String :=
      match x with
      | "foo" => "1"
      | "bar" => "2"
      | "" => "3"
      | _ => "catch"
    let xs : List String := ["foo", "bar", "", "a", "fo", "foobar", "Foo", "catch", "1", "héllo"]
    let json := "[" ++ ",".intercalate (xs.map fun x => "\"" ++ x ++ "\"") ++ "]"
    let count (js : String) : IO (List (List String)) := do
      let args := #["scripts/count-comparisons.mjs", js, "test1", "0", json]
      let run ← IO.Process.output { cmd := "node", args }
      if run.exitCode != 0 then throw (IO.userError run.stderr)
      return ((run.stdout.splitOn "\n").filter (· != "")).map (fun (l : String) => l.splitOn ",")
    let pbo ← count s!"Tests/SnapshotsPBOPure/legacy-backend/{file}.js"
    assertEq s!"{file}: PBO's test1 on every input" xs.length pbo.length
    for preset in ["pbo", "faithful"] do
      let run ← IO.Process.output { cmd := "node", args := #[s!"{file}-{preset}.check.mjs"], cwd := dir }
      assertEq s!"{file}-{preset}: node" "" (if run.exitCode == 0 then "" else run.stderr)
      assertEq s!"{file}-{preset}: checks run, none failed" true
        ((run.stdout.splitOn " 0 failed").length > 1 && (run.stdout.splitOn " 0 passed").length == 1)
      let checks ← IO.FS.readFile s!"{dir}/{file}-{preset}.check.mjs"
      for lit in ["foo", "bar"] do
        assertEq s!"{file}-{preset}: the checks take the arm of {lit}" true
          ((checks.splitOn s!"M.test1(\"{lit}\")").length > 1)
      let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      assertEq s!"{file}-{preset}: no call of the runtime" 1 (js.splitOn "import").length
      for lit in ["foo", "bar", ""] do
        assertEq s!"{file}-{preset}: one test of \"{lit}\"" 2
          (js.splitOn s!"x === \"{lit}\"").length
      let ours ← count s!"{dir}/{file}-{preset}.js"
      assertEq s!"{file}-{preset}: test1 on every input" xs.length ours.length
      for ((o, p), x) in (ours.zip pbo).zip xs do
        match o, p with
        | [_, r, n], [_, q, m] =>
          assertEq s!"{file}-{preset}: test1 \"{x}\"" (lean x) r
          assertEq s!"{file}-{preset}: PBO's test1 \"{x}\"" (lean x) q
          assertEq s!"{file}-{preset}: test1 \"{x}\" makes at most PBO's {m} comparisons" true
            (n.toNat! ≤ m.toNat!)
        | _, _ => assertEq s!"{file}-{preset}: a line of the counts" ["x", "r", "n"] o

/-- `CaseSum`: a `match` on a sum type with a `Nat` field, with literal patterns on the field. -/
def caseSumSpec : Spec := describe "CaseSum" do
  it "test1 gives Lean's answers, with at most PBO's comparisons and reads (needs node and leanscript)" do
    -- `| .L 1 => "1" | .L 2 => "2" | .L _ => "3" | .R _ => "4"`: one test of the tag, then the
    -- tests of the field in the order of the patterns, as purescript-backend-optimizer writes it
    -- (`legacy-backend/CaseSum.js`), but without PBO's second tag test (`R` is the only
    -- constructor left) nor its `throw`, and reading the field once (`const { _1: f$1 } = v`).
    -- On every input, `test1` gives Lean's answer (PBO's too) and makes no more comparisons and
    -- no more reads of the value than PBO's.  The differential checks take the field among the
    -- literals of the patterns too (`LeanScript.Cli.natLitsOf`), so each arm is taken.
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/caseSum"
    IO.FS.createDirAll dir
    let file := "CaseSum"
    let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    let lean (c : Bool) (n : Nat) : String :=
      match c, n with
      | true, 1 => "1"
      | true, 2 => "2"
      | true, _ => "3"
      | false, _ => "4"
    let xs : List (Bool × Nat) :=
      [0, 1, 2, 3, 13, 1000].flatMap fun n => [(true, n), (false, n)]
    let json := "[" ++ ",".intercalate (xs.map fun ((c, n) : Bool × Nat) =>
      s!"[\"{cond c "L" "R"}\",{n}]") ++ "]"
    for preset in ["pbo", "faithful"] do
      let run ← IO.Process.output { cmd := "node", args := #[s!"{file}-{preset}.check.mjs"], cwd := dir }
      assertEq s!"{file}-{preset}: node" "" (if run.exitCode == 0 then "" else run.stderr)
      assertEq s!"{file}-{preset}: checks run, none failed" true
        ((run.stdout.splitOn " 0 failed").length > 1 && (run.stdout.splitOn " 0 passed").length == 1)
      let lit := if preset == "pbo" then "" else "n"
      let checks ← IO.FS.readFile s!"{dir}/{file}-{preset}.check.mjs"
      assertEq s!"{file}-{preset}: the checks take the arm of `.L 2`" true
        ((checks.splitOn s!"M.test1(\{ tag: 0, _1: 2{lit} })").length > 1)
      let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      assertEq s!"{file}-{preset}: no call of the runtime" 1 (js.splitOn "import").length
      assertEq s!"{file}-{preset}: one test of the tag" 2 (js.splitOn ".tag === ").length
      assertEq s!"{file}-{preset}: no throw" 1 (js.splitOn "throw").length
      for k in [1, 2] do
        assertEq s!"{file}-{preset}: one test of {k}" 2 (js.splitOn s!" === {k}{lit}").length
      let run ← IO.Process.output { cmd := "node", args := #["scripts/sum-compare.mjs",
        s!"{dir}/{file}-{preset}.js", s!"Tests/SnapshotsPBOPure/legacy-backend/{file}.js", json] }
      assertEq s!"{file}-{preset}: sum-compare" "" (if run.exitCode == 0 then "" else run.stderr)
      let lines := (run.stdout.splitOn "\n").filter (· != "")
      assertEq s!"{file}-{preset}: test1 on every input" xs.length lines.length
      for ((c, n), l) in xs.zip lines do
        let v := s!"{cond c "L" "R"} {n}"
        match l.splitOn "|" with
        | [o, p, oc, pc, or_, pr] =>
          assertEq s!"{file}-{preset}: test1 ({v})" (lean c n) o
          assertEq s!"{file}-{preset}: PBO's test1 ({v})" (lean c n) p
          assertEq s!"{file}-{preset}: test1 ({v}) makes at most PBO's {pc} comparisons" true
            (oc.toNat! ≤ pc.toNat!)
          assertEq s!"{file}-{preset}: test1 ({v}) makes at most PBO's {pr} reads" true
            (or_.toNat! ≤ pr.toNat!)
          -- `R n`: one tag test and one read (PBO: two of each)
          if !c then
            assertEq s!"{file}-{preset}: test1 ({v}) makes one comparison" "1" oc
        | _ => assertEq s!"{file}-{preset}: a line of the results" "o|p|oc|pc|or|pr" l

/-- `DefaultRulesFunction01`: `flip`, `Function.const`, `<|` and `|>` on polymorphic functions,
    and on rank-2 parameters `f g : F` for `F := ∀ {α β γ : Type}, α → β → γ`. -/
def defaultRulesFunctionSpec : Spec := describe "DefaultRulesFunction01" do
  it "every function is translated, to one call with flip/const gone (needs node and leanscript)" do
    -- purescript-backend-optimizer (`legacy-backend/DefaultRulesFunction01.js`) writes each
    -- function as one curried call (`(f) => (g) => (_unit) => f(1)(g("foo")())`).  Ours are
    -- the same calls, uncurried: the type parameters are erased (read at the stand-in `Nat`), and
    -- a rank-2 parameter is read at its one instance.  (`test1`–`test3` answer a `Nat` here: with
    -- a result of `Unit` they would do nothing, and are skipped, `oneValueResultSpec`.)
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/defaultRulesFunction"
    IO.FS.createDirAll dir
    let file := "DefaultRulesFunction01"
    let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    for preset in ["pbo", "faithful"] do
      -- the literals are `BigInt`s at the preset `faithful`
      let n := if preset == "pbo" then "" else "n"
      let expected : List String := [
        s!"export const test1 = (f, g, a) => f(1{n}, g(\"foo\", a));",
        s!"export const test2 = (f, g, a) => f(1{n}, g(\"foo\", a));",
        s!"export const test3 = (f, g, a) => f(g(1{n}, 2{n}), 3{n});",
        "export const test4 = (f, b, a) => f(b, a);",
        "export const test5 = (a, a1) => a;",
        "export const test6 = (a) => a;"]
      let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      assertEq s!"{file}-{preset}: every function translated" 1 (js.splitOn "not translated").length
      assertEq s!"{file}-{preset}: no call of the runtime" 1 (js.splitOn "import").length
      for l in expected do
        assertEq s!"{file}-{preset}: {l}" true ((js.splitOn l).length == 2)
      -- its three type parameters are read at the stand-in `Nat`
      let nat := if preset == "pbo" then "uint53(number)" else "nat(bigint)"
      assertEq s!"{file}-{preset}: test4 is read at the stand-in Nat" true
        ((js.splitOn s!" * `test4`\n * @param \{({nat}, {nat}) => {nat}} f").length == 2)
      let run ← IO.Process.output { cmd := "node", args := #[s!"{file}-{preset}.check.mjs"], cwd := dir }
      assertEq s!"{file}-{preset}: node" "" (if run.exitCode == 0 then "" else run.stderr)
      assertEq s!"{file}-{preset}: checks run, none failed" true
        ((run.stdout.splitOn " 0 failed").length > 1 && (run.stdout.splitOn " 0 passed").length == 1)
      -- the rank-2 parameters called on recording functions: the calls Lean makes
      let script := s!"import * as M from '{dir}/{file}-{preset}.js';
const f = (x, y) => 'f(' + x + ',' + y + ')', g = (x, y) => 'g(' + x + ',' + y + ')';
console.log([M.test1(f, g, 'u'), M.test2(f, g, 'u'), M.test3(f, g, 'u'), M.test4(f, 'b', 'a'),
  M.test5('a', 'x'), M.test6('a')].join('|'));"
      let run ← IO.Process.output { cmd := "node", args := #["--input-type=module", "-e", script] }
      assertEq s!"{file}-{preset}: node -e" "" (if run.exitCode == 0 then "" else run.stderr)
      assertEq s!"{file}-{preset}: the calls"
        "f(1,g(foo,u))|f(1,g(foo,u))|f(g(1,2),3)|f(b,a)|a|a"
        run.stdout.trimAscii.toString

/-- A function whose result has one value (`Unit`, `Unit × PUnit`) does nothing in a pure
    language: the `leanscript` tool skips it silently (it is neither exported nor listed as not
    translated), even when it is total and terminating, and translates the rest of the file. -/
def oneValueResultSpec : Spec := describe "results of one value" do
  it "a function answering a Unit is skipped (needs leanscript)" do
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let dir := s!"{← IO.currentDir}/.lake/build/oneValueResult"
    IO.FS.createDirAll dir
    let file := "OneValueResult"
    IO.FS.writeFile s!"{dir}/{file}.lean" "def F := ∀ {α β γ : Type}, α → β → γ

def unitFn (f : F) (g : F) (a : Unit) : Unit :=
  f 1 <| (g \"foo\" a : Unit)

def unitThunk (f : F) (g : F) : Unit → Unit :=
  fun _ => flip f 3 $ (flip g 2 1 : Int)

def unitPair : Nat → Unit × PUnit := fun _ => ((), ())

def natFn (f : F) (g : F) (a : Nat) : Nat :=
  f 1 <| (g \"foo\" a : Nat)
"
    let args := #["--quiet", s!"--out-dir={dir}", s!"{dir}/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    for preset in ["pbo", "faithful"] do
      let n := if preset == "pbo" then "" else "n"
      let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      assertEq s!"{file}-{preset}: natFn translated" true
        ((js.splitOn s!"export const natFn = (f, g, a) => f(1{n}, g(\"foo\", a));").length == 2)
      assertEq s!"{file}-{preset}: nothing listed as not translated" 1
        (js.splitOn "not translated").length
      for f in ["unitFn", "unitThunk", "unitPair"] do
        assertEq s!"{file}-{preset}: {f} skipped" 1 (js.splitOn f).length

def defaultRulesFunctorSpec : Spec := describe "DefaultRulesFunctor01" do
  it "every function is one test of the option, with no closure (needs node and leanscript)" do
    -- purescript-backend-optimizer (`legacy-backend/DefaultRulesFunctor01.js`) writes each
    -- function as one test of the option and a new option.  Ours: the same test; `test2`
    -- (`Option Unit`, its `Unit` field erased) is a boolean, and `test5` answers its argument
    -- itself when it is a `some` (the join point is written at its jumps, `Term.joinCtor`, and
    -- the call of `const` opened, `Term.openCall`).
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/defaultRulesFunctor"
    IO.FS.createDirAll dir
    let file := "DefaultRulesFunctor01"
    let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    for preset in ["pbo", "faithful"] do
      let n := if preset == "pbo" then "" else "n"
      let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      assertEq s!"{file}-{preset}: every function translated" 1 (js.splitOn "not translated").length
      assertEq s!"{file}-{preset}: no closure" 1 (js.splitOn "=> f").length
      assertEq s!"{file}-{preset}: test2 is a boolean" true
        ((js.splitOn "export const test2 = (mb) => mb.tag !== 0;").length > 1)
      assertEq s!"{file}-{preset}: test5 answers its argument" true
        ((js.splitOn "  return mb;\n};").length > 1)
      let script := s!"import * as M from '{dir}/{file}-{preset}.js';
const none = \{ tag: 0 }, some = (x) => (\{ tag: 1, _1: x });
const show = (o) => typeof o === 'boolean' ? String(o) : o.tag === 0 ? 'none' : 'some ' + o._1;
console.log([M.test1(none), M.test1(some(-3{n})), M.test2(none), M.test2(some('a')),
  M.test3(none), M.test3(some('a')), M.test4(none), M.test4(some('a')),
  M.test5(none), M.test5(some('a'))].map(show).join('|'));"
      let run ← IO.Process.output { cmd := "node", args := #["--input-type=module", "-e", script] }
      assertEq s!"{file}-{preset}: node -e" "" (if run.exitCode == 0 then "" else run.stderr)
      assertEq s!"{file}-{preset}: the answers"
        "none|some -3|false|true|none|some 42|none|some 42|none|some a"
        run.stdout.trimAscii.toString

def defaultRulesMonoidSpec : Spec := describe "DefaultRulesMonoid01" do
  it "both functions translated, one test and no closure (needs node and leanscript)" do
    -- purescript-backend-optimizer (`legacy-backend/DefaultRulesMonoid01.js`): `test1` is one
    -- test answering `[1, 2, 3]` or `[]`; `test2` calls `f` first and answers a closure.  Ours:
    -- `test1` the same test; `test2` takes both arguments at once and calls `f` only when it is
    -- needed (no closure is built).
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/defaultRulesMonoid"
    IO.FS.createDirAll dir
    let file := "DefaultRulesMonoid01"
    let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    for preset in ["pbo", "faithful"] do
      let n := if preset == "pbo" then "" else "n"
      let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      assertEq s!"{file}-{preset}: every function translated" 1 (js.splitOn "not translated").length
      assertEq s!"{file}-{preset}: test1 is one test" true
        ((js.splitOn s!"export const test1 = (a) => (a ? [1{n}, 2{n}, 3{n}] : []);").length > 1)
      assertEq s!"{file}-{preset}: test2 takes both arguments" true
        ((js.splitOn "export const test2 = (f, a) => {").length > 1)
      let script := s!"import * as M from '{dir}/{file}-{preset}.js';
let calls = 0;
const f = (xs) => \{ calls++; return xs.map((x) => x + x); };
console.log([M.test1(true), M.test1(false), M.test2(f, true), M.test2(f, false)]
  .map((xs) => '[' + xs.join(',') + ']').join('|') + '|' + calls);"
      let run ← IO.Process.output { cmd := "node", args := #["--input-type=module", "-e", script] }
      assertEq s!"{file}-{preset}: node -e" "" (if run.exitCode == 0 then "" else run.stderr)
      assertEq s!"{file}-{preset}: the answers" "[1,2,3]|[]|[2,4,6]|[]|1"
        run.stdout.trimAscii.toString

def defaultRulesSemigroupSpec : Spec := describe "DefaultRulesSemigroup01" do
  it "the code and the names of purescript-backend-optimizer, uncurried (needs node and leanscript)" do
    -- purescript-backend-optimizer (`legacy-backend/DefaultRulesSemigroup01.js`):
    -- `test1 = (f) => (g) => (x) => f(x) + g(x)` and `test2` binding `fx = f(x)`, `gx = g(x)`
    -- once each.  Ours: the same bodies and names, with all the parameters at once (the
    -- parameter `x` is the binder of the instance's `fun`, the repeated calls are shared by
    -- `Term.optimize`, and a call of a parameter on a parameter is named after them).
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/defaultRulesSemigroup"
    IO.FS.createDirAll dir
    let file := "DefaultRulesSemigroup01"
    let args := #["--quiet", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    for preset in ["pbo", "faithful"] do
      let n := if preset == "pbo" then "" else "n"
      let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      assertEq s!"{file}-{preset}: every function translated" 1 (js.splitOn "not translated").length
      assertEq s!"{file}-{preset}: no call of the runtime" 1 (js.splitOn "import").length
      for l in ["export const test1 = (f, g, x) => f(x) + g(x);",
          "export const test2 = (f, g, x) => {\n  const fx = f(x);\n  const gx = g(x);\n  return fx + gx + fx + gx;\n};"] do
        assertEq s!"{file}-{preset}: {l}" true ((js.splitOn l).length == 2)
      -- recording functions: each is called once per function
      let script := s!"import * as M from '{dir}/{file}-{preset}.js';
let calls = 0;
const f = (x) => \{ calls++; return '[' + x + ']'; }, g = (x) => \{ calls++; return '(' + x + ')'; };
console.log([M.test1(f, g, 5{n}), M.test2(f, g, 5{n})].join('|') + '|' + calls);"
      let run ← IO.Process.output { cmd := "node", args := #["--input-type=module", "-e", script] }
      assertEq s!"{file}-{preset}: node -e" "" (if run.exitCode == 0 then "" else run.stderr)
      assertEq s!"{file}-{preset}: the answers" "[5](5)|[5](5)[5](5)|4"
        run.stdout.trimAscii.toString
  it "a name made of a call never hides a name of the module (needs leanscript)" do
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let dir := s!"{← IO.currentDir}/.lake/build/callNames"
    IO.FS.createDirAll dir
    let file := "CallNames"
    IO.FS.writeFile s!"{dir}/{file}.lean" "def fx (f : Int → String) (x : Int) : String :=
  f x ++ f x

def ab (a : Int → String) (b : Int) : String :=
  a b ++ a b

def four (f : Nat → String) (i : Nat) (n : Nat) : String :=
  f i ++ f n ++ f i ++ f n
"
    let args := #["--quiet", s!"--out-dir={dir}", s!"{dir}/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    let js ← IO.FS.readFile s!"{dir}/{file}-pbo.js"
    -- `fx` and `ab` are functions of the module: the results keep a counter
    assertEq s!"{file}: fx keeps a counter" true ((js.splitOn "const fx$1 = f(x);").length == 2)
    assertEq s!"{file}: ab keeps a counter" true ((js.splitOn "const ab$1 = a(b);").length == 2)
    -- `fi` and `fn` are free
    assertEq s!"{file}: fi named" true ((js.splitOn "const fi = f(i);").length == 2)
    assertEq s!"{file}: fn named" true ((js.splitOn "const fn = f(n);").length == 2)
    -- the shared calls come in source order: `f i` (the first call) before `f n`
    assertEq s!"{file}: calls in source order" true
      ((js.splitOn "const fi = f(i);\n  const fn = f(n);\n  return fi + fn + fi + fn;").length == 2)
  it "the differential checks call the functions on sample functions (needs node and leanscript)" do
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/defaultRulesSemigroupCheck"
    IO.FS.createDirAll dir
    let file := "DefaultRulesSemigroup01"
    let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript --check" "" (if out.exitCode == 0 then "" else out.stderr)
    for preset in ["pbo", "faithful"] do
      let run ← IO.Process.output { cmd := "node", args := #[s!"{dir}/{file}-{preset}.check.mjs"] }
      assertEq s!"{file}-{preset}: node" "" (if run.exitCode == 0 then "" else run.stdout)
      -- both functions, on every sample of `f`, `g` (two functions each) and `x` (seven
      -- integers), at most 24 combinations per function
      assertEq s!"{file}-{preset}: the checks" s!"{file}-{preset}.js: 28 passed, 0 failed"
        run.stdout.trimAscii.toString

def defaultRulesSemigroup02Spec : Spec := describe "DefaultRulesSemigroup02" do
  it "renamings, literals and closed appends of purescript-backend-optimizer (needs node and leanscript)" do
    -- purescript-backend-optimizer (`legacy-backend/DefaultRulesSemigroup02.js`): `test1` and
    -- `test2` are other names of `appendR`, `test4` is the record literal, and the inlined
    -- `test3` appends onto the literal `["hello", ...b_bar]`.  Ours: the same, uncurried, and
    -- `test3`/`test4` computed in every namespace (also `Noinline`).
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/defaultRulesSemigroup02"
    IO.FS.createDirAll dir
    let file := "DefaultRulesSemigroup02"
    let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    for preset in ["pbo", "faithful"] do
      let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      -- only `instReprR.repr` (a `Char` leaf) is not translated
      assertEq s!"{file}-{preset}: every test translated" 1 (js.splitOn "test4:").length
      assertEq s!"{file}-{preset}: no call of the runtime" 1 (js.splitOn "import").length
      for ns in ["Inline", "Noinline", "AlwaysInline", "InlineIfReduceInline"] do
        for l in [s!"export const {ns}$test1 = {ns}$appendR;",
            s!"export const {ns}$test2 = {ns}$appendR;",
            s!"export const {ns}$test3 = (b) => (\{\n  _1: \"hello\" + b._1,\n  _2: [\"hello\", ...b._2],\n});",
            "_1: \"hello, World!\"", "_2: [\"hello\", \"World!\"]"] do
          assertEq s!"{file}-{preset}: {l}" true ((js.splitOn l).length > 1)
      let run ← IO.Process.output { cmd := "node", args := #[s!"{dir}/{file}-{preset}.check.mjs"] }
      assertEq s!"{file}-{preset}: node" "" (if run.exitCode == 0 then "" else run.stdout)
      assertEq s!"{file}-{preset}: the checks" s!"{file}-{preset}.js: 244 passed, 0 failed"
        run.stdout.trimAscii.toString

/-- The JavaScript names of Lean names (`MoreJs.Ident`): escaped by code points, read back. -/
def escapeIdentifiersSpec : Spec := describe "EscapeIdentifiers" do
  -- characters beyond ASCII kept: only `α` here (the tool asks `ID_Start` / `ID_Continue`)
  let idc : Bool → Char → Bool := fun _ c => c == 'α'
  let res : String → Bool := fun s => ["class", "Math"].contains s
  it "escapes every other character by its code point" do
    for (n, js) in [("a.b ?$$ \\\" →", "a_x2eb_x20_x3f_x24_x24_x20_x5c_x22_x20_u2192"),
        ("foo'", "foo_x27"), ("x_x", "x_x5fx"), ("a_b", "a_b"), ("class", "class_x"),
        ("", "_x"), ("1abc", "_x31abc"), ("α₁", "α_u2081"), ("😀", "_U01f600")] do
      assertEq n js (MoreJs.Ident.ident idc res n)
    assertEq "Foo.bar" "Foo$bar" (MoreJs.Ident.name idc res ["Foo", "bar"])
  it "reads the names back" do
    for ns in [["a.b ?$$ \\\" →"], ["foo'", "x_x"], ["class"], [""], ["_u", "a$b"], ["😀", "1"]] do
      assertEq s!"{ns}" ns (MoreJs.Ident.decodeName (MoreJs.Ident.name idc res ns))
  it "the export of purescript-backend-optimizer's EscapeIdentifiers (needs node and leanscript)" do
    -- purescript-backend-optimizer: `a_u2eb_u20_u3f_u24_u24_u20_u22_u20_u2192` (its escapes have
    -- no fixed width: `_u2eb` may be `.` then `b`).  Ours: fixed widths, read back exactly (the
    -- Lean name holds a backslash, `_x5c`).
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/escapeIdentifiers"
    IO.FS.createDirAll dir
    let file := "EscapeIdentifiers"
    let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    for (preset, v) in [("pbo", "42"), ("faithful", "42n")] do
      let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      let l := s!"export const a_x2eb_x20_x3f_x24_x24_x20_x5c_x22_x20_u2192 = {v};"
      assertEq s!"{file}-{preset}: {l}" true ((js.splitOn l).length > 1)
      let run ← IO.Process.output { cmd := "node", args := #[s!"{dir}/{file}-{preset}.check.mjs"] }
      assertEq s!"{file}-{preset}: node" "" (if run.exitCode == 0 then "" else run.stdout)
      assertEq s!"{file}-{preset}: the checks" s!"{file}-{preset}.js: 1 passed, 0 failed"
        run.stdout.trimAscii.toString

/-- `Tests/SnapshotsPBOPure/EsPrecedence01.lean`: the repeated `f a` are shared, and the delay
    `() => f()` that is left is `f` itself (`Term.delayEta`), so `test1` is `(f) => f`, where
    purescript-backend-optimizer calls `f` up to three times. -/
def esPrecedence01Spec : Spec := describe "EsPrecedence01" do
  it "the optimised statement answers its argument, with no call" do
    let t := CseTest.test1T (Δ := DSig.nil)
    assertEq "calls before" 5 t.numCalls
    assertEq "calls after" 0 (t.optimizeN 3).numCalls
    assertEq "printed" ("val k1 [1] : ((Lazy Bool) → (Lazy Bool)) := " ++
      "fun x2 [1] : (Lazy Bool) => (closed)\n  ret x2\nret k1") (t.optimizeN 3).pretty
    for b in [false, true] do
      assertEq s!"value at {b}" (CseTest.test1 (fun _ => b) () ()) ((t.optimizeN 3).run b)
  it "Term.delayEta alone: the delay `() => f()` is `f`" do
    let t := CseTest.etaT (Δ := DSig.nil)
    assertEq "translated" ("val k1 [ω] : ((Lazy Bool) → (Lazy Bool)) := " ++
      "fun x2 [ω] : (Lazy Bool) => (closed)\n  val k3 [ω] : (Lazy Bool) := lazy (open)\n" ++
      "    let x4 [ω] : Bool := x2 ()\n    ret x4\n  ret k3\nret k1") t.pretty
    -- the mention of the delay is `f`; the delay is then dead
    assertEq "Term.delayEta" true ((t.delayEta.pretty.splitOn "  ret x2\nret k1").length > 1)
    assertEq "then Term.dce" ("val k1 [1] : ((Lazy Bool) → (Lazy Bool)) := " ++
      "fun x2 [1] : (Lazy Bool) => (closed)\n  ret x2\nret k1") t.delayEta.dce.pretty
    assertEq "the calls are kept" t.numCalls t.delayEta.numCalls
    for b in [false, true] do
      assertEq s!"value at {b}" (CseTest.eta (fun _ => b) ()) (t.delayEta.run b)
  it "Term.delayEta: a delay passed to a call is the delay it forces" do
    let t := CseTest.etaArgT (Δ := DSig.nil)
    assertEq "optimised" ("val k1 [1] : (((Lazy Nat) → Nat) → ((Lazy Nat) → Nat)) := " ++
      "fun x2 [ω] : ((Lazy Nat) → Nat) => (closed)\n" ++
      "  val k3 [1] : ((Lazy Nat) → Nat) := fun x4 [1] : (Lazy Nat) => (open)\n" ++
      "    let x5 [1] : Nat := x2 x4\n    ret lean_nat_mul(x5, 2)\n  ret k3\nret k1")
      (t.optimizeN 3).pretty
    -- a delay denotes the value it holds: `g` is run on `Nat → Nat`
    for (g, n) in [((fun x => x + 1 : Nat → Nat), 5), (fun x => x * 3, 2)] do
      assertEq s!"value at {n}" (CseTest.etaArg (fun h => g (h ())) (fun _ => n))
        ((t.optimizeN 3).run g n)
  it "the JavaScript and its checks (needs node and leanscript)" do
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/esPrecedence01"
    IO.FS.createDirAll dir
    let file := "EsPrecedence01"
    let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    for preset in ["pbo", "faithful"] do
      let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      let l := "export const test1 = (f) => f;"
      assertEq s!"{file}-{preset}: {l}" true ((js.splitOn l).length > 1)
      let run ← IO.Process.output { cmd := "node", args := #[s!"{dir}/{file}-{preset}.check.mjs"] }
      assertEq s!"{file}-{preset}: node" "" (if run.exitCode == 0 then "" else run.stdout)
      assertEq s!"{file}-{preset}: the checks" s!"{file}-{preset}.js: 2 passed, 0 failed"
        run.stdout.trimAscii.toString

/-- `Tests/SnapshotsPBOPure/EsPrecedence02.lean`: the operands of the float additions are
    commuted (and `(a - a) + (a + a)` regrouped) so that every function prints without
    parentheses, `a + a + a + a` or `a - a + a + a`, as the legacy backend's output does, with
    the results unchanged (`Neu.floatComm`, `Tests/TermTests/Optimize/FloatCommTest.lean`). -/
def esPrecedence02Spec : Spec := describe "EsPrecedence02" do
  let fns : List (String × (Float → Float) × (HashableFloat → HashableFloat) × String) := [
    ("test1", FloatCommTest.test1, ((FloatCommTest.test1T (Δ := DSig.nil)).optimizeN 3).run,
      "lean_float_add(lean_float_add(lean_float_add(x2, x2), x2), x2)"),
    ("test2", FloatCommTest.test2, ((FloatCommTest.test2T (Δ := DSig.nil)).optimizeN 3).run,
      "lean_float_add(lean_float_add(lean_float_add(x2, x2), x2), x2)"),
    ("test3", FloatCommTest.test3, ((FloatCommTest.test3T (Δ := DSig.nil)).optimizeN 3).run,
      "lean_float_add(lean_float_add(lean_float_sub(x2, x2), x2), x2)"),
    ("test4", FloatCommTest.test4, ((FloatCommTest.test4T (Δ := DSig.nil)).optimizeN 3).run,
      "lean_float_add(lean_float_add(lean_float_sub(x2, x2), x2), x2)"),
    ("test5", FloatCommTest.test5, ((FloatCommTest.test5T (Δ := DSig.nil)).optimizeN 3).run,
      "lean_float_add(lean_float_add(lean_float_sub(x2, x2), x2), x2)")]
  let pretties := [((FloatCommTest.test1T (Δ := DSig.nil)).optimizeN 3).pretty,
    ((FloatCommTest.test2T (Δ := DSig.nil)).optimizeN 3).pretty,
    ((FloatCommTest.test3T (Δ := DSig.nil)).optimizeN 3).pretty,
    ((FloatCommTest.test4T (Δ := DSig.nil)).optimizeN 3).pretty,
    ((FloatCommTest.test5T (Δ := DSig.nil)).optimizeN 3).pretty]
  it "the optimised statements, and their values (the bits of the Lean function's)" do
    for ((name, f, run, body), pretty) in fns.zip pretties do
      assertEq s!"{name}: printed" (FloatCommTest.printedFloatFn body) pretty
      for x in [(0 : Float), 0.1, 0.5, 1, 3 / 7, -1.5, 1e308, -1e308, 2.5e-324, 30] do
        assertEq s!"{name} {x}" (HashableFloat.normalize (f x)).toFloat.toBits
          (run (HashableFloat.normalize x)).toFloat.toBits
  it "the JavaScript and its checks (needs node and leanscript)" do
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/esPrecedence02"
    IO.FS.createDirAll dir
    let file := "EsPrecedence02"
    let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    for preset in ["pbo", "faithful"] do
      let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      for l in ["export const test1 = (a) => a + a + a + a;",
          "export const test2 = (a) => a + a + a + a;",
          "export const test3 = (a) => a - a + a + a;",
          "export const test4 = (a) => a - a + a + a;",
          "export const test5 = (a) => a - a + a + a;"] do
        assertEq s!"{file}-{preset}: {l}" true ((js.splitOn l).length > 1)
      let run ← IO.Process.output { cmd := "node", args := #[s!"{dir}/{file}-{preset}.check.mjs"] }
      assertEq s!"{file}-{preset}: node" "" (if run.exitCode == 0 then "" else run.stdout)
      assertEq s!"{file}-{preset}: the checks" s!"{file}-{preset}.js: 40 passed, 0 failed"
        run.stdout.trimAscii.toString

/-- `Tests/SnapshotsPBOPure/EsPrecedence03.lean`: `UInt32.shiftRight` is written inline as
    JavaScript's `>>>` (`(a >>> b) >>> b`, `a >>> (b >>> b)`), and `Int32.shiftRight` /
    `Int32.shiftLeft` as `>>` / `<<`, instead of calls of `runtime.js`: JavaScript takes the shift
    count modulo 32 itself (`RuntimeSpec.uint32_shift_right_inline`, …). -/
def esPrecedence03Spec : Spec := describe "EsPrecedence03" do
  let us : List UInt32 := [0, 1, 2, 5, 13, 31, 32, 33, 63, 64, 0x7fffffff, 0x80000000, 0xffffffff]
  let is : List Int32 := [0, 1, -1, 3, -7, 31, 32, -32, 33, 12, 2147483647, -2147483648]
  it "the model of JavaScript's shifts agrees with Lean's on samples" do
    for a in us do
      for b in us do
        assertEq s!"{a} >>> {b}" ((a >>> b).toNat : Int) (RuntimeSpec.ushr a.toNat b.toNat)
    for a in is do
      for b in is do
        assertEq s!"{a} >> {b}" (a >>> b).toInt (RuntimeSpec.sar a.toInt b.toInt)
        assertEq s!"{a} << {b}" (a <<< b).toInt (RuntimeSpec.shl a.toInt b.toInt)
  it "the JavaScript and its checks (needs node and leanscript)" do
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/esPrecedence03"
    IO.FS.createDirAll dir
    -- the file of the snapshot, and the shifts of `Int32` (no snapshot has them)
    IO.FS.writeFile s!"{dir}/Int32Shifts.lean"
      "def shr (a b : Int32) : Int32 := a >>> b\ndef shl (a b : Int32) : Int32 := a <<< b\n"
    let files : List (String × String × List String × Nat) := [
        (s!"Tests/SnapshotsPBOPure/EsPrecedence03.lean", "EsPrecedence03",
          ["export const test1 = (a, b) => (a >>> b) >>> b;",
           "export const test2 = (a, b) => a >>> (b >>> b);"], 36),
        (s!"{dir}/Int32Shifts.lean", "Int32Shifts",
          ["export const shr = (a, b) => a >> b;", "export const shl = (a, b) => a << b;"], 34)]
    for (src, file, lines, n) in files do
      let args := #["--quiet", "--check", s!"--out-dir={dir}", src]
      let out ← IO.Process.output { cmd := bin.toString, args }
      assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
      for preset in ["pbo", "faithful"] do
        let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
        assertEq s!"{file}-{preset}: no call of the runtime" 1 (js.splitOn "import").length
        for l in lines do
          assertEq s!"{file}-{preset}: {l}" true ((js.splitOn l).length > 1)
        let run ← IO.Process.output { cmd := "node", args := #[s!"{dir}/{file}-{preset}.check.mjs"] }
        assertEq s!"{file}-{preset}: node" "" (if run.exitCode == 0 then "" else run.stdout)
        assertEq s!"{file}-{preset}: the checks" s!"{file}-{preset}.js: {n} passed, 0 failed"
          run.stdout.trimAscii.toString

/-- `Tests/SnapshotsPBOPure/EsSharedElse.lean`: two tests that end in the same answer are
    merged into one condition by the `Term` optimiser (`Branch.mergeTest`,
    `Tests/TermTests/Optimize/MergeTestTest.lean`): `if (a && b) { return 1; } return c ? 2 : 3;`,
    as purescript-backend-optimizer's output (`legacy-backend/EsSharedElse.js`), with the shared
    `else` as one conditional. -/
def esSharedElseSpec : Spec := describe "EsSharedElse" do
  let bools := [false, true]
  it "the optimised statements, and their values (the Lean functions', on every input)" do
    assertEq "test1: printed" MergeTestTest.test1Printed
      ((MergeTestTest.test1T (Δ := DSig.nil)).optimizeN 3).pretty
    assertEq "andChain: printed" MergeTestTest.andChainPrinted
      ((MergeTestTest.andChainT (Δ := DSig.nil)).optimizeN 3).pretty
    assertEq "orChain: printed" MergeTestTest.orChainPrinted
      ((MergeTestTest.orChainT (Δ := DSig.nil)).optimizeN 3).pretty
    assertEq "andNot: printed" MergeTestTest.andNotPrinted
      ((MergeTestTest.andNotT (Δ := DSig.nil)).optimizeN 3).pretty
    assertEq "orNot: printed" MergeTestTest.orNotPrinted
      ((MergeTestTest.orNotT (Δ := DSig.nil)).optimizeN 3).pretty
    for a in bools do
      for b in bools do
        assertEq s!"orChain {a} {b}" (MergeTestTest.orChain a b)
          (((MergeTestTest.orChainT (Δ := DSig.nil)).optimizeN 3).run a b)
        assertEq s!"orNot {a} {b}" (MergeTestTest.orNot a b)
          (((MergeTestTest.orNotT (Δ := DSig.nil)).optimizeN 3).run a b)
        for c in bools do
          assertEq s!"test1 {a} {b} {c}" (MergeTestTest.test1 a b c)
            (((MergeTestTest.test1T (Δ := DSig.nil)).optimizeN 3).run a b c)
          assertEq s!"andChain {a} {b} {c}" (MergeTestTest.andChain a b c)
            (((MergeTestTest.andChainT (Δ := DSig.nil)).optimizeN 3).run a b c)
          assertEq s!"andNot {a} {b} {c}" (MergeTestTest.andNot a b c)
            (((MergeTestTest.andNotT (Δ := DSig.nil)).optimizeN 3).run a b c)
  it "the JavaScript and its checks (needs node and leanscript)" do
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/esSharedElse"
    IO.FS.createDirAll dir
    let file := "EsSharedElse"
    let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    for (preset, one) in [("pbo", "1"), ("faithful", "1n")] do
      let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      let two := if preset == "pbo" then "2 : 3" else "2n : 3n"
      for l in ["export const test1 = (a, b, c) => {\n  if (a && b) {\n    return " ++ one ++
          ";\n  }\n  return c ? " ++ two ++ ";\n};"] do
        assertEq s!"{file}-{preset}: {l}" true ((js.splitOn l).length > 1)
      let run ← IO.Process.output { cmd := "node", args := #[s!"{dir}/{file}-{preset}.check.mjs"] }
      assertEq s!"{file}-{preset}: node" "" (if run.exitCode == 0 then "" else run.stdout)
      assertEq s!"{file}-{preset}: the checks" s!"{file}-{preset}.js: 8 passed, 0 failed"
        run.stdout.trimAscii.toString

/-- A `EFoldable` instance at the stand-in `fun _ => Nat` for the compiled checks of
    `etaReduceRegressionSpec`: `n` appends the unit `n + 1` times. -/
@[instance_reducible] def etaFoldableNat : PolymorphismTest.EFoldable.{0, 0, 0} (fun _ => Nat) where
  foldMap := fun {_ m} [inst : PolymorphismTest.EMonoid m] _ n =>
    (List.range n).foldl (fun acc _ => inst.append acc inst.empty) (inst.append inst.empty inst.empty)

/-- `Tests/SnapshotsPBOPure/EtaReduceRegression01.lean`: the definitions polymorphic in
    universes (`identity`, `fold`) are translated, an instance parameter is a parameter (its
    dictionary), and the point-free `fold` is read in eta-long form, so the JavaScript is
    `export const fold = (dictFoldable, dictMonoid, a) => dictFoldable(dictMonoid, identity, a);`,
    the closure `(x) => x` linked to the function `identity` of the module, as
    purescript-backend-optimizer's `legacy-backend/EtaReduceRegression01.js` (which is curried
    and returns a closure). -/
def etaReduceRegressionSpec : Spec := describe "EtaReduceRegression01" do
  it "the translations compute the Lean definitions (compiled `Term.eval`)" do
    for a in ([0, 1, 7, 1000] : List Nat) do
      assertEq s!"identity {a}" (PolymorphismTest.identity a)
        ((PolymorphismTest.identityT (Δ := DSig.nil)).run a : Nat)
    let monoids : List (PolymorphismTest.EMonoid Nat) :=
      [⟨0, (· + ·)⟩, ⟨1, (· * ·)⟩, ⟨3, fun a b => a + 2 * b⟩]
    for M in monoids do
      for x in ([0, 1, 4] : List Nat) do
        assertEq s!"fold {M.empty} {x}" (@PolymorphismTest.fold (fun _ => Nat) Nat etaFoldableNat M x)
          ((PolymorphismTest.foldT (Δ := DSig.nil)).run
            (fun m g y => @etaFoldableNat.foldMap Nat Nat ⟨m.1, m.2⟩ g y) (M.empty, M.append) x : Nat)
  it "the JavaScript, its checks, and `fold` on the dictionaries of `Option`/`String` (needs node and leanscript)" do
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/etaReduceRegression"
    IO.FS.createDirAll dir
    let file := "EtaReduceRegression01"
    let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    for preset in ["pbo", "faithful"] do
      let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      assertEq s!"{file}-{preset}: nothing left untranslated" false
        ((js.splitOn "not translated").length > 1)
      assertEq s!"{file}-{preset}: no call of the runtime" 1 (js.splitOn "import").length
      for l in ["export const identity = (x) => x;",
          "export const fold = (dictFoldable, dictMonoid, a) =>\n  dictFoldable(dictMonoid, identity, a);",
          "export const test = (a) => (a.tag === 0 ? \"\" : a._1);"] do
        assertEq s!"{file}-{preset}: {l}" true ((js.splitOn l).length > 1)
      let run ← IO.Process.output { cmd := "node", args := #[s!"{dir}/{file}-{preset}.check.mjs"] }
      assertEq s!"{file}-{preset}: node" "" (if run.exitCode == 0 then "" else run.stdout)
      assertEq s!"{file}-{preset}: the checks" s!"{file}-{preset}.js: 3 passed, 0 failed"
        run.stdout.trimAscii.toString
      -- `fold` called on the dictionaries of the file's instances (`Foldable Option`: its one
      -- field `foldMap`; `Monoid String`: the record of `empty` and `append`), as `test` is
      let main := s!"{dir}/{file}-{preset}-dict.mjs"
      IO.FS.writeFile main (s!"import * as M from \"./{file}-{preset}.js\";\n" ++
        "const foldableOption = (dictMonoid, f, o) => (o.tag === 0 ? dictMonoid._1 : f(o._1));\n" ++
        "const monoidString = { _1: \"\", _2: (a, b) => a + b };\n" ++
        "const r = [M.fold(foldableOption, monoidString, { tag: 0 }),\n" ++
        "  M.fold(foldableOption, monoidString, { tag: 1, _1: \"ab\" }),\n" ++
        "  M.identity(\"x\"), M.test({ tag: 1, _1: \"cd\" }), M.test({ tag: 0 })];\n" ++
        "console.log(JSON.stringify(r));\n")
      let run ← IO.Process.output { cmd := "node", args := #[main] }
      -- Lean: `test none = ""`, `test (some s) = s`, `identity x = x`
      assertEq s!"{file}-{preset}: fold on the dictionaries" "[\"\",\"ab\",\"x\",\"cd\",\"\"]"
        run.stdout.trimAscii.toString

/-- `Tests/SnapshotsPBOPure/FloatLetRegression01.lean`: the call `f 2`, which the translation
    repeats, is computed once (common subexpression elimination, `2` being an atom), and the
    call `f 1`, used once, is moved down to its use (`Term.sinkWalk`,
    `Tests/TermTests/Optimize/SinkLetTest.lean`), so the JavaScript is
    `const x$1 = f(2); return { _1: f(1), _2: x$1, _3: x$1 };`, the shape of
    purescript-backend-optimizer's `legacy-backend/FloatLetRegression01.js`. -/
def floatLetRegressionSpec : Spec := describe "FloatLetRegression01" do
  it "the optimised statements, and their values (the Lean functions')" do
    assertEq "test: printed" SinkLetTest.testPrinted
      ((SinkLetTest.testT (Δ := DSig.nil)).optimizeN 3).pretty
    assertEq "litShare: printed" SinkLetTest.litSharePrinted
      ((SinkLetTest.litShareT (Δ := DSig.nil)).optimizeN 3).pretty
    let fs : List (String × (Int → Int)) :=
      [("x + 1", (· + 1)), ("2 - x", (2 - ·)), ("x * x", fun x => x * x)]
    for (name, f) in fs do
      let r := SinkLetTest.test f
      assertEq s!"test ({name})" (r.b, r.c1, r.c2)
        ((((SinkLetTest.testT (Δ := DSig.nil)).optimizeN 3).run f : Int × Int × Int))
    let g : String → Nat := String.length
    let h : Nat → Nat := (· * 7)
    assertEq "litShare" (SinkLetTest.litShare g h)
      ((((SinkLetTest.litShareT (Δ := DSig.nil)).optimizeN 3).run g h : Nat × Nat × Nat × Nat))
  it "the JavaScript and its checks (needs node and leanscript)" do
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/floatLetRegression"
    IO.FS.createDirAll dir
    let file := "FloatLetRegression01"
    let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    for (preset, n) in [("pbo", ""), ("faithful", "n")] do
      let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      for l in ["export const test = (f) => {\n  const x$1 = f(2" ++ n ++ ");\n  return { _1: f(1" ++ n ++
          "), _2: x$1, _3: x$1 };\n};"] do
        assertEq s!"{file}-{preset}: {l}" true ((js.splitOn l).length > 1)
      let run ← IO.Process.output { cmd := "node", args := #[s!"{dir}/{file}-{preset}.check.mjs"] }
      assertEq s!"{file}-{preset}: node" "" (if run.exitCode == 0 then "" else run.stdout)
      assertEq s!"{file}-{preset}: the checks" s!"{file}-{preset}.js: 2 passed, 0 failed"
        run.stdout.trimAscii.toString

/-- `Tests/SnapshotsPBOPure/FunctionCompose01.lean`: the compositions of `f` and `g` (closed
    functions that return a literal) are inlined by the `Term` optimiser
    (`Tests/TermTests/Optimize/FunctionComposeTest.lean`), so each `testN` is a function that
    returns the literal, with no call: `export const test1 = (a) => "a";`, as
    purescript-backend-optimizer's `legacy-backend/FunctionCompose01.js`. -/
def functionCompose01Spec : Spec := describe "FunctionCompose01" do
  it "the optimised statements, and their values (the Lean functions')" do
    -- (name, literal, the Lean function, and of the optimised translation: the printed
    -- statements, the number of calls, the function it computes)
    let ts : List (String × String × (String → String) × String × Nat × (String → String)) :=
      [("test1", "a", FunctionComposeTest.test1,
          ((FunctionComposeTest.test1T (Δ := DSig.nil)).optimizeN 3).pretty,
          ((FunctionComposeTest.test1T (Δ := DSig.nil)).optimizeN 3).numCalls,
          ((FunctionComposeTest.test1T (Δ := DSig.nil)).optimizeN 3).run),
       ("test2", "b", FunctionComposeTest.test2,
          ((FunctionComposeTest.test2T (Δ := DSig.nil)).optimizeN 3).pretty,
          ((FunctionComposeTest.test2T (Δ := DSig.nil)).optimizeN 3).numCalls,
          ((FunctionComposeTest.test2T (Δ := DSig.nil)).optimizeN 3).run),
       ("test3", "a", FunctionComposeTest.test3,
          ((FunctionComposeTest.test3T (Δ := DSig.nil)).optimizeN 3).pretty,
          ((FunctionComposeTest.test3T (Δ := DSig.nil)).optimizeN 3).numCalls,
          ((FunctionComposeTest.test3T (Δ := DSig.nil)).optimizeN 3).run),
       ("test4", "b", FunctionComposeTest.test4,
          ((FunctionComposeTest.test4T (Δ := DSig.nil)).optimizeN 3).pretty,
          ((FunctionComposeTest.test4T (Δ := DSig.nil)).optimizeN 3).numCalls,
          ((FunctionComposeTest.test4T (Δ := DSig.nil)).optimizeN 3).run)]
    for (name, lit, fn, printed, calls, run) in ts do
      assertEq s!"{name}: printed" (FunctionComposeTest.constPrinted lit) printed
      assertEq s!"{name}: no call left" 0 calls
      for s in ["", "a", "héllo"] do
        assertEq s!"{name} {s}" (fn s) (run s)
  it "the JavaScript and its checks (needs node and leanscript)" do
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/functionCompose01"
    IO.FS.createDirAll dir
    let file := "FunctionCompose01"
    let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    for preset in ["pbo", "faithful"] do
      let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      assertEq s!"{file}-{preset}: no call of the runtime" 1 (js.splitOn "import").length
      for l in ["export const f = (x) => \"a\";", "export const g = (x) => \"b\";",
          "export const test1 = (a) => \"a\";", "export const test2 = (a) => \"b\";",
          "export const test3 = (a) => \"a\";", "export const test4 = (a) => \"b\";"] do
        assertEq s!"{file}-{preset}: {l}" true ((js.splitOn l).length > 1)
      let run ← IO.Process.output { cmd := "node", args := #[s!"{dir}/{file}-{preset}.check.mjs"] }
      assertEq s!"{file}-{preset}: node" "" (if run.exitCode == 0 then "" else run.stdout)
      assertEq s!"{file}-{preset}: the checks" s!"{file}-{preset}.js: 31 passed, 0 failed"
        run.stdout.trimAscii.toString

/-- `Tests/SnapshotsPBOPure/FunctionCompose02.lean`: compositions of the parameters `f` and `g`
    (unknown functions, so nothing to inline) become a chain of calls with no intermediate
    closure (`Tests/TermTests/Optimize/FunctionCompose02Test.lean`):
    `export const test2 = (f, g, a) => g(f(g(a)));`, as purescript-backend-optimizer's
    `legacy-backend/FunctionCompose02.js` (`(f) => (g) => (x) => g(f(g(x)))`), uncurried.
    `leanscript --check` makes no check of a function with function parameters, so this runs
    the JavaScript with node on sample `f`, `g` and compares with Lean. -/
def functionCompose02Spec : Spec := describe "FunctionCompose02" do
  let f : Int → Int := fun x => 2 * x + 1
  let g : Int → Int := fun x => x - 3
  let xs : List Int := [-7, 0, 1, 42]
  it "the optimised statements, and their values (the Lean functions')" do
    -- (name, the Lean function, the calls (innermost first: `f`?), and of the optimised
    -- translation: the printed statements, the number of calls, the function it computes)
    let ts : List (String × (FunctionCompose02Test.F → FunctionCompose02Test.F →
        FunctionCompose02Test.F) × List Bool × String × Nat ×
        (FunctionCompose02Test.F → FunctionCompose02Test.F → FunctionCompose02Test.F)) :=
      [("test1", FunctionCompose02Test.test1, [false, true],
          ((FunctionCompose02Test.test1T (Δ := DSig.nil)).optimizeN 3).pretty,
          ((FunctionCompose02Test.test1T (Δ := DSig.nil)).optimizeN 3).numCalls,
          ((FunctionCompose02Test.test1T (Δ := DSig.nil)).optimizeN 3).run),
       ("test2", FunctionCompose02Test.test2, [false, true, false],
          ((FunctionCompose02Test.test2T (Δ := DSig.nil)).optimizeN 3).pretty,
          ((FunctionCompose02Test.test2T (Δ := DSig.nil)).optimizeN 3).numCalls,
          ((FunctionCompose02Test.test2T (Δ := DSig.nil)).optimizeN 3).run),
       ("test3", FunctionCompose02Test.test3, [false, true, false, true],
          ((FunctionCompose02Test.test3T (Δ := DSig.nil)).optimizeN 3).pretty,
          ((FunctionCompose02Test.test3T (Δ := DSig.nil)).optimizeN 3).numCalls,
          ((FunctionCompose02Test.test3T (Δ := DSig.nil)).optimizeN 3).run),
       ("test4", FunctionCompose02Test.test4, [false, true, false, true, false],
          ((FunctionCompose02Test.test4T (Δ := DSig.nil)).optimizeN 3).pretty,
          ((FunctionCompose02Test.test4T (Δ := DSig.nil)).optimizeN 3).numCalls,
          ((FunctionCompose02Test.test4T (Δ := DSig.nil)).optimizeN 3).run)]
    for (name, fn, calls, printed, numCalls, run) in ts do
      assertEq s!"{name}: printed" (FunctionCompose02Test.chainPrinted calls) printed
      assertEq s!"{name}: one call per composed function" calls.length numCalls
      for x in xs do
        assertEq s!"{name} {x}" (fn f g x) (run f g x)
        assertEq s!"{name} {x} (swapped)" (fn g f x) (run g f x)
  it "the JavaScript, run with node (needs node and leanscript)" do
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/functionCompose02"
    IO.FS.createDirAll dir
    let file := "FunctionCompose02"
    let args := #["--quiet", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    let tests : List (String × (FunctionCompose02Test.F → FunctionCompose02Test.F →
        FunctionCompose02Test.F)) :=
      [("test1", FunctionCompose02Test.test1), ("test2", FunctionCompose02Test.test2),
       ("test3", FunctionCompose02Test.test3), ("test4", FunctionCompose02Test.test4)]
    -- (preset, the suffix of an integer literal)
    for (preset, n) in [("pbo", ""), ("faithful", "n")] do
      let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      assertEq s!"{file}-{preset}: no call of the runtime" 1 (js.splitOn "import").length
      for l in ["export const test1 = (f, g, a) => f(g(a));",
          "export const test2 = (f, g, a) => g(f(g(a)));",
          "export const test3 = (f, g, a) => f(g(f(g(a))));",
          "export const test4 = (f, g, a) => g(f(g(f(g(a)))));"] do
        assertEq s!"{file}-{preset}: {l}" true ((js.splitOn l).length > 1)
      -- a module that prints `testN(f, g, x)` and `testN(g, f, x)` for every sample
      let lit (x : Int) : String := s!"{x}{n}"
      let mut prog := s!"import * as M from \"./{file}-{preset}.js\";\n" ++
        s!"const f = (x) => {lit 2} * x + {lit 1};\nconst g = (x) => x - {lit 3};\n" ++
        "const out = [];\n"
      let mut expected : List String := []
      for (name, fn) in tests do
        for x in xs do
          prog := prog ++ s!"out.push(String(M.{name}(f, g, {lit x})));\n" ++
            s!"out.push(String(M.{name}(g, f, {lit x})));\n"
          expected := expected ++ [toString (fn f g x), toString (fn g f x)]
      prog := prog ++ "console.log(out.join(\"\\n\"));\n"
      let runner := s!"{dir}/{file}-{preset}.run.mjs"
      IO.FS.writeFile runner prog
      let run ← IO.Process.output { cmd := "node", args := #[runner] }
      assertEq s!"{file}-{preset}: node" "" (if run.exitCode == 0 then "" else run.stderr)
      assertEq s!"{file}-{preset}: the values" ("\n".intercalate expected)
        run.stdout.trimAscii.toString

/-- `Tests/SnapshotsPBOPure/FunctionCompose03.lean`: compositions of thunks forced again at each
    use (`f () ∘ g ()`).  The optimiser shares the repeated `f ()`, `g ()`
    (`Tests/TermTests/Optimize/FunctionCompose03Test.lean`), and the printer writes a thunk
    forced once where it is used (JavaScript computes the function called before its
    arguments): `export const test1 = (f, g, a) => f()(g()(a));`,
    `const x$1 = g(); return x$1(f()(x$1(a)));` for `test2`, as purescript-backend-optimizer's
    `legacy-backend/FunctionCompose03.js` (`const $0 = g(); const $1 = f(); return (x) => …`),
    uncurried and with fewer constants.  This runs the JavaScript with node on sample thunks,
    compares with Lean, and checks that each thunk is forced exactly once per call. -/
def functionCompose03Spec : Spec := describe "FunctionCompose03" do
  let f : FunctionCompose03Test.F := fun _ x => 2 * x + 1
  let g : FunctionCompose03Test.F := fun _ x => x - 3
  let xs : List Int := [-7, 0, 1, 42]
  it "the optimised translations: their values (the Lean functions') and their calls" do
    -- (name, the Lean function, the calls of the optimised translation, the function it computes)
    let ts : List (String × (FunctionCompose03Test.F → FunctionCompose03Test.F → Int → Int) ×
        Nat × ((Int → Int) → (Int → Int) → Int → Int)) :=
      [("test1", FunctionCompose03Test.test1,
          ((FunctionCompose03Test.test1T (Δ := DSig.nil)).optimizeN 3).numCalls,
          ((FunctionCompose03Test.test1T (Δ := DSig.nil)).optimizeN 3).run),
       ("test2", FunctionCompose03Test.test2,
          ((FunctionCompose03Test.test2T (Δ := DSig.nil)).optimizeN 3).numCalls,
          ((FunctionCompose03Test.test2T (Δ := DSig.nil)).optimizeN 3).run),
       ("test3", FunctionCompose03Test.test3,
          ((FunctionCompose03Test.test3T (Δ := DSig.nil)).optimizeN 3).numCalls,
          ((FunctionCompose03Test.test3T (Δ := DSig.nil)).optimizeN 3).run),
       ("test4", FunctionCompose03Test.test4,
          ((FunctionCompose03Test.test4T (Δ := DSig.nil)).optimizeN 3).numCalls,
          ((FunctionCompose03Test.test4T (Δ := DSig.nil)).optimizeN 3).run)]
    for ((name, fn, numCalls, run), composed) in ts.zip ([2, 3, 4, 5] : List Nat) do
      assertEq s!"{name}: two thunks forced, then one call per composed function"
        (2 + composed) numCalls
      for x in xs do
        assertEq s!"{name} {x}" (fn f g x) (run (f ()) (g ()) x)
        assertEq s!"{name} {x} (swapped)" (fn g f x) (run (g ()) (f ()) x)
  it "the JavaScript, run with node (needs node and leanscript)" do
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/functionCompose03"
    IO.FS.createDirAll dir
    let file := "FunctionCompose03"
    let args := #["--quiet", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    let tests : List (String × (FunctionCompose03Test.F → FunctionCompose03Test.F → Int → Int)) :=
      [("test1", FunctionCompose03Test.test1), ("test2", FunctionCompose03Test.test2),
       ("test3", FunctionCompose03Test.test3), ("test4", FunctionCompose03Test.test4)]
    -- (preset, the suffix of an integer literal)
    for (preset, n) in [("pbo", ""), ("faithful", "n")] do
      let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      assertEq s!"{file}-{preset}: no call of the runtime" 1 (js.splitOn "import").length
      for l in ["export const test1 = (f, g, a) => f()(g()(a));",
          "export const test2 = (f, g, a) => {\n  const x$1 = g();\n  return x$1(f()(x$1(a)));\n};",
          "export const test3 = (f, g, a) => {\n  const x$1 = f();\n  const x$2 = g();\n" ++
            "  return x$1(x$2(x$1(x$2(a))));\n};",
          "export const test4 = (f, g, a) => {\n  const x$1 = g();\n  const x$2 = f();\n" ++
            "  return x$1(x$2(x$1(x$2(x$1(a)))));\n};"] do
        assertEq s!"{file}-{preset}: {l}" true ((js.splitOn l).length > 1)
      -- a module that prints `testN(f, g, x)`, `testN(g, f, x)` for every sample, each followed
      -- by how many times `f` and `g` were forced
      let lit (x : Int) : String := s!"{x}{n}"
      let mut prog := s!"import * as M from \"./{file}-{preset}.js\";\n" ++
        "let cf = 0, cg = 0;\n" ++
        s!"const f = () => \{ cf++; return (x) => {lit 2} * x + {lit 1}; };\n" ++
        s!"const g = () => \{ cg++; return (x) => x - {lit 3}; };\n" ++
        "const out = [];\n" ++
        "const run = (h) => { cf = 0; cg = 0; const v = h(); out.push(`${v} ${cf} ${cg}`); };\n"
      let mut expected : List String := []
      for (name, fn) in tests do
        for x in xs do
          prog := prog ++ s!"run(() => M.{name}(f, g, {lit x}));\n" ++
            s!"run(() => M.{name}(g, f, {lit x}));\n"
          expected := expected ++ [s!"{fn f g x} 1 1", s!"{fn g f x} 1 1"]
      prog := prog ++ "console.log(out.join(\"\\n\"));\n"
      let runner := s!"{dir}/{file}-{preset}.run.mjs"
      IO.FS.writeFile runner prog
      let run ← IO.Process.output { cmd := "node", args := #[runner] }
      assertEq s!"{file}-{preset}: node" "" (if run.exitCode == 0 then "" else run.stderr)
      assertEq s!"{file}-{preset}: the values, and each thunk forced once"
        ("\n".intercalate expected) run.stdout.trimAscii.toString

/-- `Tests/SnapshotsPBOPure/Fusion02.lean`: the pipeline over an unfold (`toArrayLoop` and
    `filterMapStep`, by well-founded recursion) is fused into one `for … of` loop that pushes
    onto the result (`LeanScript.TermElab.ToTerm.StreamFusion`), and the differential checks
    against Lean pass under node. -/
def fusion02Spec : Spec := describe "Fusion02" do
  it "the JavaScript of `test` is one loop, and its checks pass (needs node and leanscript)" do
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/fusion02"
    IO.FS.createDirAll dir
    let file := "Fusion02"
    let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    for preset in ["pbo", "faithful"] do
      let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      assertEq s!"{file}-{preset}: `test` is translated" true
        ((js.splitOn "export const test = (arr) => {").length > 1)
      assertEq s!"{file}-{preset}: one `for … of` loop" 2 (js.splitOn "for (const ").length
      assertEq s!"{file}-{preset}: no `while`, no closure, no recursion" 1
        ((js.splitOn "while").length + (js.splitOn "toArrayLoop(").length +
          (js.splitOn "filterMapStep(").length - 2)
      assertEq s!"{file}-{preset}: pushes onto the result in place" true
        ((js.splitOn "array__lean_array_push_mutable(acc$").length > 1)
      let run ← IO.Process.output { cmd := "node", args := #[s!"{dir}/{file}-{preset}.check.mjs"] }
      assertEq s!"{file}-{preset}: the checks" "" (if run.exitCode == 0 then "" else run.stdout ++ run.stderr)

def heterogeneous01Spec : Spec := describe "Heterogeneous01" do
  it "`test1` is a constant record, `test2` one record literal, and the checks run (needs node and leanscript)" do
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/heterogeneous01"
    IO.FS.createDirAll dir
    let file := "Heterogeneous01"
    let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    for (preset, one) in [("pbo", "int53__lean_int_add(args._1, 1)"), ("faithful", "args._1 + 1n")] do
      let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      assertEq s!"{file}-{preset}: `test1` is folded to a constant" true
        ((js.splitOn "export const test1 = { _1: 13").length > 1)
      assertEq s!"{file}-{preset}: `test2` builds its record directly" true
        ((js.splitOn s!"export const test2 = (args) => (\{\n  _1: {one},\n  _2: \{ _1: \"bar\", _2: args._2 },\n  _3: !args._3,\n});").length > 1)
      assertEq s!"{file}-{preset}: no closure record, no `zipRecord`" 1
        ((js.splitOn "zipRecord").length + (js.splitOn "=> (x").length - 1)
      let checks ← IO.FS.readFile s!"{dir}/{file}-{preset}.check.mjs"
      assertEq s!"{file}-{preset}: 4 checks" 5 (checks.splitOn "\ncheck(").length
      let run ← IO.Process.output { cmd := "node", args := #[s!"{dir}/{file}-{preset}.check.mjs"] }
      assertEq s!"{file}-{preset}: the checks" "" (if run.exitCode == 0 then "" else run.stdout ++ run.stderr)

/-- `Tests/SnapshotsPBOPure/InlineArrayIndex.lean`: `array[i]?` at a literal index is folded to
    the constant option (`{ tag: 1, _1: 1 }`, `{ tag: 0 }` out of bounds), as in the legacy
    output; the checks compare the options with Lean (`showUnion`).  And
    `Tests/SnapshotsMy/ArrayIndexBounds.lean`: an access under a test of its index against a
    literal that proves the bounds is the plain `a[i]` (`JsTerm.Lower.Bounds`), and only there. -/
def inlineArrayIndexSpec : Spec := describe "InlineArrayIndex" do
  it "the options are constants, accesses in bounds are plain, and the checks run (needs node and leanscript)" do
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/inlinearrayindex"
    IO.FS.createDirAll dir
    for src in ["Tests/SnapshotsPBOPure/InlineArrayIndex.lean", "Tests/SnapshotsMy/ArrayIndexBounds.lean"] do
      let out ← IO.Process.output { cmd := bin.toString, args := #["--quiet", "--check", s!"--out-dir={dir}", src] }
      assertEq s!"{src}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    for (preset, one, two, three) in [("pbo", "1", "2", "3"), ("faithful", "1n", "2n", "3n")] do
      let file := "InlineArrayIndex"
      let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      for (n, v) in [("test1", s!"\{ tag: 1, _1: {one} }"), ("test2", s!"\{ tag: 1, _1: {two} }"),
          ("test3", s!"\{ tag: 1, _1: {three} }"), ("test4", "{ tag: 0 }")] do
        assertEq s!"{file}-{preset}: `{n}` is a constant" true
          ((js.splitOn s!"export const {n} = {v};").length > 1)
      let checks ← IO.FS.readFile s!"{dir}/{file}-{preset}.check.mjs"
      assertEq s!"{file}-{preset}: 5 checks" 6 (checks.splitOn "\ncheck(").length
      let file := "ArrayIndexBounds"
      let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      -- `getUnproved` and `getSizedUnproved` only
      assertEq s!"{file}-{preset}: two accesses check their bounds" 3
        (js.splitOn "__lean_array_get(").length
      for frag in ["export const getLe = (i) => (", "export const getGe = (i) => (", "export const getD = (i) => ("] do
        assertEq s!"{file}-{preset}: {frag}… is one conditional" true ((js.splitOn frag).length > 1)
      for file in ["InlineArrayIndex", "ArrayIndexBounds"] do
        let run ← IO.Process.output { cmd := "node", args := #[s!"{dir}/{file}-{preset}.check.mjs"] }
        assertEq s!"{file}-{preset}: the checks" "" (if run.exitCode == 0 then "" else run.stdout ++ run.stderr)

/-- `Tests/SnapshotsPBOPure/InlineCase01.lean`: `maybe`/`maybe'` (`@[inline]`) are inlined into
    each `testN`, which is one function of all its parameters (no closure returned, no
    `Option.elim`, no `maybe`): one test of the tag, the lazy default forced only in the `none`
    branch, the partial application `g 1` a direct call `g(1, …)`.  The checks, which pass
    functions of two arguments too (`SType.fn2`), run under node. -/
def inlineCase01Spec : Spec := describe "InlineCase01" do
  it "each `testN` is one test of the tag, and the checks run (needs node and leanscript)" do
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/inlinecase01"
    IO.FS.createDirAll dir
    let file := "InlineCase01"
    let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    for (preset, add, one) in [("pbo", fun (x : String) => s!"int53__lean_int_add({x}, 1)", "1"),
        ("faithful", fun (x : String) => s!"{x} + 1n", "1n")] do
      let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      let fn (name ps o noneArm someArm : String) : String :=
        s!"export const {name} = ({ps}) => \{\n  if ({o}.tag === 0) \{\n    return {noneArm};\n  }\n  return {someArm};\n};"
      for (n, frag) in [
          ("test1", fn "test1" "f, o" "o" "f()" (add "o._1")),
          ("test2", fn "test2" "f, g, o" "o" "f()" s!"g({one}, o._1)"),
          ("test3", fn "test3" "f, a" "a" "f()" (add "a._1")),
          ("test4", fn "test4" "f, g, a" "a" "f()" s!"g({one}, a._1)"),
          ("test5", fn "test5" "a, g, a1" "a1" (add "a") s!"g({one}, a1._1)")] do
        assertEq s!"{file}-{preset}: `{n}` is one test of the tag" true ((js.splitOn frag).length > 1)
      assertEq s!"{file}-{preset}: no `maybe`, no `Option.elim`, no returned closure" 1
        ((js.splitOn "maybe").length + (js.splitOn "elim").length + (js.splitOn "=> (").length - 2)
      let checks ← IO.FS.readFile s!"{dir}/{file}-{preset}.check.mjs"
      -- 6 for each of `test1`, `test3`; 12 for each of `test2`, `test4`; 42 for `test5`
      assertEq s!"{file}-{preset}: 78 checks" 79 (checks.splitOn "\ncheck(").length
      for n in ["test2", "test4", "test5"] do
        assertEq s!"{file}-{preset}: `{n}` is checked with functions of two arguments" true
          ((checks.splitOn s!"M.{n}(").length > 1 && (checks.splitOn "(x, y) =>").length > 1)
      let run ← IO.Process.output { cmd := "node", args := #[s!"{dir}/{file}-{preset}.check.mjs"] }
      assertEq s!"{file}-{preset}: the checks" "" (if run.exitCode == 0 then "" else run.stdout ++ run.stderr)

namespace HtmlSnap

/-- A copy of `Tests/SnapshotsPBOPure/Html.lean` (whose definitions are private). -/
inductive Html where
  | elem (tag : String) (children : List Html)
  | text (content : String)

def render : Html → String
  | .text content => s!"Html.text {repr content}"
  | .elem tag children =>
      let childrenStr := String.intercalate ", " (children.attach.map fun ⟨c, _⟩ => render c)
      s!"Html.elem {repr tag} [{childrenStr}]"

def test (user : String) : Html :=
  Html.elem "section"
    [ Html.elem "h1" [Html.text ("Posts for " ++ user)]
    , Html.elem "article"
        [ Html.elem "h2" [Html.text "The first post"]
        , Html.elem "p"
            [ Html.text "This is the first post."
            , Html.text "Not much else to say."
            ]
        ]
    ]

/-- The users the JavaScript `test` is called on. -/
def users : List String := ["", "alice", "Bob \"the\" builder"]

end HtmlSnap

/-- `Tests/SnapshotsPBOPure/Html.lean`: `test` builds a tree of a type recursive through `List`
    (`children : List Html`).  Its JavaScript is one object literal, the list of children
    cons cells (`{ tag: 1, _1: head, _2: tail }`, as `List Html` is part of the recursion of
    `Html`); rendered in JavaScript, it gives what Lean's `render (test user)` gives. -/
def htmlSpec : Spec := describe "Html" do
  it "`test` is one object literal, and renders as in Lean (needs node and leanscript)" do
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/html"
    IO.FS.createDirAll dir
    let file := "Html"
    let args := #["--quiet", s!"--out-dir={dir}", s!"Tests/SnapshotsPBOPure/{file}.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    let expected := String.join (HtmlSnap.users.map fun u => HtmlSnap.render (HtmlSnap.test u) ++ "\n")
    for preset in ["pbo", "faithful"] do
      let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
      assertEq s!"{file}-{preset}: `test` is one object literal" true
        ((js.splitOn "export const test = (user) => ({\n  tag: 0,\n  _1: \"section\",").length > 1)
      let body := (js.splitOn "export const test = ").getLast!
      assertEq s!"{file}-{preset}: no statement, no call" 1
        ((body.splitOn "const ").length + (body.splitOn "return").length +
          (body.splitOn "(").length - (body.splitOn "(user)").length - (body.splitOn "({").length)
      let users := ", ".intercalate (HtmlSnap.users.map fun u => (Lean.Json.str u).compress)
      let script := s!"import \{ test } from {(Lean.Json.str s!"{dir}/{file}-{preset}.js").compress};
const list = (l) => \{ const a = []; for (; l.tag === 1; l = l._2) a.push(l._1); return a; };
const render = (v) => v.tag === 1 ? \"Html.text \" + JSON.stringify(v._1)
  : \"Html.elem \" + JSON.stringify(v._1) + \" [\" + list(v._2).map(render).join(\", \") + \"]\";
for (const u of [{users}]) console.log(render(test(u)));
"
      let path := s!"{dir}/{file}-{preset}.render.mjs"
      IO.FS.writeFile path script
      let run ← IO.Process.output { cmd := "node", args := #[path] }
      assertEq s!"{file}-{preset}: node" "" (if run.exitCode == 0 then "" else run.stderr)
      assertEq s!"{file}-{preset}: rendered as in Lean" expected run.stdout

/-- `Tests/SnapshotsPBOPure/InlineNever.lean`: `test` reads the literal constant `foo`; its
    JavaScript is the literal itself (`export const test = "foo";`, no indirection), on both
    presets.  `Tests/SnapshotsMy/NoInlineAlias.lean`: when the definition read is marked
    `@[noinline]`, the reader refers to it instead (`export const test = foo;`, as
    purescript-backend-optimizer does for `inline never`); the checks run under node. -/
def inlineNeverSpec : Spec := describe "InlineNever" do
  it "a literal constant stays the literal, unless `@[noinline]` (needs node and leanscript)" do
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/inlinenever"
    IO.FS.createDirAll dir
    for (path, file, frags) in [
        ("Tests/SnapshotsPBOPure", "InlineNever",
          ["export const foo = \"foo\";", "export const test = \"foo\";"]),
        ("Tests/SnapshotsMy", "NoInlineAlias",
          ["export const test = foo;", "export const test2 = \"bar\";",
           "export const test3 = big;", "export const test4 = \"foo!\";"])] do
      let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"{path}/{file}.lean"]
      let out ← IO.Process.output { cmd := bin.toString, args }
      assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
      for preset in ["pbo", "faithful"] do
        let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
        for frag in frags do
          assertEq s!"{file}-{preset}: `{frag}`" true ((js.splitOn frag).length > 1)
        let run ← IO.Process.output { cmd := "node", args := #[s!"{dir}/{file}-{preset}.check.mjs"] }
        assertEq s!"{file}-{preset}: the checks" "" (if run.exitCode == 0 then "" else run.stdout ++ run.stderr)

/-- `Tests/SnapshotsPBOPure/InlineReferenceOpArrayLength.lean`: the tests of the size of a known
    array are decided, and a constant reads the values of the constants before it by their names
    (`shareConstValues`: `extern2 = [extern1, [3], [0]]`, `test3 = extern1`, `test4 = extern2`, as
    purescript-backend-optimizer writes them); `Tests/SnapshotsMy/ShareConstValues.lean`: its
    edge cases (empty arrays, typed arrays, functions not rewritten).  The checks run under node. -/
def inlineReferenceOpArrayLengthSpec : Spec := describe "InlineReferenceOpArrayLength" do
  it "constants share the values of the constants before them (needs node and leanscript)" do
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/inlinerefarrlen"
    IO.FS.createDirAll dir
    -- (directory, file, fragments at both presets, at `pbo`, at `faithful`, absent, checks)
    for (path, file, frags, pboFrags, faithfulFrags, absent, nChecks) in [
        ("Tests/SnapshotsPBOPure", "InlineReferenceOpArrayLength",
          ["export const test1 = (fn) => [1", "export const extern2 = [extern1, [3", "export const test3 = extern1;",
           "export const test4 = extern2;"],
          ["const x$1 = fn();\n  return [[1, 2, x$1], [3, 4], [x$1]];"],
          ["const x$1 = fn();\n  return [[1n, 2n, x$1], [3n, 4n], [x$1]];"],
          ["if (", " ? ", ".length", "lean_array"], (9 : Nat)),
        ("Tests/SnapshotsMy", "ShareConstValues",
          ["export const same = table;", "export const nested = [table, [4", "export const nested2 = nested;",
           "export const pair = { _1: table, _2: { tag: 1, _1: table } };", "export const empty2 = [];",
           "export const freshConst = (x) => [1", "export const later = [[4", "], table];"],
          ["export const bytes = table;"], ["export const bytes = Uint8Array.of(1, 2, 3);"],
          ["(n) => table", "(x) => table"], 17)] do
      let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"{path}/{file}.lean"]
      let out ← IO.Process.output { cmd := bin.toString, args }
      assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
      for (preset, own) in [("pbo", pboFrags), ("faithful", faithfulFrags)] do
        let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
        for frag in frags ++ own do
          assertEq s!"{file}-{preset}: `{frag}`" true ((js.splitOn frag).length > 1)
        for frag in absent do
          assertEq s!"{file}-{preset}: no `{frag}`" false ((js.splitOn frag).length > 1)
        let run ← IO.Process.output { cmd := "node", args := #[s!"{dir}/{file}-{preset}.check.mjs"] }
        assertEq s!"{file}-{preset}: the checks" "" (if run.exitCode == 0 then "" else run.stdout ++ run.stderr)
        assertEq s!"{file}-{preset}: number of checks" true
          ((run.stdout.splitOn s!"{nChecks} passed, 0 failed").length > 1)

/-- `Tests/SnapshotsPBOPure/BranchSpecialization01.lean`: nested case analyses of an enum of four
    constructors (a derived `BEq`).  The renamings and substitutions read each branch of a case
    analysis several times (`Fin.optAll`); before `Fin.optAllMemo` computed each once, the
    optimiser took minutes on this file (exponential in the nesting).  It must take seconds. -/
def nestedEnumCasesSpec : Spec := describe "Nested enum case analyses" do
  it "BranchSpecialization01 is translated in seconds (needs leanscript)" do
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let dir := s!"{← IO.currentDir}/.lake/build/nestedenum"
    IO.FS.createDirAll dir
    let t0 ← IO.monoMsNow
    let args := #["--quiet", s!"--out-dir={dir}", "Tests/SnapshotsPBOPure/BranchSpecialization01.lean"]
    let out ← IO.Process.output { cmd := bin.toString, args }
    let ms := (← IO.monoMsNow) - t0
    assertEq "leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
    assertEq s!"under 60 s (took {ms} ms)" true (ms < 60000)
    let js ← IO.FS.readFile s!"{dir}/BranchSpecialization01-pbo.js"
    assertEq "test1 is a comparison of the enum" true
      ((js.splitOn "export const test1 = (a) => a === 2;").length > 1)

/-- `InlineReferenceIfThenElse.lean` (the tests decided while Lean is turned into `Term`) and its
    variants `IfThenElseKnownField.lean` (the tests whose answer is known from an enclosing `if`,
    dropped by `Term.knownTests`). -/
def inlineReferenceIfThenElseSpec : Spec := describe "InlineReferenceIfThenElse" do
  it "known tests are dropped (needs node and leanscript)" do
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/inlinerefite"
    IO.FS.createDirAll dir
    -- (directory, file, fragments that must be present, fragments that must be absent)
    for (path, file, frags, absent) in [
        ("Tests/SnapshotsPBOPure", "InlineReferenceIfThenElse",
          ["export const test1 = 42", "export const test2 = 42",
           "export const extern1 = { _1: true, _2: 0"],
          ["if (", " ? "]),
        ("Tests/SnapshotsMy", "IfThenElseKnownField",
          ["export const test3 = (x) => 42", "export const test5 = (x) => x;",
           "export const test6 = (r) => (r._1 ? r._2 : 0",
           "export const test7 = (c, x) => (c ? x : ",
           "export const test8 = (r) => (r._1 ? r._2 : 1",
           "export const test9 = (c, x) => (c ? "],
          ["return c ?", "c ? 0", "c ? 1 :", "c ? 1n"])] do
      let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"{path}/{file}.lean"]
      let out ← IO.Process.output { cmd := bin.toString, args }
      assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
      for preset in ["pbo", "faithful"] do
        let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
        for frag in frags do
          assertEq s!"{file}-{preset}: `{frag}`" true ((js.splitOn frag).length > 1)
        for frag in absent do
          assertEq s!"{file}-{preset}: no `{frag}`" false ((js.splitOn frag).length > 1)
        let run ← IO.Process.output { cmd := "node", args := #[s!"{dir}/{file}-{preset}.check.mjs"] }
        assertEq s!"{file}-{preset}: the checks" "" (if run.exitCode == 0 then "" else run.stdout ++ run.stderr)

/-- `InlineReferenceOpIsTag.lean`: the tests of the constructor of a value built in place (`match
    Cons 1 (fn ()) with | Cons .. => …`, through records too) are decided while Lean is turned
    into `Term` and by `Term.optimize`; the constants read the earlier constants
    (`shareConstValues`), a structure of one field is its field (`extern2 = extern1`).  Its
    results are of a recursive datatype of the source (`MyList Int`): the checks print them to the
    depth `treeShowDepth` (`showTree`), so they are compared with Lean too, and so are those of
    `Tests/SnapshotsMy/RecursiveUnionChecks.lean` (a tree, a value deeper than that depth, unboxed
    structures, a lazy parameter answering a list). -/
def inlineReferenceOpIsTagSpec : Spec := describe "InlineReferenceOpIsTag" do
  -- `--check` on `RecursiveUnionChecks` evaluates its 242 checks in Lean (about 20 s alone),
  -- so under a parallel load the default 30 s are not enough.
  it "the tests of a known constructor are decided (needs node and leanscript)"
      (timeoutMs? := some 120000) do
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/inlinerefistag"
    IO.FS.createDirAll dir
    -- (directory, file, fragments at both presets, at `pbo`, at `faithful`, absent, checks)
    for (path, file, frags, pboFrags, faithfulFrags, absent, nChecks) in [
        ("Tests/SnapshotsPBOPure", "InlineReferenceOpIsTag",
          ["export const extern2 = extern1;", "export const extern3 = { _1: extern1, _2: { tag: 1 } };",
           "export const test5 = test4;", "export const test6 = test4;"],
          ["export const test1 = (fn) => ({\n  tag: 0,\n  _1: 0,\n  _2: { tag: 0, _1: 1, _2: fn() },\n});",
           "export const test4 = { tag: 0, _1: 0, _2: extern1 };"],
          ["export const test1 = (fn) => ({\n  tag: 0,\n  _1: 0n,\n  _2: { tag: 0, _1: 1n, _2: fn() },\n});",
           "export const test4 = { tag: 0, _1: 0n, _2: extern1 };"],
          ["if (", " ? ", ".tag", "=== 0", "switch", "fn_prime("], (13 : Nat)),
        ("Tests/SnapshotsMy", "RecursiveUnionChecks",
          ["export const wrapMirror = ", "export const consForced = (f) => "], [], [], [], 242)] do
      let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"{path}/{file}.lean"]
      let out ← IO.Process.output { cmd := bin.toString, args }
      assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
      for (preset, own) in [("pbo", pboFrags), ("faithful", faithfulFrags)] do
        let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
        for frag in frags ++ own do
          assertEq s!"{file}-{preset}: `{frag}`" true ((js.splitOn frag).length > 1)
        for frag in absent do
          assertEq s!"{file}-{preset}: no `{frag}`" false ((js.splitOn frag).length > 1)
        let run ← IO.Process.output { cmd := "node", args := #[s!"{dir}/{file}-{preset}.check.mjs"] }
        assertEq s!"{file}-{preset}: the checks" "" (if run.exitCode == 0 then "" else run.stdout ++ run.stderr)
        assertEq s!"{file}-{preset}: number of checks" true
          ((run.stdout.splitOn s!"{nChecks} passed, 0 failed").length > 1)

def inlineReferencePrimOpBooleanSpec : Spec := describe "InlineReferencePrimOpBoolean" do
  it "known boolean fields and conditions are decided or simplified (needs node and leanscript)" do
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/inlinerefprimopbool"
    IO.FS.createDirAll dir
    -- (directory, file, fragments at both presets, at `pbo`, at `faithful`, absent, checks)
    for (path, file, frags, pboFrags, faithfulFrags, absent, nChecks) in [
        ("Tests/SnapshotsPBOPure", "InlineReferencePrimOpBoolean", [],
          ["export const test1 = 42;", "export const test6 = 42;",
           "export const extern1 = { _1: true, _2: 0, _3: true, _4: false };"],
          ["export const test1 = 42n;", "export const test6 = 42n;",
           "export const extern1 = { _1: true, _2: 0n, _3: true, _4: false };"],
          ["if (", " ? ", "fn("], (12 : Nat)),
        ("Tests/SnapshotsMy", "PrimOpBooleanKnownField",
          ["export const test7 = (x, g) => x;", "export const test16 = (c, x) => x;",
           "export const test17 = (c) => c;", "export const test18 = (c) => true;",
           "export const test21 = (c, d) => c && d;", "export const test22 = (c, d) => c || !d;",
           "if (f$1 && r._3) {"],
          ["export const test9 = (r) => (r._1 && r._3 ? 42 : 0);",
           "export const test10 = (r) => (r._4 || r._1 ? 42 : r._2);",
           "export const test12 = (c, d, x) => (c && d ? x : 2);",
           "export const test13 = (c, d, x) => (c || d ? 1 : 2);",
           "export const test15 = (c, x) => 7;", "export const test19 = (c, x) => 7;"],
          ["export const test9 = (r) => (r._1 && r._3 ? 42n : 0n);",
           "export const test10 = (r) => (r._4 || r._1 ? 42n : r._2);",
           "export const test12 = (c, d, x) => (c && d ? x : 2n);",
           "export const test13 = (c, d, x) => (c || d ? 1n : 2n);",
           "export const test15 = (c, x) => 7n;", "export const test19 = (c, x) => 7n;"],
          [], 141)] do
      let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"{path}/{file}.lean"]
      let out ← IO.Process.output { cmd := bin.toString, args }
      assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
      for (preset, own) in [("pbo", pboFrags), ("faithful", faithfulFrags)] do
        let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
        for frag in frags ++ own do
          assertEq s!"{file}-{preset}: `{frag}`" true ((js.splitOn frag).length > 1)
        for frag in absent do
          assertEq s!"{file}-{preset}: no `{frag}`" false ((js.splitOn frag).length > 1)
        let run ← IO.Process.output { cmd := "node", args := #[s!"{dir}/{file}-{preset}.check.mjs"] }
        assertEq s!"{file}-{preset}: the checks" "" (if run.exitCode == 0 then "" else run.stdout ++ run.stderr)
        assertEq s!"{file}-{preset}: number of checks" true
          ((run.stdout.splitOn s!"{nChecks} passed, 0 failed").length > 1)

/-- `InlineReferencePrimOpInt.lean`: the arithmetic on the fields of a known record is computed at
    compile time; `if res != k then res else k` is `res` (`Neu.condIsElse`), so
    `externTest = (f) => f(extern)`, reading the constant `extern` instead of building the record
    again (`shareConstValues`, frozen values only).  Its variants `PrimOpIntEqSelect.lean` (the
    other equalities, `Float` kept, an array never shared). -/
def inlineReferencePrimOpIntSpec : Spec := describe "InlineReferencePrimOpInt" do
  it "known arithmetic, equality selects and shared record constants (needs node and leanscript)" do
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/inlinerefprimopint"
    IO.FS.createDirAll dir
    -- (directory, file, fragments at both presets, at `pbo`, at `faithful`, absent, checks)
    for (path, file, frags, pboFrags, faithfulFrags, absent, nChecks) in [
        ("Tests/SnapshotsPBOPure", "InlineReferencePrimOpInt",
          ["export const externTest = (f) => f(extern);"],
          ["export const test1 = 110;", "export const test2 = 88;", "export const test3 = 1089;",
           "export const test4 = 9;", "export const test8 = 9;",
           "export const extern = { _1: 99, _2: 0, _3: 11 };",
           "return x$1 === -2147483648 ? 0 : x$1;"],
          ["export const test1 = 110n;", "export const test4 = 9n;",
           "export const extern = { _1: 99n, _2: 0n, _3: 11n };",
           "return x$1 === -2147483648n ? 0n : x$1;"],
          ["-2147483648 : x$1", "-2147483648n : x$1"], (14 : Nat)),
        ("Tests/SnapshotsMy", "PrimOpIntEqSelect",
          ["export const selInt = (x) => x;", "export const selIntEq = (x) => x;",
           "export const selIntVars = (x, y) => x;", "export const selNat = (n) => n;",
           "export const selString = (s) => s;", "export const selUInt8 = (x) => x;",
           "export const selInt32 = (x) => x;", "export const selCall = (f, x) => f(x);",
           "export const keepFloat = (x) => (x === 0 ? 0 : x);",
           "export const applyOrigin = (f) => f(origin);"],
          ["export const selIntFlip = (x) => 5;", "export const keepOther = (x) => (x === 5 ? 6 : x);",
           "export const applyArr = (f) => f([1, 2, 3]);"],
          ["export const selIntFlip = (x) => 5n;", "export const keepOther = (x) => (x === 5n ? 6n : x);",
           "export const applyArr = (f) => f([1n, 2n, 3n]);"],
          ["f(arr)"], 99)] do
      let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"{path}/{file}.lean"]
      let out ← IO.Process.output { cmd := bin.toString, args }
      assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
      for (preset, own) in [("pbo", pboFrags), ("faithful", faithfulFrags)] do
        let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
        for frag in frags ++ own do
          assertEq s!"{file}-{preset}: `{frag}`" true ((js.splitOn frag).length > 1)
        for frag in absent do
          assertEq s!"{file}-{preset}: no `{frag}`" false ((js.splitOn frag).length > 1)
        let run ← IO.Process.output { cmd := "node", args := #[s!"{dir}/{file}-{preset}.check.mjs"] }
        assertEq s!"{file}-{preset}: the checks" "" (if run.exitCode == 0 then "" else run.stdout ++ run.stderr)
        assertEq s!"{file}-{preset}: number of checks" true
          ((run.stdout.splitOn s!"{nChecks} passed, 0 failed").length > 1)

/-- `InlineReferencePrimOpNumber.lean`: the `Float` arithmetic on the fields of a known record is
    computed at compile time and `externTest = (f) => f(extern)`.  Its faithful variant
    `PrimOpNumberBottom.lean` puts back the test against `bottom` (`-Infinity`) of the PureScript
    original: `if res != k then res else k` is `res` for a `Float` literal `k` that is not a zero
    (`Neu.condIsElse`, `PExpr.floatNonzeroLit`), and stays against `0.0` (`-0.0 == 0.0`). -/
def inlineReferencePrimOpNumberSpec : Spec := describe "InlineReferencePrimOpNumber" do
  it "known float arithmetic and float equality selects (needs node and leanscript)" do
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/inlinerefprimopnumber"
    IO.FS.createDirAll dir
    -- (directory, file, fragments at both presets, absent, checks)
    for (path, file, frags, absent, nChecks) in [
        ("Tests/SnapshotsPBOPure", "InlineReferencePrimOpNumber",
          ["export const localTest = (f) => f({ _1: 99, _2: 0, _3: 11 });",
           "export const test1 = 110;", "export const test2 = 88;", "export const test3 = 1089;",
           "export const test4 = 9;", "export const test8 = 9;",
           "export const extern = { _1: 99, _2: 0, _3: 11 };",
           "export const externTest = (f) => f(extern);"],
          ["if (", " ? ", "fn("], (13 : Nat)),
        ("Tests/SnapshotsMy", "PrimOpNumberBottom",
          ["export const bottom = -Infinity;",
           "return x$1 === -Infinity ? 0 : x$1;",
           "export const test1 = 110;", "export const test4 = 9;", "export const test8 = 9;",
           "export const externTest = (f) => f(extern);",
           "export const selNegInf = (x) => x;", "export const selPosInf = (x) => x;",
           "export const selFive = (x) => x;", "export const selFiveFlip = (x) => 5;",
           "export const selNegHalf = (x) => x;", "export const selCall = (f, x) => f(x);",
           "export const keepZero = (x) => (x === 0 ? 0 : x);",
           "export const keepOther = (x) => (x === 5 ? 6 : x);",
           "export const keepVars = (x, y) => (x === y ? y : x);"],
          ["-Infinity : x$1", "fn("], 92)] do
      let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"{path}/{file}.lean"]
      let out ← IO.Process.output { cmd := bin.toString, args }
      assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
      for preset in ["pbo", "faithful"] do
        let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
        for frag in frags do
          assertEq s!"{file}-{preset}: `{frag}`" true ((js.splitOn frag).length > 1)
        for frag in absent do
          assertEq s!"{file}-{preset}: no `{frag}`" false ((js.splitOn frag).length > 1)
        let run ← IO.Process.output { cmd := "node", args := #[s!"{dir}/{file}-{preset}.check.mjs"] }
        assertEq s!"{file}-{preset}: the checks" "" (if run.exitCode == 0 then "" else run.stdout ++ run.stderr)
        assertEq s!"{file}-{preset}: number of checks" true
          ((run.stdout.splitOn s!"{nChecks} passed, 0 failed").length > 1)

/-- `InlineReferenceRecordUpdate.lean`: the record updates of known records are computed at compile
    time (`extern1 = { _1: 42, _2: 2, _3: 3 }`, `test2 = 3`) and `test1 = (fn) => fn()._3`.  Its
    variants `RecordUpdateKnownField.lean` update an unknown record: the field just set is known
    (`updKnown = (r) => r._3`), the call only one arm needs is made in that arm
    (`Term.sinkArm`), a join point taking a record apart is written at its jumps (`joinCtor`), a
    test whose arms build the same record is dropped (`PExpr.same`), and a field of a loop's
    record passed on unchanged is not assigned (`p$2 = p$2;`). -/
def inlineReferenceRecordUpdateSpec : Spec := describe "InlineReferenceRecordUpdate" do
  it "record updates of known and unknown records (needs node and leanscript)" do
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/inlinerefrecordupdate"
    IO.FS.createDirAll dir
    -- (directory, file, fragments at both presets, absent, checks)
    for (path, file, frags, absent, nChecks) in [
        ("Tests/SnapshotsPBOPure", "InlineReferenceRecordUpdate",
          ["export const test1 = (fn) => fn()._3;",
           "export const fn_prime = { _1: 1",
           "export const extern1 = { _1: 42",
           "export const test2 = 3"],
          ["if (", " ? ", "..."], (3 : Nat)),
        ("Tests/SnapshotsMy", "RecordUpdateKnownField",
          ["export const updKnown = (r) => r._3;",
           "export const updOther = (r) => r._2;",
           "export const updAll = (r, x) => ({ _1: x, _2: x, _3: x });",
           "return fn()._3;",
           "return b ? ",
           "export const updSameBranches = (r, x) => ({ _1: 0"],
          ["const x$1 = fn();", "p$2 = p$2;", "x < 0 ?"], 93)] do
      let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"{path}/{file}.lean"]
      let out ← IO.Process.output { cmd := bin.toString, args }
      assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
      for preset in ["pbo", "faithful"] do
        let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
        for frag in frags do
          assertEq s!"{file}-{preset}: `{frag}`" true ((js.splitOn frag).length > 1)
        for frag in absent do
          assertEq s!"{file}-{preset}: no `{frag}`" false ((js.splitOn frag).length > 1)
        let run ← IO.Process.output { cmd := "node", args := #[s!"{dir}/{file}-{preset}.check.mjs"] }
        assertEq s!"{file}-{preset}: the checks" "" (if run.exitCode == 0 then "" else run.stdout ++ run.stderr)
        assertEq s!"{file}-{preset}: number of checks" true
          ((run.stdout.splitOn s!"{nChecks} passed, 0 failed").length > 1)

/-- `KnownConstructor07.lean`: `test` makes one call and builds the record, as legacy does, and the
    derived `Repr` instance is one expression: each arm of the sign test of `Repr Int` reads the
    field again, and both jump to the join point with the same text (`Branch.sameJumpArg?`,
    `Term.joinSame`), so the join points and the tests disappear in the `Term` optimiser.  Its
    variants `ReprSameJump.lean`: nested and mixed derived instances, `repr` of an `Int`, and a
    test whose two identical arms read the record (`Term.joinViaZip`). -/
def knownConstructor07Spec : Spec := describe "KnownConstructor07" do
  it "one call, derived Repr without tests (needs node and leanscript)" do
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/knownconstructor07"
    IO.FS.createDirAll dir
    -- (directory, file, fragments at both presets, absent, checks)
    for (path, file, frags, absent, nChecks) in [
        ("Tests/SnapshotsPBOPure", "KnownConstructor07",
          ["export const instReprPairBox$repr = (x, prec) => ({",
           "_2: { tag: 3, _1: String(x._1) } }", "_2: { tag: 3, _1: String(x._2) } }",
           "const fy = f(y);"],
          ["if (", " ? ", "const x$1", "let "], (14 : Nat)),
        ("Tests/SnapshotsMy", "ReprSameJump",
          ["export const fmtInt = (x) => ({ tag: 3, _1: String(x) });",
           "export const sameArg = (g, t, c) => g(",
           "export const otherArg = (g, t, c) => {"],
          ["x < 0", "< 0)"], 24)] do
      let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"{path}/{file}.lean"]
      let out ← IO.Process.output { cmd := bin.toString, args }
      assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
      for preset in ["pbo", "faithful"] do
        let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
        for frag in frags do
          assertEq s!"{file}-{preset}: `{frag}`" true ((js.splitOn frag).length > 1)
        for frag in absent do
          assertEq s!"{file}-{preset}: no `{frag}`" false ((js.splitOn frag).length > 1)
        let run ← IO.Process.output { cmd := "node", args := #[s!"{dir}/{file}-{preset}.check.mjs"] }
        assertEq s!"{file}-{preset}: the checks" "" (if run.exitCode == 0 then "" else run.stdout ++ run.stderr)
        assertEq s!"{file}-{preset}: number of checks" true
          ((run.stdout.splitOn s!"{nChecks} passed, 0 failed").length > 1)

def knownConstructors01Spec : Spec := describe "KnownConstructors01" do
  it "a known constructor is folded, loop states unboxed (needs node and leanscript)" do
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/knownconstructors01"
    IO.FS.createDirAll dir
    -- (directory, file, fragments at both presets, absent, checks)
    for (path, file, frags, absent, nChecks) in [
        ("Tests/SnapshotsPBOPure", "KnownConstructors01",
          ["export const test1 = \"b\";"], ["tag:", ".tag", "=>"], (1 : Nat)),
        ("Tests/SnapshotsMy", "KnownCtorOption",
          ["export const mapConstArg = (x) => \"b\";",
           "export const mapFnArg = (f) => f(\"c\");",
           "export const mapBoth = (f, x) => f(x);",
           "export const mapNone = (f) => \"a\";",
           "export const mapTwice = (f, g, x) => g(f(x));",
           "export const exceptKnown = (f, x) => f(x);",
           "  return acc$1;\n};\n\n/**\n * `loopPair`",
           "    let acc$3 = acc$1;", "acc$1 = acc$3;",
           "if (acc$1.tag === 1 && k < i$2) {"],
          ["if (acc$1.tag === 1) {", "return acc$1._1;\n};\n\n/**\n * `loopPair`"], 113)] do
      let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"{path}/{file}.lean"]
      let out ← IO.Process.output { cmd := bin.toString, args }
      assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
      for preset in ["pbo", "faithful"] do
        let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
        for frag in frags do
          assertEq s!"{file}-{preset}: `{frag}`" true ((js.splitOn frag).length > 1)
        for frag in absent do
          assertEq s!"{file}-{preset}: no `{frag}`" false ((js.splitOn frag).length > 1)
        let run ← IO.Process.output { cmd := "node", args := #[s!"{dir}/{file}-{preset}.check.mjs"] }
        assertEq s!"{file}-{preset}: the checks" "" (if run.exitCode == 0 then "" else run.stdout ++ run.stderr)
        assertEq s!"{file}-{preset}: number of checks" true
          ((run.stdout.splitOn s!"{nChecks} passed, 0 failed").length > 1)

/-- `KnownConstructors02.lean`: `test` (a `match` on `some a`, `a : Except Int Int`, each arm
    answering its one field) is `(a) => a._1`, without a test (legacy tests both tags and throws
    `UNREACHABLE`).  Its variants `KnownCtorExcept.lean`: the same field followed by more code
    (`knownThenAdd`, `callAfter`: the join point is written into the arms, which the printer then
    writes once, `JsTerm.Lower.JoinArms`), and a loop whose state is rebuilt by a `match` on
    itself (`countDown`: every arm assigns the loop variable, no temporary). -/
def knownConstructors02Spec : Spec := describe "KnownConstructors02" do
  it "the same field in every arm read once, without a test (needs node and leanscript)" do
    let bin : System.FilePath := ".lake/build/bin/leanscript"
    let built : Bool ← (bin.pathExists : IO Bool)
    if !built then return  -- `lake build leanscript` first
    let node ← try
        some <$> IO.Process.output { cmd := "node", args := #["--version"] }
      catch _ => pure none
    if node.isNone then return  -- no `node`: nothing to run
    let dir := s!"{← IO.currentDir}/.lake/build/knownconstructors02"
    IO.FS.createDirAll dir
    -- (directory, file, fragments at both presets, absent, checks)
    for (path, file, frags, absent, nChecks) in [
        ("Tests/SnapshotsPBOPure", "KnownConstructors02",
          ["export const test = (a) => a._1;"], [".tag", "if (", "throw"], (4 : Nat)),
        ("Tests/SnapshotsMy", "KnownCtorExcept",
          ["export const knownSome = (a) => a._1;",
           "export const knownSum = (a) => a._1;",
           "export const threeFirst = (t) => t._1;",
           "export const knownNested = (a) => a._1;",
           "export const knownViaHelper = (a) => a._1;",
           "export const knownThenAdd = (a, k) => ",
           "export const callAfter = (f, a) => ", "f(a._1)",
           "      p$1 = { tag: 1, _1: ", "      p$1 = { tag: 0, _1: "],
          ["const x$", "let x$", "const { _1: f$", "throw"], 119)] do
      let args := #["--quiet", "--check", s!"--out-dir={dir}", s!"{path}/{file}.lean"]
      let out ← IO.Process.output { cmd := bin.toString, args }
      assertEq s!"{file}: leanscript" "" (if out.exitCode == 0 then "" else out.stderr)
      for preset in ["pbo", "faithful"] do
        let js ← IO.FS.readFile s!"{dir}/{file}-{preset}.js"
        for frag in frags do
          assertEq s!"{file}-{preset}: `{frag}`" true ((js.splitOn frag).length > 1)
        for frag in absent do
          assertEq s!"{file}-{preset}: no `{frag}`" false ((js.splitOn frag).length > 1)
        let run ← IO.Process.output { cmd := "node", args := #[s!"{dir}/{file}-{preset}.check.mjs"] }
        assertEq s!"{file}-{preset}: the checks" "" (if run.exitCode == 0 then "" else run.stdout ++ run.stderr)
        assertEq s!"{file}-{preset}: number of checks" true
          ((run.stdout.splitOn s!"{nChecks} passed, 0 failed").length > 1)

def spec : Spec := do
  tcoSpec
  whileSpec
  quotientSpec
  roseSpec
  optimizeSpec
  appendSpec
  knownLitSpec
  arithSpec
  moreJsSpec
  caseRedBlackTreeSpec
  caseStringSpec
  caseSumSpec
  defaultRulesFunctionSpec
  oneValueResultSpec
  defaultRulesFunctorSpec
  defaultRulesMonoidSpec
  defaultRulesSemigroupSpec
  defaultRulesSemigroup02Spec
  escapeIdentifiersSpec
  esPrecedence01Spec
  esPrecedence02Spec
  esPrecedence03Spec
  esSharedElseSpec
  etaReduceRegressionSpec
  floatLetRegressionSpec
  functionCompose01Spec
  functionCompose02Spec
  functionCompose03Spec
  fusion02Spec
  heterogeneous01Spec
  htmlSpec
  inlineArrayIndexSpec
  inlineCase01Spec
  inlineNeverSpec
  inlineReferenceOpArrayLengthSpec
  nestedEnumCasesSpec
  inlineReferenceIfThenElseSpec
  inlineReferenceOpIsTagSpec
  inlineReferencePrimOpBooleanSpec
  inlineReferencePrimOpIntSpec
  inlineReferencePrimOpNumberSpec
  inlineReferenceRecordUpdateSpec
  knownConstructor07Spec
  knownConstructors01Spec
  knownConstructors02Spec
  wfTermSpec

public def main (args : List String) : IO UInt32 :=
  runSpecFromArgsAndReturnExitCode args spec
