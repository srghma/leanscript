module

import Spec.RunSpec
import TermTests.ToTerm.TcoTest
import TermTests.ToTerm.WhileTest
import TermTests.Datatypes.QuotientTest
import TermTests.Datatypes.RoseVariantsTest
import TermTests.Optimize.WFTermTest
import LeanScript.Term.Optimize.Basic
import MoreJsTy.FromTerm

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

/-- The conversion to the JavaScript grammar (`MoreJs.termToJs`) at both presets: the layouts
    the configuration chooses, and the shape of the functions it produces.  (The generated
    JavaScript itself is run against Lean by `scripts/leanscript-snapshots.sh`.) -/
def moreJsSpec : Spec := describe "MoreJsTy" do
  let faithful : MoreJs.JsConfig := {}
  let pbo := MoreJs.JsConfig.presetPBO
  it "Nat is a BigInt (faithful) or a checked UInt53 (pbo)" do
    assertEq "faithful" "nat(bigint)" (MoreJs.lowerScalarPrim faithful .nat).pretty
    assertEq "pbo" "uint53(number)" (MoreJs.lowerScalarPrim pbo .nat).pretty
  let conv (cfg : MoreJs.JsConfig) (name : String) (ps : List String) (ct : ClosedTerm) :
      IO MoreJs.JsFun :=
    match MoreJs.termToJs cfg name name ps ct with
    | .ok (f, _) => pure f
    | .error e => throw (IO.userError s!"{name}: {e}")
  for (cfgName, cfg) in [("faithful", faithful), ("pbo", pbo)] do
    it s!"ack2 converts ({cfgName})" do
      let f ← conv cfg "ack2" ["m", "n"] ⟨[], .nil, _, _, Tco.ack2T⟩
      -- `ack2` is `fun m => nat_rec …`: one parameter, returning a function of `n`
      assertEq "parameters" ["m"] (f.params.map Prod.fst)
      assertEq "exported" true ((f.pretty.splitOn "export function ack2(").length > 1)
    it s!"hyperWhile converts to loops ({cfgName})" do
      let f ← conv cfg "hyperWhile" ["n", "a", "b"] ⟨[], .nil, _, _, Tco.hyperWhileT⟩
      assertEq "a for loop" true ((f.pretty.splitOn "for (").length > 1)
    it s!"bits converts ({cfgName})" do
      let f ← conv cfg "bits" ["n"] ⟨[], .nil, _, _, WhileTest.bitsT⟩
      assertEq "result layout" (MoreJs.lowerScalarPrim cfg .nat).pretty f.ret.pretty

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
