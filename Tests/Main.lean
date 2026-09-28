module

import Spec.RunSpec
import TermTests.ToTerm.TcoTest
import TermTests.ToTerm.WhileTest
import TermTests.Datatypes.QuotientTest
import TermTests.Datatypes.RoseVariantsTest
import TermTests.Optimize.WFTermTest
import LeanScript.Term.Optimize.Basic
import JsTerm.FromTerm
import JsTerm.Hoist
import ExternCatalogue

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
def moreJsSpec : Spec := describe "JsTerm" do
  let faithful : MoreJs.JsConfig := {}
  let pbo := MoreJs.JsConfig.presetPBO
  it "Nat is a BigInt (faithful) or a checked UInt53 (pbo)" do
    assertEq "faithful" "nat(bigint)" (MoreJs.lowerScalarPrim faithful .nat).pretty
    assertEq "pbo" "uint53(number)" (MoreJs.lowerScalarPrim pbo .nat).pretty
  it "records and unions are objects" do
    assertEq "record" "{ _1: a, _2: b }" ((MoreJs.recordObj [.var "a", .var "b"]).pretty "")
    assertEq "nullary constructor" "{ tag: 0 }" ((MoreJs.unionObj 0 []).pretty "")
    assertEq "constructor" "{ tag: 2, _1: a }" ((MoreJs.unionObj 2 [.var "a"]).pretty "")
    assertEq "record layout" "{ _1: nat(bigint), _2: boolean }"
      (MoreJs.JsTerm.record [.nat, .bool]).pretty
    assertEq "union layout" "({ tag: 0 } | { tag: 1, _1: nat(bigint) })"
      (MoreJs.JsTerm.union [[], [.nat]]).pretty
  it "externs call the functions of the runtime modules" do
    let (e, fs) := MoreJs.lowerExtern .trusting "lean_nat_pow" [.nat, .nat] .nat (some .nat)
      [.var "x", .var "y"]
    assertEq "call" "$lean_nat_pow(x, y)" (e.pretty "")
    assertEq "functions" [("lean_runtime_nat_bigint.mjs", "$lean_nat_pow")]
      (fs.map fun (f : MoreJs.RtFn) => (f.file.fileName, f.name))
    let (e, fs) := MoreJs.lowerExtern .trusting "lean_nat_pow" [.uint53, .uint53] .uint53
      (some .nat) [.var "x", .var "y"]
    assertEq "call (number)" "$lean_nat_pow(x, y)" (e.pretty "")
    assertEq "functions (number)" [("lean_runtime_nat_num.mjs", "$lean_nat_pow")]
      (fs.map fun (f : MoreJs.RtFn) => (f.file.fileName, f.name))
    -- a runtime without the function: the call throws when it is evaluated
    let (e, fs) := MoreJs.lowerExtern ⟨fun _ _ => false⟩ "lean_nat_pow" [.nat, .nat] .nat
      (some .nat) [.var "x", .var "y"]
    assertEq "unimplemented" true (((e.pretty "").splitOn "$lean_extern_unimplemented").length > 1)
    assertEq "unimplemented functions" ["$lean_extern_unimplemented"] (fs.map (·.name : MoreJs.RtFn → String))
  it "a Float.Model is the number of the Float it models" do
    assertEq "Float.Model" "float" (MoreJs.lowerScalarPrim faithful .floatModel).pretty
    assertEq "Float32.Model" "float32" (MoreJs.lowerScalarPrim pbo .float32Model).pretty
    match MoreJs.primLit pbo .floatModel (Float.toModel 2.5) with
    | .ok e => assertEq "literal" "25e-1" (e.pretty "")
    | .error err => throw (IO.userError err)
    let (e, hs) := MoreJs.lowerExtern .trusting "lean_float_to_bits__Float_toModel" [.float]
      .float none [.var "x"]
    assertEq "toModel" "x" (e.pretty "")
    assertEq "toModel helpers" 0 hs.length
  it "appends of arrays become one array literal" do
    let body : List MoreJs.JsStmt :=
      [.const "k" (.array [.lit (.str "a")]),
       .const "x" (.array [.spread (.var "arr"), .spread (.array [.lit (.str "c")])]),
       .const "y" (.array [.spread (.var "k"), .spread (.var "x")]),
       .ret (.var "y")]
    match MoreJs.inlineArrays body with
    | [.ret e] => assertEq "literal" "[\"a\", ...arr, \"c\"]" (e.pretty "")
    | ss => throw (IO.userError s!"not one return: {ss.length} statements")
    -- a literal used inside a loop is not moved into it
    let loop : List MoreJs.JsStmt :=
      [.const "k" (.array [.lit (.str "a")]),
       .forOf "e" (.var "xs") [.expr (.array [.spread (.var "k")])]]
    assertEq "loop" 2 (MoreJs.inlineArrays loop).length
  it "an array only one variable refers to is updated in place" do
    let push (a : String) (v : Nat) : MoreJs.JsExpr := .helper "$lean_array_push" [.var a, .lit (.int v)]
    -- `a` is a fresh array read once: the push mutates it
    let body : List MoreJs.JsStmt :=
      [.const "a" (.array []), .const "b" (push "a" 1), .const "c" (push "b" 2), .ret (.var "c")]
    assertEq "owned" ["$lean_array_push_inplace"] (MoreJs.calledHelpers (MoreJs.inPlaceStmts body))
    -- a parameter may be referred to by the caller: it is copied
    let param : List MoreJs.JsStmt := [.const "b" (push "p" 1), .ret (.var "b")]
    assertEq "parameter" ["$lean_array_push"] (MoreJs.calledHelpers (MoreJs.inPlaceStmts param))
    -- `a` is read twice: the first push must copy it, the second may mutate its own result
    let shared : List MoreJs.JsStmt :=
      [.const "a" (.array []), .const "b" (push "a" 1), .const "c" (push "b" 2),
       .ret (.array [.var "a", .var "c"])]
    match MoreJs.inPlaceStmts shared with
    | [_, .const _ e1, .const _ e2, _] =>
      assertEq "shared (copy)" ["$lean_array_push"] e1.calls
      assertEq "shared (own result)" ["$lean_array_push_inplace"] e2.calls
    | _ => throw (IO.userError "shared: unexpected statements")
    -- an array read in a closure is copied
    let closure : List MoreJs.JsStmt :=
      [.const "a" (.array []), .const "f" (.arrow [] [.ret (.var "a")]),
       .const "b" (push "a" 1), .ret (.array [.var "b", .var "f"])]
    assertEq "closure" ["$lean_array_push"] (MoreJs.calledHelpers (MoreJs.inPlaceStmts closure))
  it "constants are computed once, at the top of the module" do
    let f : MoreJs.JsFun :=
      { name := "f", leanName := "f", params := ["x"], ret := .bool,
        body := [.ret (.cond (.var "x") (MoreJs.unionObj 0 [])
          (.array [MoreJs.unionObj 1 [.var "x"], MoreJs.unionObj 0 [],
                   MoreJs.unionObj 1 [.lit (.bigint 3)], .array []]))] }
    let (consts, funs) := MoreJs.hoistConsts [] [f]
    assertEq "constants" [("$tag0", "{ tag: 0 }"), ("$k2", "{ tag: 1, _1: 3n }")]
      (consts.map fun ((n, e) : String × MoreJs.JsExpr) => (n, e.pretty ""))
    let body : String := match funs with
      | [g] => match g.body with
        | [.ret e] => e.pretty ""
        | _ => "?"
      | _ => "?"
    assertEq "body" "(x ? $tag0 : [{ tag: 1, _1: x }, $tag0, $k2, []])" body
  it "the runtime modules export the functions of every implemented extern" do
    let srcs ← MoreJs.RtFile.all.mapM fun (f : MoreJs.RtFile) => do
      return (f.fileName, ← IO.FS.readFile (System.FilePath.mk "runtime" / f.fileName))
    let rt := MoreJs.Runtime.ofSources srcs
    -- the two modules of a knob export the same functions
    for k in [MoreJs.RtKnob.nat, .int, .uint64, .int64, .bitvec] do
      let names (big : Bool) : List String :=
        MoreJs.exportedNames ((srcs.lookup (MoreJs.RtFile.knob k big).fileName).getD "")
      assertEq s!"{k.name}: bigint and num export the same functions" (names true) (names false)
    for (preset, table) in [("faithful", ExternCatalogue.faithful), ("pbo", ExternCatalogue.pbo)] do
      let mut missing : List String := []
      for (name, argTys, resTy, knob, implemented) in table do
        if implemented then
          let args := (List.range argTys.length).map fun i => MoreJs.JsExpr.var s!"a{i}"
          let (_, fs) := MoreJs.lowerExtern rt name argTys resTy knob args
          if fs.any (fun (f : MoreJs.RtFn) => f.name == "$lean_extern_unimplemented" || !rt.has f.file f.name) then
            missing := name :: missing
      assertEq s!"{preset}: implemented externs without a runtime function" [] missing.reverse
  let conv (cfg : MoreJs.JsConfig) (name : String) (ps : List String) (ct : ClosedTerm) :
      IO MoreJs.JsFun :=
    match MoreJs.termToJs cfg .trusting name name ps ct with
    | .ok (f, _) => pure f
    | .error e => throw (IO.userError s!"{name}: {e}")
  for (cfgName, cfg) in [("faithful", faithful), ("pbo", pbo)] do
    it s!"ack2 converts ({cfgName})" do
      let f ← conv cfg "ack2" ["m", "n"] ⟨[], .nil, _, _, Tco.ack2T⟩
      -- `ack2` is `fun m => nat_rec …`: one parameter, returning a function of `n`
      assertEq "parameters" ["m"] f.params
      assertEq "exported" true ((f.pretty.splitOn "export const ack2 = (m) =>").length > 1)
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
