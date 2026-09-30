module

public import LeanScript.Term.Optimize.Basic
public import LeanScript.Term.Optimize.FloatReassoc
public import LeanScript.Term.Pretty
public import LeanScript.Term.Build
public meta import LeanScript.TermElab.ToTerm
public meta import LeanScript.Term.Pretty
public meta import LeanScript.Term.Optimize.Basic
public meta import LeanScript.Term.Optimize.FloatReassoc

@[expose] public section

set_option autoImplicit false

/-!
# `Tests/SnapshotsPBOPure/AssocNumberOps.lean`, formally

The six `Float` functions of the snapshot, translated to `Term` (`#leanscript_to_term`, which
now translates float literals) and optimised (`Term.optimizeN 3`).

* `testN_optimized_run`: the optimised translation computes what the translation computes, for
  every input (the general `Term.optimizeN_run`).
* `testN_optimized_pretty`: the optimised statement is exactly the one of
  `AssocNumberOps-Term-optimized.txt`: the unit operand `1.0 *` of `test4`–`test6` is dropped
  (`Neu.floatUnit`, exact), and nothing else changes — the chains are **not** regrouped.
* **Why not regroup** as the legacy backend does (`legacy-backend/AssocNumberOps.js`:
  `3.0 + x + x + x + x + 7.0`): that changes the result.  `test1_ne_legacy` is a concrete input
  (`x = 3/7`) at which `test1` and the legacy body differ, and
  `test1_floatReassoc_changes_result` shows that the opt-in pass `Term.floatReassoc` (which
  reproduces the legacy output, `leanscript --float-reassoc`) changes the value of the
  translation of `test1` at that input.  These are checked with `native_decide` (the float
  operations run as compiled code).
-/

namespace AssocNumberOpsTest

open LeanScript

/-- The printed form of an optimised `Float → Float` function whose body returns `body`. -/
def printedFloatFn (body : String) : String :=
  "val k1 [1] : (Float → Float) := fun x2 [ω] : Float => (closed)\n  ret " ++ body ++ "\nret k1"

def test1 (x : Float) : Float :=
  1.0 + (((((2.0 + x) + x) + x) + x) + 3.0) + 4.0

def test1T := #leanscript_to_term test1

def test2 (x : Float) : Float :=
  1.0 + (2.0 + (x + (x + (x + (x + 3.0))))) + 4.0

def test2T := #leanscript_to_term test2

def test3 (x : Float) : Float :=
  1.0 + (2.0 + (x + (x + (x + (x + 3.0))))) + 4.0 + (((((5.0 + x) + x) + x) + x) + 6.0) + 7.0

def test3T := #leanscript_to_term test3

def test4 (x : Float) : Float :=
  1.0 * (((((2.0 * x) * x) * x) * x) * 3.0) * 4.0

def test4T := #leanscript_to_term test4

def test5 (x : Float) : Float :=
  1.0 * (2.0 * (x * (x * (x * (x * 3.0))))) * 4.0

def test5T := #leanscript_to_term test5

def test6 (x : Float) : Float :=
  1.0 * (2.0 * (x * (x * (x * (x * 3.0))))) * 4.0 * (((((5.0 * x) * x) * x) * x) * 6.0) * 7.0

def test6T := #leanscript_to_term test6

/-! ## The optimiser keeps the value -/

theorem test1_optimized_run (x : HashableFloat) :
    ((test1T (Δ := DSig.nil)).optimizeN 3).run x = (test1T (Δ := DSig.nil)).run x := by
  rw [Term.optimizeN_run]

theorem test4_optimized_run (x : HashableFloat) :
    ((test4T (Δ := DSig.nil)).optimizeN 3).run x = (test4T (Δ := DSig.nil)).run x := by
  rw [Term.optimizeN_run]

/-! ## The optimised statements -/

/-- `test1`: unchanged (no unit operand; the chain is not regrouped). -/
theorem test1_optimized_pretty :
    ((test1T (Δ := DSig.nil)).optimizeN 3).pretty =
      printedFloatFn "lean_float_add(lean_float_add(1.000000, lean_float_add(lean_float_add(lean_float_add(lean_float_add(lean_float_add(2.000000, x2), x2), x2), x2), 3.000000)), 4.000000)" := by
  native_decide

/-- `test4`: the unit operand `1.0 *` is dropped. -/
theorem test4_optimized_pretty :
    ((test4T (Δ := DSig.nil)).optimizeN 3).pretty =
      printedFloatFn "lean_float_mul(lean_float_mul(lean_float_mul(lean_float_mul(lean_float_mul(lean_float_mul(2.000000, x2), x2), x2), x2), 3.000000), 4.000000)" := by
  native_decide

/-- `test5`: the unit operand `1.0 *` is dropped. -/
theorem test5_optimized_pretty :
    ((test5T (Δ := DSig.nil)).optimizeN 3).pretty =
      printedFloatFn "lean_float_mul(lean_float_mul(2.000000, lean_float_mul(x2, lean_float_mul(x2, lean_float_mul(x2, lean_float_mul(x2, 3.000000))))), 4.000000)" := by
  native_decide

/-- `test6`: the unit operand `1.0 *` is dropped. -/
theorem test6_optimized_pretty :
    ((test6T (Δ := DSig.nil)).optimizeN 3).pretty =
      printedFloatFn "lean_float_mul(lean_float_mul(lean_float_mul(lean_float_mul(2.000000, lean_float_mul(x2, lean_float_mul(x2, lean_float_mul(x2, lean_float_mul(x2, 3.000000))))), 4.000000), lean_float_mul(lean_float_mul(lean_float_mul(lean_float_mul(lean_float_mul(5.000000, x2), x2), x2), x2), 6.000000)), 7.000000)" := by
  native_decide

/-! ## Regrouping float chains changes results -/

/-- The value of a closed `Float → Float` translation at an input. -/
def runF {o : Lvl} (t : Term DSig.nil 0 [] [] (.fn (.prim .float) (.prim .float)) [] o)
    (x : HashableFloat) : HashableFloat :=
  t.run x

/-- The body the legacy backend writes for `test1`. -/
def legacyTest1 (x : Float) : Float := 3.0 + x + x + x + x + 7.0

/-- `test1` and the legacy backend's body differ at `x = 3/7`. -/
theorem test1_ne_legacy : test1 (3.0 / 7.0) ≠ legacyTest1 (3.0 / 7.0) := by
  native_decide

/-- The opt-in pass `Term.floatReassoc` rewrites the optimised `test1` into the legacy body
    `3.0 + x + x + x + x + 7.0`… -/
theorem test1_floatReassoc_pretty :
    ((test1T (Δ := DSig.nil)).optimizeN 3).floatReassoc.pretty =
      printedFloatFn "lean_float_add(lean_float_add(lean_float_add(lean_float_add(lean_float_add(3.000000, x2), x2), x2), x2), 7.000000)" := by
  native_decide

/-- …and so it **changes the result** of the translation (at `x = 3/7`): unlike the passes
    of `Term.optimize`, it does not preserve `Term.eval`. -/
theorem test1_floatReassoc_changes_result :
    runF ((test1T (Δ := DSig.nil)).optimizeN 3).floatReassoc (HashableFloat.normalize (3.0 / 7.0)) ≠
      runF (test1T (Δ := DSig.nil)) (HashableFloat.normalize (3.0 / 7.0)) := by
  native_decide

end AssocNumberOpsTest

end
