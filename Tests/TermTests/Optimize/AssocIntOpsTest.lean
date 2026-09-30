module

public import LeanScript.Term.Optimize.Basic
public import LeanScript.Term.Pretty
public import LeanScript.Term.Build
public meta import LeanScript.TermElab.ToTerm
public meta import LeanScript.Term.Pretty
public meta import LeanScript.Term.Optimize.Basic

@[expose] public section

set_option autoImplicit false

/-!
# `Tests/SnapshotsPBOPure/AssocIntOps.lean`, formally

The six functions of the snapshot, translated to `Term` (`#leanscript_to_term`) and optimised
(`Term.optimizeN 3`, the pipeline's `Term → Term` phase, whose chain normalisation is
`Term.arithWalk`).  For each function `testN` this file proves:

* `testN_optimized_run`: for **every** input `x`, the optimised statement computes the closed
  form (`x * 4 + 10`, `x * 8 + 28`, `x ^ 4 * 24`, `x ^ 8 * 5040`).  The proof goes through the
  general theorem `Term.optimizeN_run` (the optimiser never changes the result) and a proof
  about the Lean function itself (`testN_eq`), so it holds symbolically, not just on samples.
* `testN_optimized_pretty`: the optimised statement is exactly the two-operation statement
  that `Tests/SnapshotsPBOPure/AssocIntOps-Term-optimized.txt` shows (checked with
  `native_decide`, since the printer is compiled code).
* `numIntOps_optimized` / `numIntOps_unoptimized`: every optimised statement writes 2 integer
  operations, where the elaborated ones write 7 (`test1`, `test2`, `test4`, `test5`) or 14
  (`test3`, `test6`).  For comparison, the legacy backend's
  `Tests/SnapshotsPBOPure/legacy-backend/AssocIntOps.js` writes 5 or 10 arithmetic operations,
  each followed by a `| 0`.
-/

namespace AssocIntOpsTest

open LeanScript

/-- The number of integer operations (`lean_int_…` calls) in a printed statement. -/
def numIntOps (s : String) : Nat := (s.splitOn "lean_int_").length - 1

/-- The printed form of an optimised `Int → Int` function whose body returns `body`. -/
def printedIntFn (body : String) : String :=
  "val k1 [1] : (Int → Int) := fun x2 [1] : Int => (closed)\n  ret " ++ body ++ "\nret k1"

def test1 (x : Int) : Int :=
  1 + (((((2 + x) + x) + x) + x) + 3) + 4

def test1T := #leanscript_to_term test1

def test2 (x : Int) : Int :=
  1 + (2 + (x + (x + (x + (x + 3))))) + 4

def test2T := #leanscript_to_term test2

def test3 (x : Int) : Int :=
  1 + (2 + (x + (x + (x + (x + 3))))) + 4 + (((((5 + x) + x) + x) + x) + 6) + 7

def test3T := #leanscript_to_term test3

def test4 (x : Int) : Int :=
  1 * (((((2 * x) * x) * x) * x) * 3) * 4

def test4T := #leanscript_to_term test4

def test5 (x : Int) : Int :=
  1 * (2 * (x * (x * (x * (x * 3))))) * 4

def test5T := #leanscript_to_term test5

def test6 (x : Int) : Int :=
  1 * (2 * (x * (x * (x * (x * 3))))) * 4 * (((((5 * x) * x) * x) * x) * 6) * 7

def test6T := #leanscript_to_term test6

/-- `test1 x = x * 4 + 10` for every `x`. -/
theorem test1_eq (x : Int) : test1 x = x * 4 + 10 := by
  unfold test1; omega

/-- The optimised translation of `test1` computes `x * 4 + 10`, for every `x`. -/
theorem test1_optimized_run (x : Int) :
    ((test1T (Δ := DSig.nil)).optimizeN 3).run x = x * 4 + 10 := by
  rw [Term.optimizeN_run]
  exact test1_eq x

/-- The optimised translation of `test1` is `lean_int_add(lean_int_mul(x2, 4), 10)`. -/
theorem test1_optimized_pretty :
    ((test1T (Δ := DSig.nil)).optimizeN 3).pretty =
      printedIntFn "lean_int_add(lean_int_mul(x2, 4), 10)" := by
  native_decide

/-- `test2 x = x * 4 + 10` for every `x`. -/
theorem test2_eq (x : Int) : test2 x = x * 4 + 10 := by
  unfold test2; omega

/-- The optimised translation of `test2` computes `x * 4 + 10`, for every `x`. -/
theorem test2_optimized_run (x : Int) :
    ((test2T (Δ := DSig.nil)).optimizeN 3).run x = x * 4 + 10 := by
  rw [Term.optimizeN_run]
  exact test2_eq x

/-- The optimised translation of `test2` is `lean_int_add(lean_int_mul(x2, 4), 10)`. -/
theorem test2_optimized_pretty :
    ((test2T (Δ := DSig.nil)).optimizeN 3).pretty =
      printedIntFn "lean_int_add(lean_int_mul(x2, 4), 10)" := by
  native_decide

/-- `test3 x = x * 8 + 28` for every `x`. -/
theorem test3_eq (x : Int) : test3 x = x * 8 + 28 := by
  unfold test3; omega

/-- The optimised translation of `test3` computes `x * 8 + 28`, for every `x`. -/
theorem test3_optimized_run (x : Int) :
    ((test3T (Δ := DSig.nil)).optimizeN 3).run x = x * 8 + 28 := by
  rw [Term.optimizeN_run]
  exact test3_eq x

/-- The optimised translation of `test3` is `lean_int_add(lean_int_mul(x2, 8), 28)`. -/
theorem test3_optimized_pretty :
    ((test3T (Δ := DSig.nil)).optimizeN 3).pretty =
      printedIntFn "lean_int_add(lean_int_mul(x2, 8), 28)" := by
  native_decide

/-- `test4 x = x ^ 4 * 24` for every `x`. -/
theorem test4_eq (x : Int) : test4 x = x ^ 4 * 24 := by
  have h : x ^ 4 * 24 = x * x * x * x * (1 * 2 * 3 * 4) := by
    simp only [Int.pow_succ, Int.pow_zero, Int.one_mul]; rfl
  rw [h]; unfold test4; ac_rfl

/-- The optimised translation of `test4` computes `x ^ 4 * 24`, for every `x`. -/
theorem test4_optimized_run (x : Int) :
    ((test4T (Δ := DSig.nil)).optimizeN 3).run x = x ^ 4 * 24 := by
  rw [Term.optimizeN_run]
  exact test4_eq x

/-- The optimised translation of `test4` is `lean_int_mul(lean_int_pow(x2, 4), 24)`. -/
theorem test4_optimized_pretty :
    ((test4T (Δ := DSig.nil)).optimizeN 3).pretty =
      printedIntFn "lean_int_mul(lean_int_pow(x2, 4), 24)" := by
  native_decide

/-- `test5 x = x ^ 4 * 24` for every `x`. -/
theorem test5_eq (x : Int) : test5 x = x ^ 4 * 24 := by
  have h : x ^ 4 * 24 = x * x * x * x * (1 * 2 * 3 * 4) := by
    simp only [Int.pow_succ, Int.pow_zero, Int.one_mul]; rfl
  rw [h]; unfold test5; ac_rfl

/-- The optimised translation of `test5` computes `x ^ 4 * 24`, for every `x`. -/
theorem test5_optimized_run (x : Int) :
    ((test5T (Δ := DSig.nil)).optimizeN 3).run x = x ^ 4 * 24 := by
  rw [Term.optimizeN_run]
  exact test5_eq x

/-- The optimised translation of `test5` is `lean_int_mul(lean_int_pow(x2, 4), 24)`. -/
theorem test5_optimized_pretty :
    ((test5T (Δ := DSig.nil)).optimizeN 3).pretty =
      printedIntFn "lean_int_mul(lean_int_pow(x2, 4), 24)" := by
  native_decide

/-- `test6 x = x ^ 8 * 5040` for every `x`. -/
theorem test6_eq (x : Int) : test6 x = x ^ 8 * 5040 := by
  have h : x ^ 8 * 5040 = x * x * x * x * x * x * x * x * (1 * 2 * 3 * 4 * 5 * 6 * 7) := by
    simp only [Int.pow_succ, Int.pow_zero, Int.one_mul]; rfl
  rw [h]; unfold test6; ac_rfl

/-- The optimised translation of `test6` computes `x ^ 8 * 5040`, for every `x`. -/
theorem test6_optimized_run (x : Int) :
    ((test6T (Δ := DSig.nil)).optimizeN 3).run x = x ^ 8 * 5040 := by
  rw [Term.optimizeN_run]
  exact test6_eq x

/-- The optimised translation of `test6` is `lean_int_mul(lean_int_pow(x2, 8), 5040)`. -/
theorem test6_optimized_pretty :
    ((test6T (Δ := DSig.nil)).optimizeN 3).pretty =
      printedIntFn "lean_int_mul(lean_int_pow(x2, 8), 5040)" := by
  native_decide

/-- Every optimised statement writes two integer operations. -/
theorem numIntOps_optimized :
    numIntOps ((test1T (Δ := DSig.nil)).optimizeN 3).pretty = 2 ∧
    numIntOps ((test2T (Δ := DSig.nil)).optimizeN 3).pretty = 2 ∧
    numIntOps ((test3T (Δ := DSig.nil)).optimizeN 3).pretty = 2 ∧
    numIntOps ((test4T (Δ := DSig.nil)).optimizeN 3).pretty = 2 ∧
    numIntOps ((test5T (Δ := DSig.nil)).optimizeN 3).pretty = 2 ∧
    numIntOps ((test6T (Δ := DSig.nil)).optimizeN 3).pretty = 2 := by
  native_decide

/-- The elaborated (unoptimised) statements write 7 or 14 integer operations. -/
theorem numIntOps_unoptimized :
    numIntOps (test1T (Δ := DSig.nil)).pretty = 7 ∧
    numIntOps (test2T (Δ := DSig.nil)).pretty = 7 ∧
    numIntOps (test3T (Δ := DSig.nil)).pretty = 14 ∧
    numIntOps (test4T (Δ := DSig.nil)).pretty = 7 ∧
    numIntOps (test5T (Δ := DSig.nil)).pretty = 7 ∧
    numIntOps (test6T (Δ := DSig.nil)).pretty = 14 := by
  native_decide

end AssocIntOpsTest

end
