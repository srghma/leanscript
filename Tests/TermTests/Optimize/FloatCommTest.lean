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
# `Tests/SnapshotsPBOPure/EsPrecedence02.lean`, formally

The five `Float` functions of the snapshot, and a few more, translated to `Term`
(`#leanscript_to_term`) and optimised (`Term.optimizeN 3`).  `Neu.floatComm`
(`LeanScript.Term.Optimize.FloatComm`) puts the operand that would need parentheses in
JavaScript on the left of a `+` or `*` (IEEE `+` and `*` are commutative, bit for bit), and
regroups `(b - b) + (y + z)` as `((b - b) + y) + z` (exact too, since `b - b` is `+0` or
`NaN`).  So every function prints without parentheses, as the legacy backend's output
(`legacy-backend/EsPrecedence02.js`) does, but without changing any result:

| function | Lean | JavaScript |
|---|---|---|
| `test1` | `a + (a + (a + a))` | `a + a + a + a` |
| `test2` | `((a + a) + a) + a` | `a + a + a + a` |
| `test3` | `a + (a + (a - a))` | `a - a + a + a` |
| `test4` | `((a - a) + a) + a` | `a - a + a + a` |
| `test5` | `(a - a) + (a + a)` | `a - a + a + a` |

* `testN_optimized_run`: the optimised translation computes what the translation computes, for
  every input (the general `Term.optimizeN_run`).
* `testN_optimized_pretty`: the optimised statement (as in `EsPrecedence02-Term-optimized.txt`).
* `Tests/Main.lean` (`esPrecedence02Spec`) runs the optimised statements, compiled, on sample
  floats, and runs `leanscript --check` and node on the snapshot.
-/

namespace FloatCommTest

open LeanScript

/-- The printed form of an optimised `Float → Float` function whose body returns `body`. -/
def printedFloatFn (body : String) : String :=
  "val k1 [1] : (Float → Float) := fun x2 [ω] : Float => (closed)\n  ret " ++ body ++ "\nret k1"

def test1 (a : Float) : Float := a + (a + (a + a))
def test2 (a : Float) : Float := ((a + a) + a) + a
def test3 (a : Float) : Float := a + (a + (a - a))
def test4 (a : Float) : Float := ((a - a) + a) + a
def test5 (a : Float) : Float := (a - a) + (a + a)

/-- `x * (y / z)`: `y / z * x`. -/
def mulDiv (a : Float) : Float := a * (a / 3.0)

/-- `(y + z) + (b - b)`, the mirror of `test5`: `a - a + a + 2`. -/
def subSelfRight (a : Float) : Float := (a + 2.0) + (a - a)

/-- `x - (y + z)` is left alone: `-` is not commutative. -/
def subAdd (a : Float) : Float := a - (a + 2.0)

def test1T := #leanscript_to_term test1
def test2T := #leanscript_to_term test2
def test3T := #leanscript_to_term test3
def test4T := #leanscript_to_term test4
def test5T := #leanscript_to_term test5
def mulDivT := #leanscript_to_term mulDiv
def subSelfRightT := #leanscript_to_term subSelfRight
def subAddT := #leanscript_to_term subAdd

/-! ## The optimiser keeps the value -/

theorem test1_optimized_run (x : HashableFloat) :
    ((test1T (Δ := DSig.nil)).optimizeN 3).run x = (test1T (Δ := DSig.nil)).run x := by
  rw [Term.optimizeN_run]

theorem test3_optimized_run (x : HashableFloat) :
    ((test3T (Δ := DSig.nil)).optimizeN 3).run x = (test3T (Δ := DSig.nil)).run x := by
  rw [Term.optimizeN_run]

theorem test5_optimized_run (x : HashableFloat) :
    ((test5T (Δ := DSig.nil)).optimizeN 3).run x = (test5T (Δ := DSig.nil)).run x := by
  rw [Term.optimizeN_run]

/-! ## The optimised statements -/

/-- `a + (a + (a + a))`: both additions commuted. -/
theorem test1_optimized_pretty :
    ((test1T (Δ := DSig.nil)).optimizeN 3).pretty =
      printedFloatFn "lean_float_add(lean_float_add(lean_float_add(x2, x2), x2), x2)" := by
  native_decide

/-- `((a + a) + a) + a`: unchanged. -/
theorem test2_optimized_pretty :
    ((test2T (Δ := DSig.nil)).optimizeN 3).pretty =
      printedFloatFn "lean_float_add(lean_float_add(lean_float_add(x2, x2), x2), x2)" := by
  native_decide

/-- `a + (a + (a - a))`: both additions commuted. -/
theorem test3_optimized_pretty :
    ((test3T (Δ := DSig.nil)).optimizeN 3).pretty =
      printedFloatFn "lean_float_add(lean_float_add(lean_float_sub(x2, x2), x2), x2)" := by
  native_decide

/-- `((a - a) + a) + a`: unchanged. -/
theorem test4_optimized_pretty :
    ((test4T (Δ := DSig.nil)).optimizeN 3).pretty =
      printedFloatFn "lean_float_add(lean_float_add(lean_float_sub(x2, x2), x2), x2)" := by
  native_decide

/-- `(a - a) + (a + a)`: regrouped as `((a - a) + a) + a`. -/
theorem test5_optimized_pretty :
    ((test5T (Δ := DSig.nil)).optimizeN 3).pretty =
      printedFloatFn "lean_float_add(lean_float_add(lean_float_sub(x2, x2), x2), x2)" := by
  native_decide

/-- `a * (a / 3)`: commuted. -/
theorem mulDiv_optimized_pretty :
    ((mulDivT (Δ := DSig.nil)).optimizeN 3).pretty =
      printedFloatFn "lean_float_mul(lean_float_div(x2, 3.000000), x2)" := by
  native_decide

/-- `(a + 2) + (a - a)`: regrouped as `((a - a) + a) + 2`. -/
theorem subSelfRight_optimized_pretty :
    ((subSelfRightT (Δ := DSig.nil)).optimizeN 3).pretty =
      printedFloatFn "lean_float_add(lean_float_add(lean_float_sub(x2, x2), x2), 2.000000)" := by
  native_decide

/-- `a - (a + 2)`: unchanged. -/
theorem subAdd_optimized_pretty :
    ((subAddT (Δ := DSig.nil)).optimizeN 3).pretty =
      printedFloatFn "lean_float_sub(x2, lean_float_add(x2, 2.000000))" := by
  native_decide

end FloatCommTest

end
