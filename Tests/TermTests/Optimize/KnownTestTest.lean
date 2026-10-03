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
# `Tests/SnapshotsPBOPure/InlineReferenceIfThenElse.lean` and its variants, formally

The definitions of the snapshot and of `Tests/SnapshotsMy/IfThenElseKnownField.lean` (copies),
translated to `Term` (`#leanscript_to_term`) and optimised (`Term.optimizeN 3`).

* `test1`, `test2` (the snapshot): every `if` is on a value known when the code is translated,
  so the translation is already `ret 42` (`test1_translation_pretty`, …), the constant `42` of
  purescript-backend-optimizer's `legacy-backend/InlineReferenceIfThenElse.js`.
* `test7`–`test10` (the variants): a condition tested again inside an arm of an `if` on the same
  condition.  `Term.knownTests` (`LeanScript.Term.Optimize.KnownTest`) drops the inner tests:
  `test7_knownTests_pretty` shows the statement after that one rewrite (one `if` left of three),
  `test7_optimized_pretty` … after the whole optimiser (one conditional, `c ? x : x + 2`).
* `…_translation_run`: the translation computes the Lean function, for every input.
* `…_optimized_run`, `test7_knownTests_run`: so do the optimised statements (by the general
  `Term.optimizeN_run` and `Term.knownTests_eval`).
-/

namespace KnownTestTest

open LeanScript

/-! ## The definitions (copies of the snapshots) -/

structure RecC where
  c : Bool

structure RecB where
  b : RecC

structure RecA where
  a : RecB
  d : Int

def fn {α : Type} (_r : α) : Int := 0

def test1 : Int :=
  let rec1 : RecA := { a := { b := { c := true } }, d := fn () }
  if rec1.a.b.c then 42 else fn rec1

def extern1 : RecA :=
  { a := { b := { c := true } }, d := fn () }

def test2 : Int :=
  if extern1.a.b.c then 42 else 99

def test7 (c : Bool) (x : Int) : Int :=
  let rec1 : RecA := { a := { b := { c := c } }, d := x }
  if rec1.a.b.c then (if rec1.a.b.c then x else 0) else (if rec1.a.b.c then 1 else x + 2)

def test8 (r : RecA) : Int :=
  if r.a.b.c then (if r.a.b.c then r.d else 0) else 1

def test9 (c : Bool) (x : Int) : Int :=
  if !c then (if c then 1 else x) else (if c then x + 1 else 2)

def test10 (c : Bool) (x : Int) : Int :=
  if c then
    let y := x * x
    if c then y + 1 else y
  else 0

def test1T := #leanscript_to_term test1
def test2T := #leanscript_to_term test2
def test7T := #leanscript_to_term test7
def test8T := #leanscript_to_term test8
def test9T := #leanscript_to_term test9
def test10T := #leanscript_to_term test10

/-! ## The snapshot: decided while Lean is turned into `Term` -/

theorem test1_translation_pretty : (test1T (Δ := DSig.nil)).pretty = "ret 42" := by native_decide
theorem test2_translation_pretty : (test2T (Δ := DSig.nil)).pretty = "ret 42" := by native_decide

theorem test1_translation_run : (test1T (Δ := DSig.nil)).run = test1 := rfl
theorem test2_translation_run : (test2T (Δ := DSig.nil)).run = test2 := rfl

theorem test1_optimized_run : ((test1T (Δ := DSig.nil)).optimizeN 3).run = (42 : Int) := by
  rw [Term.optimizeN_run]; rfl
theorem test2_optimized_run : ((test2T (Δ := DSig.nil)).optimizeN 3).run = (42 : Int) := by
  rw [Term.optimizeN_run]; rfl

/-! ## The variants: the translations compute the Lean functions -/

theorem test7_translation_run (c : Bool) (x : Int) :
    (test7T (Δ := DSig.nil)).run c x = test7 c x := by
  cases c <;> rfl

theorem test8_translation_run (r : RecA) :
    (test8T (Δ := DSig.nil)).run (r.a.b.c, r.d) = test8 r := by
  rcases r with ⟨⟨⟨c⟩⟩, d⟩; cases c <;> rfl

theorem test9_translation_run (c : Bool) (x : Int) :
    (test9T (Δ := DSig.nil)).run c x = test9 c x := by
  cases c <;> rfl

theorem test10_translation_run (c : Bool) (x : Int) :
    (test10T (Δ := DSig.nil)).run c x = test10 c x := by
  cases c <;> rfl

/-! ## The known tests dropped -/

/-- The translation of `test7`: three tests of `x2`. -/
def test7Printed : String :=
  "\n".intercalate [
    "val k1 [ω] : (Bool → (Int → Int)) := fun x2 [ω] : Bool => (closed)",
    "  val k3 [ω] : (Int → Int) := fun x4 [ω] : Int => (open)",
    "    if x2 then",
    "      if x2 then",
    "        ret x4",
    "      else",
    "        ret 0",
    "    else",
    "      if x2 then",
    "        ret 1",
    "      else",
    "        ret lean_int_add(x4, 2)",
    "  ret k3",
    "ret k1"]

theorem test7_translation_pretty : (test7T (Δ := DSig.nil)).pretty = test7Printed := by
  native_decide

/-- `Term.knownTests` alone: the inner tests of `x2` are dropped, one test is left. -/
def test7KnownTestsPrinted : String :=
  "\n".intercalate [
    "val k1 [ω] : (Bool → (Int → Int)) := fun x2 [ω] : Bool => (closed)",
    "  val k3 [ω] : (Int → Int) := fun x4 [ω] : Int => (open)",
    "    if x2 then",
    "      ret x4",
    "    else",
    "      ret lean_int_add(x4, 2)",
    "  ret k3",
    "ret k1"]

theorem test7_knownTests_pretty :
    (test7T (Δ := DSig.nil)).knownTests.pretty = test7KnownTestsPrinted := by
  native_decide

theorem test7_knownTests_run (c : Bool) (x : Int) :
    (test7T (Δ := DSig.nil)).knownTests.run c x = test7 c x := by
  rw [Term.knownTests_run]; exact test7_translation_run c x

/-! ## The whole optimiser -/

/-- `test7`: one conditional, `c ? x : x + 2`. -/
def test7OptimizedPrinted : String :=
  "\n".intercalate [
    "val k1 [1] : (Bool → (Int → Int)) := fun x2 [ω] : Bool => (closed)",
    "  val k3 [1] : (Int → Int) := fun x4 [ω] : Int => (open)",
    "    ret cond(x2, x4, lean_int_add(x4, 2))",
    "  ret k3",
    "ret k1"]

theorem test7_optimized_pretty :
    ((test7T (Δ := DSig.nil)).optimizeN 3).pretty = test7OptimizedPrinted := by
  native_decide

/-- `test8`: the field tested twice is tested once, `r._1 ? r._2 : 1`. -/
def test8OptimizedPrinted : String :=
  "\n".intercalate [
    "val k1 [1] : ((Bool × Int) → Int) := fun x2 [1] : (Bool × Int) => (closed)",
    "  let ⟨f3 [1] : Bool, f4 [1] : Int⟩ := x2",
    "  ret cond(f3, f4, 1)",
    "ret k1"]

theorem test8_optimized_pretty :
    ((test8T (Δ := DSig.nil)).optimizeN 3).pretty = test8OptimizedPrinted := by
  native_decide

/-- `test9`: inside `if !c` the value of `c` is known, `c ? x + 1 : x`. -/
def test9OptimizedPrinted : String :=
  "\n".intercalate [
    "val k1 [1] : (Bool → (Int → Int)) := fun x2 [ω] : Bool => (closed)",
    "  val k3 [1] : (Int → Int) := fun x4 [ω] : Int => (open)",
    "    ret cond(x2, lean_int_add(x4, 1), x4)",
    "  ret k3",
    "ret k1"]

theorem test9_optimized_pretty :
    ((test9T (Δ := DSig.nil)).optimizeN 3).pretty = test9OptimizedPrinted := by
  native_decide

/-- `test10`: the inner test under a `let` is dropped. -/
def test10OptimizedPrinted : String :=
  "\n".intercalate [
    "val k1 [1] : (Bool → (Int → Int)) := fun x2 [ω] : Bool => (closed)",
    "  val k3 [1] : (Int → Int) := fun x4 [ω] : Int => (open)",
    "    if x2 then",
    "      let x5 [1] : Int := share lean_int_mul(x4, x4)",
    "      ret lean_int_add(x5, 1)",
    "    else",
    "      ret 0",
    "  ret k3",
    "ret k1"]

theorem test10_optimized_pretty :
    ((test10T (Δ := DSig.nil)).optimizeN 3).pretty = test10OptimizedPrinted := by
  native_decide

theorem test7_optimized_run (c : Bool) (x : Int) :
    ((test7T (Δ := DSig.nil)).optimizeN 3).run c x = test7 c x := by
  rw [Term.optimizeN_run]; exact test7_translation_run c x

theorem test8_optimized_run (r : RecA) :
    ((test8T (Δ := DSig.nil)).optimizeN 3).run (r.a.b.c, r.d) = test8 r := by
  rw [Term.optimizeN_run]; exact test8_translation_run r

theorem test9_optimized_run (c : Bool) (x : Int) :
    ((test9T (Δ := DSig.nil)).optimizeN 3).run c x = test9 c x := by
  rw [Term.optimizeN_run]; exact test9_translation_run c x

theorem test10_optimized_run (c : Bool) (x : Int) :
    ((test10T (Δ := DSig.nil)).optimizeN 3).run c x = test10 c x := by
  rw [Term.optimizeN_run]; exact test10_translation_run c x

end KnownTestTest

end
