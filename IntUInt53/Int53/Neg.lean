import IntUInt53.Int53.Basic
import IntUInt53.BoundedInt64.Neg

/-!
# Negation and absolute value on `Int53`

Because the range of `Int53` is symmetric — `MIN = -MAX` — negation and the
absolute value are **total**: neither can ever leave the range.  This is the
practical advantage of the symmetric range over a two's-complement one, where
`-MIN` is not representable.

So this file defines the total `Int53.neg` and `Int53.abs`, installs `-a` as
notation for the former, and proves that all four variants of each operation
agree with it.
-/

set_option autoImplicit false

open BoundedInt64

namespace Int53

theorem lo_toInt_eq_neg_hi_toInt' :
    (-(2 ^ 53 - 1) : Int64).toInt = -((2 ^ 53 - 1 : Int64).toInt) := by decide

/-- Negation never overflows on `Int53`. -/
theorem not_negOverflows (a : Int53) : ¬ negOverflows a :=
  BoundedInt64.not_negOverflows_of_symm lo_toInt_eq_neg_hi_toInt' a

/-- The absolute value never overflows on `Int53`. -/
theorem not_absOverflows (a : Int53) : ¬ absOverflows a :=
  BoundedInt64.not_absOverflows_of_symm lo_toInt_eq_neg_hi_toInt' a

/-- Total negation on `Int53`. -/
def neg (a : Int53) : Int53 :=
  BoundedInt64.ofIntMem _ _ (-a.toInt)
    (by rw [lo_toInt]; have h := le_MAX a; unfold MIN MAX at *; omega)
    (by rw [hi_toInt]; have h := MIN_le a; unfold MIN MAX at *; omega)

instance : Neg Int53 := ⟨neg⟩

@[simp] theorem toInt_neg (a : Int53) : (-a).toInt = -a.toInt := by
  show (neg a).toInt = -a.toInt
  unfold neg
  rw [BoundedInt64.toInt_ofIntMem]

/-- Total absolute value on `Int53`. -/
def abs (a : Int53) : Int53 :=
  BoundedInt64.ofIntMem _ _ (a.toInt.natAbs)
    (by rw [lo_toInt]; have h := le_MAX a; have h' := MIN_le a; unfold MIN MAX at *; omega)
    (by rw [hi_toInt]; have h := le_MAX a; have h' := MIN_le a; unfold MIN MAX at *; omega)

@[simp] theorem toInt_abs (a : Int53) : (abs a).toInt = a.toInt.natAbs := by
  unfold abs; rw [BoundedInt64.toInt_ofIntMem]

/-- Negation is an involution. -/
@[simp] theorem neg_neg (a : Int53) : - -a = a := by
  apply BoundedInt64.ext
  rw [toInt_neg, toInt_neg, Int.neg_neg]

/-- The absolute value is nonnegative. -/
theorem zero_le_toInt_abs (a : Int53) : 0 ≤ (abs a).toInt := by
  rw [toInt_abs]
  exact Int.natCast_nonneg _

/-- The absolute value ignores the sign. -/
theorem abs_neg (a : Int53) : abs (-a) = abs a := by
  apply BoundedInt64.ext
  rw [toInt_abs, toInt_abs, toInt_neg, Int.natAbs_neg]

/-! ### All four variants agree with the total operations -/

/-- All four variants of negation return the exact value `-a`. -/
theorem neg_variants_exact (a : Int53) :
    (∃ c, checked_neg a = some c ∧ c.toInt = -a.toInt) ∧
      (wrapping_neg a).toInt = -a.toInt ∧
      (overflowing_neg a).1.toInt = -a.toInt ∧
      (overflowing_neg a).2 = false ∧
      (saturating_neg a).toInt = -a.toInt :=
  BoundedInt64.neg_variants_agree (not_negOverflows a)

/-- All four variants of the absolute value return the exact value `|a|`. -/
theorem abs_variants_exact (a : Int53) :
    (∃ c, checked_abs a = some c ∧ c.toInt = a.toInt.natAbs) ∧
      (wrapping_abs a).toInt = a.toInt.natAbs ∧
      (overflowing_abs a).1.toInt = a.toInt.natAbs ∧
      (overflowing_abs a).2 = false ∧
      (saturating_abs a).toInt = a.toInt.natAbs :=
  BoundedInt64.abs_variants_agree (not_absOverflows a)

/-! ### Exact arithmetic, concretely -/

/-- Negating the smallest value is exact: `-MIN = MAX`. -/
theorem neg_minVal : -minVal = maxVal := by
  apply BoundedInt64.ext
  rw [toInt_neg, toInt_minVal, toInt_maxVal]
  decide

/-- Negating the largest value is exact: `-MAX = MIN`. -/
theorem neg_maxVal : -maxVal = minVal := by
  apply BoundedInt64.ext
  rw [toInt_neg, toInt_minVal, toInt_maxVal]
  decide

/-- `|-3| = 3`. -/
theorem abs_neg_three : abs (ofInt (-3)) = ofInt 3 := by
  apply BoundedInt64.ext
  rw [toInt_abs, toInt_ofInt, toInt_ofInt]
  decide

end Int53
