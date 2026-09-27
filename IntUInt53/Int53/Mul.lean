import IntUInt53.Int53.Basic

/-!
# Multiplication on `Int53`

The four variants of multiplication, specialised from `BoundedInt64` to the
`Int53` constants.

As on `UInt53`, the product of two in-range values need not fit in a machine
word — `MAX * MAX` is about `8.1 · 10 ^ 31` — so the generic implementation
forms the product in `Int`, where it is exact, and applies the chosen overflow
behaviour to the true mathematical product.  There is consequently no machine
refinement theorem here: the raw `Int64` product would already have wrapped.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

open BoundedInt64

namespace Int53

/-! ### Overflow -/

theorem mulOverflows_iff {a b : Int53} :
    mulOverflows a b ↔ (a.toInt * b.toInt < MIN ∨ MAX < a.toInt * b.toInt) := by
  rw [BoundedInt64.mulOverflows_iff, hi_toInt, lo_toInt]

/-! ### The checked variant -/

/-- Exactness: whenever `checked_mul` succeeds, it returns the exact product. -/
theorem toInt_of_checked_mul {a b c : Int53} (h : checked_mul a b = some c) :
    c.toInt = a.toInt * b.toInt := BoundedInt64.toInt_of_checked_mul h

/-- `checked_mul` fails exactly on the products that leave `[MIN, MAX]`. -/
theorem checked_mul_eq_none_iff {a b : Int53} :
    checked_mul a b = none ↔ (a.toInt * b.toInt < MIN ∨ MAX < a.toInt * b.toInt) := by
  rw [BoundedInt64.checked_mul_eq_none_iff, mulOverflows_iff]

/-- `checked_mul` succeeds, with the exact product, on every product in range. -/
theorem checked_mul_exact {a b : Int53} (h₁ : MIN ≤ a.toInt * b.toInt)
    (h₂ : a.toInt * b.toInt ≤ MAX) :
    ∃ c, checked_mul a b = some c ∧ c.toInt = a.toInt * b.toInt :=
  BoundedInt64.checked_mul_of_not_overflows (by rw [mulOverflows_iff]; omega)

/-! ### The wrapping variant -/

@[simp] theorem toInt_wrapping_mul (a b : Int53) :
    (wrapping_mul a b).toInt = MIN + (a.toInt * b.toInt - MIN) % SIZE := by
  rw [BoundedInt64.toInt_wrapping_mul, lo_toInt, period_eq]

theorem toInt_wrapping_mul_exact {a b : Int53} (h₁ : MIN ≤ a.toInt * b.toInt)
    (h₂ : a.toInt * b.toInt ≤ MAX) : (wrapping_mul a b).toInt = a.toInt * b.toInt :=
  BoundedInt64.toInt_wrapping_mul_of_not_overflows (by rw [mulOverflows_iff]; omega)

/-! ### The overflowing variant -/

theorem overflowing_mul_snd_iff {a b : Int53} :
    (overflowing_mul a b).2 = true ↔
      (a.toInt * b.toInt < MIN ∨ MAX < a.toInt * b.toInt) := by
  rw [BoundedInt64.overflowing_mul_snd_iff, mulOverflows_iff]

theorem toInt_overflowing_mul_exact {a b : Int53} (h₁ : MIN ≤ a.toInt * b.toInt)
    (h₂ : a.toInt * b.toInt ≤ MAX) :
    (overflowing_mul a b).1.toInt = a.toInt * b.toInt := by
  rw [overflowing_mul_fst]
  exact toInt_wrapping_mul_exact h₁ h₂

/-! ### The saturating variant -/

@[simp] theorem toInt_saturating_mul (a b : Int53) :
    (saturating_mul a b).toInt = max MIN (min (a.toInt * b.toInt) MAX) := by
  rw [BoundedInt64.toInt_saturating_mul, hi_toInt, lo_toInt]

theorem toInt_saturating_mul_exact {a b : Int53} (h₁ : MIN ≤ a.toInt * b.toInt)
    (h₂ : a.toInt * b.toInt ≤ MAX) : (saturating_mul a b).toInt = a.toInt * b.toInt :=
  BoundedInt64.toInt_saturating_mul_of_not_overflows (by rw [mulOverflows_iff]; omega)

theorem toInt_saturating_mul_of_gt_MAX {a b : Int53} (h : MAX < a.toInt * b.toInt) :
    (saturating_mul a b).toInt = MAX :=
  BoundedInt64.toInt_saturating_mul_of_gt_hi (by rw [hi_toInt]; exact h) |>.trans hi_toInt

theorem toInt_saturating_mul_of_lt_MIN {a b : Int53} (h : a.toInt * b.toInt < MIN) :
    (saturating_mul a b).toInt = MIN :=
  BoundedInt64.toInt_saturating_mul_of_lt_lo (by rw [lo_toInt]; exact h) |>.trans lo_toInt

/-! ### Exact arithmetic, concretely -/

/-- `3 * 4 = 12`, exactly. -/
theorem three_mul_four : checked_mul (ofInt 3) (ofInt 4) = some (ofInt 12) := by decide

/-- `(-3) * 4 = -12`, exactly. -/
theorem neg_three_mul_four :
    checked_mul (ofInt (-3)) (ofInt 4) = some (ofInt (-12)) := by decide

/-- `MAX * 2` overflows: the checked variant reports it. -/
theorem checked_mul_max_two : checked_mul maxVal (ofInt 2) = none := by decide

/-- `MAX * 2` saturates at `MAX`. -/
theorem saturating_mul_max_two : saturating_mul maxVal (ofInt 2) = maxVal := by decide

/-- `MAX * (-2)` saturates at `MIN`. -/
theorem saturating_mul_max_neg_two :
    saturating_mul maxVal (ofInt (-2)) = minVal := by decide

/-- Multiplying by `1` is exact even at the top of the range. -/
theorem checked_mul_max_one : checked_mul maxVal (ofInt 1) = some maxVal := by decide

end Int53
