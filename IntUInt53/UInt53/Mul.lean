import IntUInt53.UInt53.Basic

/-!
# Multiplication on `UInt53`

The four variants of multiplication, specialised from `TopBoundedUInt64` to the
`UInt53` constants.

Note the difference with addition and subtraction: the product of two values of
this range can be as large as `(2 ^ 53 - 1) ^ 2`, which does *not* fit in a
machine word.  The generic implementation therefore forms the product in `Nat`,
where it is exact, and applies the chosen overflow behaviour to the true
mathematical product rather than to a truncated one.
-/

set_option autoImplicit false

open TopBoundedUInt64

namespace UInt53

/-! ### Overflow -/

theorem mulOverflows_iff {a b : UInt53} : mulOverflows a b ↔ MAX < a.toNat * b.toNat := by
  rw [TopBoundedUInt64.mulOverflows_iff, hi_toNat]

/-! ### The checked variant -/

/-- Exactness: whenever `checked_mul` succeeds, it returns the exact product. -/
theorem toNat_of_checked_mul {a b c : UInt53} (h : checked_mul a b = some c) :
    c.toNat = a.toNat * b.toNat := TopBoundedUInt64.toNat_of_checked_mul h

/-- `checked_mul` fails exactly on the products that exceed `MAX`. -/
theorem checked_mul_eq_none_iff {a b : UInt53} :
    checked_mul a b = none ↔ MAX < a.toNat * b.toNat := by
  rw [TopBoundedUInt64.checked_mul_eq_none_iff, mulOverflows_iff]

/-- `checked_mul` succeeds, with the exact product, on every product at most `MAX`. -/
theorem checked_mul_exact {a b : UInt53} (h : a.toNat * b.toNat ≤ MAX) :
    ∃ c, checked_mul a b = some c ∧ c.toNat = a.toNat * b.toNat :=
  TopBoundedUInt64.checked_mul_of_not_overflows (by rw [mulOverflows_iff]; omega)

/-! ### The wrapping variant -/

@[simp] theorem toNat_wrapping_mul (a b : UInt53) :
    (wrapping_mul a b).toNat = (a.toNat * b.toNat) % SIZE := by
  rw [TopBoundedUInt64.toNat_wrapping_mul, period_eq]

theorem toNat_wrapping_mul_exact {a b : UInt53} (h : a.toNat * b.toNat ≤ MAX) :
    (wrapping_mul a b).toNat = a.toNat * b.toNat :=
  TopBoundedUInt64.toNat_wrapping_mul_of_not_overflows (by rw [mulOverflows_iff]; omega)

/-! ### The overflowing variant -/

theorem overflowing_mul_snd_iff {a b : UInt53} :
    (overflowing_mul a b).2 = true ↔ MAX < a.toNat * b.toNat := by
  rw [TopBoundedUInt64.overflowing_mul_snd_iff, mulOverflows_iff]

theorem toNat_overflowing_mul_exact {a b : UInt53} (h : a.toNat * b.toNat ≤ MAX) :
    (overflowing_mul a b).1.toNat = a.toNat * b.toNat := by
  rw [overflowing_mul_fst]
  exact toNat_wrapping_mul_exact h

/-! ### The saturating variant -/

@[simp] theorem toNat_saturating_mul (a b : UInt53) :
    (saturating_mul a b).toNat = min (a.toNat * b.toNat) MAX := by
  rw [TopBoundedUInt64.toNat_saturating_mul, hi_toNat]

theorem toNat_saturating_mul_exact {a b : UInt53} (h : a.toNat * b.toNat ≤ MAX) :
    (saturating_mul a b).toNat = a.toNat * b.toNat :=
  TopBoundedUInt64.toNat_saturating_mul_of_not_overflows (by rw [mulOverflows_iff]; omega)

theorem saturating_mul_of_overflow {a b : UInt53} (h : MAX < a.toNat * b.toNat) :
    saturating_mul a b = maxVal :=
  TopBoundedUInt64.saturating_mul_of_overflows (mulOverflows_iff.mpr h)

/-! ### Exact arithmetic, concretely -/

/-- `3 * 4 = 12`, exactly. -/
theorem three_mul_four : checked_mul (ofNat 3) (ofNat 4) = some (ofNat 12) := by decide

/-- `MAX * 2` overflows: the checked variant reports it. -/
theorem checked_mul_max_two : checked_mul maxVal (ofNat 2) = none := by decide

/-- `MAX * 2` saturates at `MAX`. -/
theorem saturating_mul_max_two : saturating_mul maxVal (ofNat 2) = maxVal := by decide

/-- Multiplying by `1` is exact even at the top of the range. -/
theorem checked_mul_max_one : checked_mul maxVal (ofNat 1) = some maxVal := by decide

end UInt53
