import IntUInt53.UInt53.Basic

/-!
# Subtraction on `UInt53`

The four variants of subtraction, specialised from `TopBoundedUInt64` to the
`UInt53` constants, together with the concrete boundary behaviour at `0` and a
refinement theorem for the raw machine subtraction.
-/

set_option autoImplicit false

open TopBoundedUInt64

namespace UInt53

/-! ### Overflow -/

theorem subOverflows_iff {a b : UInt53} : subOverflows a b ↔ a.toNat < b.toNat := Iff.rfl

/-! ### The checked variant -/

/-- Exactness: whenever `checked_sub` succeeds, it returns the exact difference. -/
theorem toNat_of_checked_sub {a b c : UInt53} (h : checked_sub a b = some c) :
    c.toNat = a.toNat - b.toNat := TopBoundedUInt64.toNat_of_checked_sub h

/-- `checked_sub` fails exactly when the difference would be negative. -/
theorem checked_sub_eq_none_iff {a b : UInt53} :
    checked_sub a b = none ↔ a.toNat < b.toNat :=
  TopBoundedUInt64.checked_sub_eq_none_iff

/-- `checked_sub` succeeds, with the exact difference, whenever `b ≤ a`. -/
theorem checked_sub_exact {a b : UInt53} (h : b.toNat ≤ a.toNat) :
    ∃ c, checked_sub a b = some c ∧ c.toNat = a.toNat - b.toNat :=
  TopBoundedUInt64.checked_sub_of_not_overflows (by rw [subOverflows_iff]; omega)

/-! ### The wrapping variant -/

@[simp] theorem toNat_wrapping_sub (a b : UInt53) :
    (wrapping_sub a b).toNat = (a.toNat + SIZE - b.toNat) % SIZE := by
  rw [TopBoundedUInt64.toNat_wrapping_sub, period_eq]

theorem toNat_wrapping_sub_exact {a b : UInt53} (h : b.toNat ≤ a.toNat) :
    (wrapping_sub a b).toNat = a.toNat - b.toNat :=
  TopBoundedUInt64.toNat_wrapping_sub_of_not_overflows (by rw [subOverflows_iff]; omega)

/-! ### The overflowing variant -/

theorem overflowing_sub_snd_iff {a b : UInt53} :
    (overflowing_sub a b).2 = true ↔ a.toNat < b.toNat :=
  TopBoundedUInt64.overflowing_sub_snd_iff

theorem toNat_overflowing_sub_exact {a b : UInt53} (h : b.toNat ≤ a.toNat) :
    (overflowing_sub a b).1.toNat = a.toNat - b.toNat := by
  rw [overflowing_sub_fst]
  exact toNat_wrapping_sub_exact h

/-! ### The saturating variant -/

@[simp] theorem toNat_saturating_sub (a b : UInt53) :
    (saturating_sub a b).toNat = a.toNat - b.toNat :=
  TopBoundedUInt64.toNat_saturating_sub a b

theorem saturating_sub_of_underflow {a b : UInt53} (h : a.toNat < b.toNat) :
    saturating_sub a b = minVal :=
  TopBoundedUInt64.saturating_sub_of_overflows (subOverflows_iff.mpr h)

/-! ### The machine operation is already exact on this range -/

/-- When `b ≤ a`, the raw `UInt64` difference of the underlying words denotes the exact
difference. -/
theorem toNat_val_sub {a b : UInt53} (h : b.toNat ≤ a.toNat) :
    (a.val - b.val).toNat = a.toNat - b.toNat := by
  have ha := le_MAX a
  have ha' : a.val.toNat = a.toNat := rfl
  have hb' : b.val.toNat = b.toNat := rfl
  unfold MAX at ha
  rw [UInt64.toNat_sub, ha', hb']
  have hrw : 2 ^ 64 - b.toNat + a.toNat = (a.toNat - b.toNat) + 2 ^ 64 := by omega
  rw [hrw, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- Refinement: when `b ≤ a`, `wrapping_sub` returns the raw machine difference. -/
theorem val_wrapping_sub_exact {a b : UInt53} (h : b.toNat ≤ a.toNat) :
    (wrapping_sub a b).val = a.val - b.val := by
  apply UInt64.toNat_inj.mp
  rw [toNat_val_sub h]
  exact toNat_wrapping_sub_exact h

/-! ### Exact arithmetic, concretely -/

/-- `3 - 2 = 1`, exactly. -/
theorem three_sub_two : checked_sub (ofNat 3) (ofNat 2) = some (ofNat 1) := by decide

/-- `0 - 1` underflows: the checked variant reports it. -/
theorem checked_sub_zero_one : checked_sub minVal (ofNat 1) = none := by decide

/-- `0 - 1` wraps to `MAX`. -/
theorem wrapping_sub_zero_one : wrapping_sub minVal (ofNat 1) = maxVal := by decide

/-- `0 - 1` saturates at `0`. -/
theorem saturating_sub_zero_one : saturating_sub minVal (ofNat 1) = minVal := by decide

/-- The overflowing variant returns the wrapped value together with `true`. -/
theorem overflowing_sub_zero_one : overflowing_sub minVal (ofNat 1) = (maxVal, true) := by
  decide

end UInt53
