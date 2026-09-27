import IntUInt53.UInt53.Basic

/-!
# Addition on `UInt53`

The four variants of addition are inherited from `TopBoundedUInt64`:

* `checked_add`     — `none` on overflow;
* `overflowing_add` — the wrapped value and a flag;
* `wrapping_add`    — wraps modulo `SIZE = 2 ^ 53`;
* `saturating_add`  — caps at `MAX = 9007199254740991`.

This file states them with the `UInt53` constants in place of the generic
bound, checks the boundary behaviour concretely, and proves that the raw
machine addition of the underlying `UInt64` words is already exact on this
range — the `53 < 64` head room means no wrapping can happen at the machine
level before the chosen overflow behaviour is applied.
-/

set_option autoImplicit false

open TopBoundedUInt64

namespace UInt53

/-! ### Overflow -/

theorem addOverflows_iff {a b : UInt53} : addOverflows a b ↔ MAX < a.toNat + b.toNat := by
  rw [TopBoundedUInt64.addOverflows_iff, hi_toNat]

/-! ### The checked variant -/

/-- Exactness: whenever `checked_add` succeeds, it returns the exact sum. -/
theorem toNat_of_checked_add {a b c : UInt53} (h : checked_add a b = some c) :
    c.toNat = a.toNat + b.toNat := TopBoundedUInt64.toNat_of_checked_add h

/-- `checked_add` fails exactly on the sums that exceed `MAX`. -/
theorem checked_add_eq_none_iff {a b : UInt53} :
    checked_add a b = none ↔ MAX < a.toNat + b.toNat := by
  rw [TopBoundedUInt64.checked_add_eq_none_iff, addOverflows_iff]

/-- `checked_add` succeeds, with the exact sum, on every sum that is at most `MAX`. -/
theorem checked_add_exact {a b : UInt53} (h : a.toNat + b.toNat ≤ MAX) :
    ∃ c, checked_add a b = some c ∧ c.toNat = a.toNat + b.toNat :=
  TopBoundedUInt64.checked_add_of_not_overflows (by rw [addOverflows_iff]; omega)

/-! ### The wrapping variant -/

@[simp] theorem toNat_wrapping_add (a b : UInt53) :
    (wrapping_add a b).toNat = (a.toNat + b.toNat) % SIZE := by
  rw [TopBoundedUInt64.toNat_wrapping_add, period_eq]

theorem toNat_wrapping_add_exact {a b : UInt53} (h : a.toNat + b.toNat ≤ MAX) :
    (wrapping_add a b).toNat = a.toNat + b.toNat :=
  TopBoundedUInt64.toNat_wrapping_add_of_not_overflows (by rw [addOverflows_iff]; omega)

/-! ### The overflowing variant -/

theorem overflowing_add_snd_iff {a b : UInt53} :
    (overflowing_add a b).2 = true ↔ MAX < a.toNat + b.toNat := by
  rw [TopBoundedUInt64.overflowing_add_snd_iff, addOverflows_iff]

theorem toNat_overflowing_add_exact {a b : UInt53} (h : a.toNat + b.toNat ≤ MAX) :
    (overflowing_add a b).1.toNat = a.toNat + b.toNat := by
  rw [overflowing_add_fst]
  exact toNat_wrapping_add_exact h

/-! ### The saturating variant -/

@[simp] theorem toNat_saturating_add (a b : UInt53) :
    (saturating_add a b).toNat = min (a.toNat + b.toNat) MAX := by
  rw [TopBoundedUInt64.toNat_saturating_add, hi_toNat]

theorem toNat_saturating_add_exact {a b : UInt53} (h : a.toNat + b.toNat ≤ MAX) :
    (saturating_add a b).toNat = a.toNat + b.toNat :=
  TopBoundedUInt64.toNat_saturating_add_of_not_overflows (by rw [addOverflows_iff]; omega)

theorem saturating_add_of_overflow {a b : UInt53} (h : MAX < a.toNat + b.toNat) :
    saturating_add a b = maxVal :=
  TopBoundedUInt64.saturating_add_of_overflows (addOverflows_iff.mpr h)

/-! ### The machine operation is already exact on this range -/

/-- Because `2 * MAX < 2 ^ 64`, the raw `UInt64` sum of two `UInt53` values never wraps
at the machine level: it denotes the exact sum. -/
theorem toNat_val_add (a b : UInt53) : (a.val + b.val).toNat = a.toNat + b.toNat := by
  have ha := le_MAX a
  have hb := le_MAX b
  unfold MAX at ha hb
  have ha' : a.val.toNat = a.toNat := rfl
  have hb' : b.val.toNat = b.toNat := rfl
  rw [UInt64.toNat_add, ha', hb']
  exact Nat.mod_eq_of_lt (by omega)

/-- Refinement: when the sum is in range, the value returned by `wrapping_add` is the
raw machine sum of the two underlying words. -/
theorem val_wrapping_add_exact {a b : UInt53} (h : a.toNat + b.toNat ≤ MAX) :
    (wrapping_add a b).val = a.val + b.val := by
  apply UInt64.toNat_inj.mp
  rw [toNat_val_add]
  exact toNat_wrapping_add_exact h

/-! ### Exact arithmetic, concretely -/

/-- `1 + 2 = 3`, exactly. -/
theorem one_add_two : checked_add (ofNat 1) (ofNat 2) = some (ofNat 3) := by decide

/-- The largest value plus one overflows: the checked variant reports it. -/
theorem checked_add_max_one : checked_add maxVal (ofNat 1) = none := by decide

/-- The largest value plus one wraps to `0`. -/
theorem wrapping_add_max_one : wrapping_add maxVal (ofNat 1) = minVal := by decide

/-- The largest value plus one saturates at `MAX`. -/
theorem saturating_add_max_one : saturating_add maxVal (ofNat 1) = maxVal := by decide

/-- The overflowing variant returns the wrapped value together with `true`. -/
theorem overflowing_add_max_one : overflowing_add maxVal (ofNat 1) = (minVal, true) := by
  decide

end UInt53
