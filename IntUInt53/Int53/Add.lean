import IntUInt53.Int53.Basic

/-!
# Addition on `Int53`

The four variants of addition are inherited from `BoundedInt64`:

* `checked_add`     — `none` on overflow;
* `overflowing_add` — the wrapped value and a flag;
* `wrapping_add`    — wraps modulo `SIZE = 2 ^ 54 - 1` into `[MIN, MAX]`;
* `saturating_add`  — caps at `MAX` above and at `MIN` below.

This file states them with the `Int53` constants in place of the generic
bounds, checks the boundary behaviour concretely, and proves that the raw
machine addition of the underlying `Int64` words is already exact on this
range.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

open BoundedInt64

namespace Int53

/-! ### Overflow -/

theorem addOverflows_iff {a b : Int53} :
    addOverflows a b ↔ (a.toInt + b.toInt < MIN ∨ MAX < a.toInt + b.toInt) := by
  rw [BoundedInt64.addOverflows_iff, hi_toInt, lo_toInt]

/-! ### The checked variant -/

/-- Exactness: whenever `checked_add` succeeds, it returns the exact sum. -/
theorem toInt_of_checked_add {a b c : Int53} (h : checked_add a b = some c) :
    c.toInt = a.toInt + b.toInt := BoundedInt64.toInt_of_checked_add h

/-- `checked_add` fails exactly on the sums that leave `[MIN, MAX]`. -/
theorem checked_add_eq_none_iff {a b : Int53} :
    checked_add a b = none ↔ (a.toInt + b.toInt < MIN ∨ MAX < a.toInt + b.toInt) := by
  rw [BoundedInt64.checked_add_eq_none_iff, addOverflows_iff]

/-- `checked_add` succeeds, with the exact sum, on every sum in `[MIN, MAX]`. -/
theorem checked_add_exact {a b : Int53} (h₁ : MIN ≤ a.toInt + b.toInt)
    (h₂ : a.toInt + b.toInt ≤ MAX) :
    ∃ c, checked_add a b = some c ∧ c.toInt = a.toInt + b.toInt :=
  BoundedInt64.checked_add_of_not_overflows (by rw [addOverflows_iff]; omega)

/-! ### The wrapping variant -/

@[simp] theorem toInt_wrapping_add (a b : Int53) :
    (wrapping_add a b).toInt = MIN + (a.toInt + b.toInt - MIN) % SIZE := by
  rw [BoundedInt64.toInt_wrapping_add, lo_toInt, period_eq]

theorem toInt_wrapping_add_exact {a b : Int53} (h₁ : MIN ≤ a.toInt + b.toInt)
    (h₂ : a.toInt + b.toInt ≤ MAX) : (wrapping_add a b).toInt = a.toInt + b.toInt :=
  BoundedInt64.toInt_wrapping_add_of_not_overflows (by rw [addOverflows_iff]; omega)

/-- Above `MAX`, wrapping addition subtracts one period. -/
theorem toInt_wrapping_add_of_gt_MAX {a b : Int53} (h : MAX < a.toInt + b.toInt) :
    (wrapping_add a b).toInt = a.toInt + b.toInt - SIZE := by
  have ha := le_MAX a
  have hb := le_MAX b
  have hlt : (2 ^ 53 - 1 : Int64).toInt < a.toInt + b.toInt := by rw [hi_toInt]; exact h
  have hle : a.toInt + b.toInt - BoundedInt64.period (-(2 ^ 53 - 1)) (2 ^ 53 - 1)
      ≤ (2 ^ 53 - 1 : Int64).toInt := by
    rw [hi_toInt, period_eq]
    unfold MAX SIZE at *
    omega
  have := BoundedInt64.toInt_wrapping_add_of_gt_hi hlt hle
  rwa [period_eq] at this

/-- Below `MIN`, wrapping addition adds one period. -/
theorem toInt_wrapping_add_of_lt_MIN {a b : Int53} (h : a.toInt + b.toInt < MIN) :
    (wrapping_add a b).toInt = a.toInt + b.toInt + SIZE := by
  have ha := MIN_le a
  have hb := MIN_le b
  have hlt : a.toInt + b.toInt < (-(2 ^ 53 - 1) : Int64).toInt := by rw [lo_toInt]; exact h
  have hle : (-(2 ^ 53 - 1) : Int64).toInt
      ≤ a.toInt + b.toInt + BoundedInt64.period (-(2 ^ 53 - 1)) (2 ^ 53 - 1) := by
    rw [lo_toInt, period_eq]
    unfold MIN SIZE at *
    omega
  have := BoundedInt64.toInt_wrapping_add_of_lt_lo hlt hle
  rwa [period_eq] at this

/-! ### The overflowing variant -/

theorem overflowing_add_snd_iff {a b : Int53} :
    (overflowing_add a b).2 = true ↔
      (a.toInt + b.toInt < MIN ∨ MAX < a.toInt + b.toInt) := by
  rw [BoundedInt64.overflowing_add_snd_iff, addOverflows_iff]

theorem toInt_overflowing_add_exact {a b : Int53} (h₁ : MIN ≤ a.toInt + b.toInt)
    (h₂ : a.toInt + b.toInt ≤ MAX) :
    (overflowing_add a b).1.toInt = a.toInt + b.toInt := by
  rw [overflowing_add_fst]
  exact toInt_wrapping_add_exact h₁ h₂

/-! ### The saturating variant -/

@[simp] theorem toInt_saturating_add (a b : Int53) :
    (saturating_add a b).toInt = max MIN (min (a.toInt + b.toInt) MAX) := by
  rw [BoundedInt64.toInt_saturating_add, hi_toInt, lo_toInt]

theorem toInt_saturating_add_exact {a b : Int53} (h₁ : MIN ≤ a.toInt + b.toInt)
    (h₂ : a.toInt + b.toInt ≤ MAX) : (saturating_add a b).toInt = a.toInt + b.toInt :=
  BoundedInt64.toInt_saturating_add_of_not_overflows (by rw [addOverflows_iff]; omega)

theorem toInt_saturating_add_of_gt_MAX {a b : Int53} (h : MAX < a.toInt + b.toInt) :
    (saturating_add a b).toInt = MAX :=
  BoundedInt64.toInt_saturating_add_of_gt_hi (by rw [hi_toInt]; exact h) |>.trans hi_toInt

theorem toInt_saturating_add_of_lt_MIN {a b : Int53} (h : a.toInt + b.toInt < MIN) :
    (saturating_add a b).toInt = MIN :=
  BoundedInt64.toInt_saturating_add_of_lt_lo (by rw [lo_toInt]; exact h) |>.trans lo_toInt

/-! ### The machine operation is already exact on this range -/

/-- Because `2 * MAX < 2 ^ 63`, the raw `Int64` sum of two `Int53` values never wraps at
the machine level: it denotes the exact sum. -/
theorem toInt_val_add (a b : Int53) : (a.val + b.val).toInt = a.toInt + b.toInt := by
  have ha₁ := MIN_le a
  have ha₂ := le_MAX a
  have hb₁ := MIN_le b
  have hb₂ := le_MAX b
  have ha' : a.val.toInt = a.toInt := rfl
  have hb' : b.val.toInt = b.toInt := rfl
  unfold MIN MAX at *
  rw [Int64.toInt_add, ha', hb']
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- Refinement: when the sum is in range, the value returned by `wrapping_add` is the
raw machine sum of the two underlying words. -/
theorem val_wrapping_add_exact {a b : Int53} (h₁ : MIN ≤ a.toInt + b.toInt)
    (h₂ : a.toInt + b.toInt ≤ MAX) : (wrapping_add a b).val = a.val + b.val := by
  apply Int64.toInt_inj.mp
  rw [toInt_val_add]
  exact toInt_wrapping_add_exact h₁ h₂

/-! ### Exact arithmetic, concretely -/

/-- `1 + 2 = 3`, exactly. -/
theorem one_add_two : checked_add (ofInt 1) (ofInt 2) = some (ofInt 3) := by decide

/-- `(-1) + 1 = 0`, exactly. -/
theorem neg_one_add_one : checked_add (ofInt (-1)) (ofInt 1) = some zero := by decide

/-- `MAX + 1` overflows: the checked variant reports it. -/
theorem checked_add_max_one : checked_add maxVal (ofInt 1) = none := by decide

/-- `MAX + 1` wraps to `MIN`. -/
theorem wrapping_add_max_one : wrapping_add maxVal (ofInt 1) = minVal := by decide

/-- `MAX + 1` saturates at `MAX`. -/
theorem saturating_add_max_one : saturating_add maxVal (ofInt 1) = maxVal := by decide

/-- `MIN + (-1)` wraps to `MAX`. -/
theorem wrapping_add_min_neg_one : wrapping_add minVal (ofInt (-1)) = maxVal := by decide

/-- `MIN + (-1)` saturates at `MIN`. -/
theorem saturating_add_min_neg_one : saturating_add minVal (ofInt (-1)) = minVal := by
  decide

end Int53
