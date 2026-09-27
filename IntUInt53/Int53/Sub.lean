import IntUInt53.Int53.Basic

/-!
# Subtraction on `Int53`

The four variants of subtraction, specialised from `BoundedInt64` to the
`Int53` constants, with the concrete boundary behaviour and the refinement
theorem for the raw machine subtraction.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

open BoundedInt64

namespace Int53

/-! ### Overflow -/

theorem subOverflows_iff {a b : Int53} :
    subOverflows a b ↔ (a.toInt - b.toInt < MIN ∨ MAX < a.toInt - b.toInt) := by
  rw [BoundedInt64.subOverflows_iff, hi_toInt, lo_toInt]

/-! ### The checked variant -/

/-- Exactness: whenever `checked_sub` succeeds, it returns the exact difference. -/
theorem toInt_of_checked_sub {a b c : Int53} (h : checked_sub a b = some c) :
    c.toInt = a.toInt - b.toInt := BoundedInt64.toInt_of_checked_sub h

/-- `checked_sub` fails exactly on the differences that leave `[MIN, MAX]`. -/
theorem checked_sub_eq_none_iff {a b : Int53} :
    checked_sub a b = none ↔ (a.toInt - b.toInt < MIN ∨ MAX < a.toInt - b.toInt) := by
  rw [BoundedInt64.checked_sub_eq_none_iff, subOverflows_iff]

/-- `checked_sub` succeeds, with the exact difference, on every difference in range. -/
theorem checked_sub_exact {a b : Int53} (h₁ : MIN ≤ a.toInt - b.toInt)
    (h₂ : a.toInt - b.toInt ≤ MAX) :
    ∃ c, checked_sub a b = some c ∧ c.toInt = a.toInt - b.toInt :=
  BoundedInt64.checked_sub_of_not_overflows (by rw [subOverflows_iff]; omega)

/-! ### The wrapping variant -/

@[simp] theorem toInt_wrapping_sub (a b : Int53) :
    (wrapping_sub a b).toInt = MIN + (a.toInt - b.toInt - MIN) % SIZE := by
  rw [BoundedInt64.toInt_wrapping_sub, lo_toInt, period_eq]

theorem toInt_wrapping_sub_exact {a b : Int53} (h₁ : MIN ≤ a.toInt - b.toInt)
    (h₂ : a.toInt - b.toInt ≤ MAX) : (wrapping_sub a b).toInt = a.toInt - b.toInt :=
  BoundedInt64.toInt_wrapping_sub_of_not_overflows (by rw [subOverflows_iff]; omega)

/-- Above `MAX`, wrapping subtraction subtracts one period. -/
theorem toInt_wrapping_sub_of_gt_MAX {a b : Int53} (h : MAX < a.toInt - b.toInt) :
    (wrapping_sub a b).toInt = a.toInt - b.toInt - SIZE := by
  have ha := le_MAX a
  have hb := MIN_le b
  have hlt : (2 ^ 53 - 1 : Int64).toInt < a.toInt - b.toInt := by rw [hi_toInt]; exact h
  have hle : a.toInt - b.toInt - BoundedInt64.period (-(2 ^ 53 - 1)) (2 ^ 53 - 1)
      ≤ (2 ^ 53 - 1 : Int64).toInt := by
    rw [hi_toInt, period_eq]
    unfold MAX MIN SIZE at *
    omega
  have := BoundedInt64.toInt_wrapping_sub_of_gt_hi hlt hle
  rwa [period_eq] at this

/-- Below `MIN`, wrapping subtraction adds one period. -/
theorem toInt_wrapping_sub_of_lt_MIN {a b : Int53} (h : a.toInt - b.toInt < MIN) :
    (wrapping_sub a b).toInt = a.toInt - b.toInt + SIZE := by
  have ha := MIN_le a
  have hb := le_MAX b
  have hlt : a.toInt - b.toInt < (-(2 ^ 53 - 1) : Int64).toInt := by rw [lo_toInt]; exact h
  have hle : (-(2 ^ 53 - 1) : Int64).toInt
      ≤ a.toInt - b.toInt + BoundedInt64.period (-(2 ^ 53 - 1)) (2 ^ 53 - 1) := by
    rw [lo_toInt, period_eq]
    unfold MAX MIN SIZE at *
    omega
  have := BoundedInt64.toInt_wrapping_sub_of_lt_lo hlt hle
  rwa [period_eq] at this

/-! ### The overflowing variant -/

theorem overflowing_sub_snd_iff {a b : Int53} :
    (overflowing_sub a b).2 = true ↔
      (a.toInt - b.toInt < MIN ∨ MAX < a.toInt - b.toInt) := by
  rw [BoundedInt64.overflowing_sub_snd_iff, subOverflows_iff]

theorem toInt_overflowing_sub_exact {a b : Int53} (h₁ : MIN ≤ a.toInt - b.toInt)
    (h₂ : a.toInt - b.toInt ≤ MAX) :
    (overflowing_sub a b).1.toInt = a.toInt - b.toInt := by
  rw [overflowing_sub_fst]
  exact toInt_wrapping_sub_exact h₁ h₂

/-! ### The saturating variant -/

@[simp] theorem toInt_saturating_sub (a b : Int53) :
    (saturating_sub a b).toInt = max MIN (min (a.toInt - b.toInt) MAX) := by
  rw [BoundedInt64.toInt_saturating_sub, hi_toInt, lo_toInt]

theorem toInt_saturating_sub_exact {a b : Int53} (h₁ : MIN ≤ a.toInt - b.toInt)
    (h₂ : a.toInt - b.toInt ≤ MAX) : (saturating_sub a b).toInt = a.toInt - b.toInt :=
  BoundedInt64.toInt_saturating_sub_of_not_overflows (by rw [subOverflows_iff]; omega)

theorem toInt_saturating_sub_of_gt_MAX {a b : Int53} (h : MAX < a.toInt - b.toInt) :
    (saturating_sub a b).toInt = MAX :=
  BoundedInt64.toInt_saturating_sub_of_gt_hi (by rw [hi_toInt]; exact h) |>.trans hi_toInt

theorem toInt_saturating_sub_of_lt_MIN {a b : Int53} (h : a.toInt - b.toInt < MIN) :
    (saturating_sub a b).toInt = MIN :=
  BoundedInt64.toInt_saturating_sub_of_lt_lo (by rw [lo_toInt]; exact h) |>.trans lo_toInt

/-! ### The machine operation is already exact on this range -/

/-- Because `2 * MAX < 2 ^ 63`, the raw `Int64` difference of two `Int53` values never
wraps at the machine level: it denotes the exact difference. -/
theorem toInt_val_sub (a b : Int53) : (a.val - b.val).toInt = a.toInt - b.toInt := by
  have ha₁ := MIN_le a
  have ha₂ := le_MAX a
  have hb₁ := MIN_le b
  have hb₂ := le_MAX b
  have ha' : a.val.toInt = a.toInt := rfl
  have hb' : b.val.toInt = b.toInt := rfl
  unfold MIN MAX at *
  rw [Int64.toInt_sub, ha', hb']
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- Refinement: when the difference is in range, `wrapping_sub` returns the raw machine
difference. -/
theorem val_wrapping_sub_exact {a b : Int53} (h₁ : MIN ≤ a.toInt - b.toInt)
    (h₂ : a.toInt - b.toInt ≤ MAX) : (wrapping_sub a b).val = a.val - b.val := by
  apply Int64.toInt_inj.mp
  rw [toInt_val_sub]
  exact toInt_wrapping_sub_exact h₁ h₂

/-! ### Exact arithmetic, concretely -/

/-- `3 - 2 = 1`, exactly. -/
theorem three_sub_two : checked_sub (ofInt 3) (ofInt 2) = some (ofInt 1) := by decide

/-- `1 - 3 = -2`, exactly: negative results are in range. -/
theorem one_sub_three : checked_sub (ofInt 1) (ofInt 3) = some (ofInt (-2)) := by decide

/-- `MIN - 1` underflows: the checked variant reports it. -/
theorem checked_sub_min_one : checked_sub minVal (ofInt 1) = none := by decide

/-- `MIN - 1` wraps to `MAX`. -/
theorem wrapping_sub_min_one : wrapping_sub minVal (ofInt 1) = maxVal := by decide

/-- `MIN - 1` saturates at `MIN`. -/
theorem saturating_sub_min_one : saturating_sub minVal (ofInt 1) = minVal := by decide

/-- `MAX - (-1)` wraps to `MIN`. -/
theorem wrapping_sub_max_neg_one : wrapping_sub maxVal (ofInt (-1)) = minVal := by decide

end Int53
