import IntUInt53.BoundedInt64.Basic

/-!
# Subtraction on `BoundedInt64`

The four variants of subtraction:

* `checked_sub`     — `none` when the exact difference leaves `[lo, hi]`;
* `overflowing_sub` — the wrapped value together with a flag;
* `wrapping_sub`    — reduction modulo the period `hi - lo + 1`;
* `saturating_sub`  — the exact difference, clamped to `[lo, hi]`.

Everything is specified through `toInt`, i.e. through exact integer arithmetic.
Whenever the exact difference is representable, all four variants return it.
-/

set_option autoImplicit false

namespace BoundedInt64

variable {lo hi : Int64}

/-- The exact difference of the integers denoted by `a` and `b`. -/
def exactSub (a b : BoundedInt64 lo hi) : Int := a.toInt - b.toInt

/-- Subtraction overflows when the exact difference leaves the range. -/
def subOverflows (a b : BoundedInt64 lo hi) : Prop := ¬ InRange lo hi (exactSub a b)

instance (a b : BoundedInt64 lo hi) : Decidable (subOverflows a b) := by
  unfold subOverflows; infer_instance

theorem subOverflows_iff {a b : BoundedInt64 lo hi} :
    subOverflows a b ↔ (a.toInt - b.toInt < lo.toInt ∨ hi.toInt < a.toInt - b.toInt) := by
  unfold subOverflows InRange exactSub; omega

/-! ### The checked variant -/

/-- Checked subtraction: `none` exactly when the exact difference is out of range. -/
def checked_sub (a b : BoundedInt64 lo hi) : Option (BoundedInt64 lo hi) :=
  ofInt? lo hi (exactSub a b)

theorem checked_sub_eq_some_iff {a b c : BoundedInt64 lo hi} :
    checked_sub a b = some c ↔ c.toInt = a.toInt - b.toInt :=
  ofInt?_eq_some_iff

/-- Exactness: whenever checked subtraction succeeds, its result is the exact difference. -/
theorem toInt_of_checked_sub {a b c : BoundedInt64 lo hi} (h : checked_sub a b = some c) :
    c.toInt = a.toInt - b.toInt := checked_sub_eq_some_iff.mp h

theorem checked_sub_eq_none_iff {a b : BoundedInt64 lo hi} :
    checked_sub a b = none ↔ subOverflows a b := ofInt?_eq_none_iff

/-- Checked subtraction succeeds, with the exact difference, whenever that value is in range. -/
theorem checked_sub_of_not_overflows {a b : BoundedInt64 lo hi} (h : ¬ subOverflows a b) :
    ∃ c, checked_sub a b = some c ∧ c.toInt = a.toInt - b.toInt := by
  have hr : InRange lo hi (exactSub a b) := Decidable.of_not_not h
  exact ⟨ofIntMem lo hi (exactSub a b) hr.1 hr.2, ofInt?_of_inRange hr, by simp [exactSub]⟩

/-! ### The wrapping variant -/

/-- Wrapping subtraction: the exact difference reduced modulo the period `hi - lo + 1`. -/
def wrapping_sub (a b : BoundedInt64 lo hi) : BoundedInt64 lo hi :=
  ofIntWrap (lo_le_hi a) (exactSub a b)

@[simp] theorem toInt_wrapping_sub (a b : BoundedInt64 lo hi) :
    (wrapping_sub a b).toInt = lo.toInt + (a.toInt - b.toInt - lo.toInt) % period lo hi := by
  unfold wrapping_sub exactSub; rw [toInt_ofIntWrap]

/-- Exactness: wrapping subtraction returns the exact difference when there is no overflow. -/
theorem toInt_wrapping_sub_of_not_overflows {a b : BoundedInt64 lo hi}
    (h : ¬ subOverflows a b) : (wrapping_sub a b).toInt = a.toInt - b.toInt :=
  ofIntWrap_of_inRange (lo_le_hi a) (Decidable.of_not_not h)

/-- Above the upper bound — and within one period of it — wrapping subtraction subtracts
exactly one period. -/
theorem toInt_wrapping_sub_of_gt_hi {a b : BoundedInt64 lo hi}
    (h₁ : hi.toInt < a.toInt - b.toInt)
    (h₂ : a.toInt - b.toInt - period lo hi ≤ hi.toInt) :
    (wrapping_sub a b).toInt = a.toInt - b.toInt - period lo hi :=
  toInt_ofIntWrap_sub_period (lo_le_hi a) h₁ h₂

/-- Below the lower bound — and within one period of it — wrapping subtraction adds
exactly one period. -/
theorem toInt_wrapping_sub_of_lt_lo {a b : BoundedInt64 lo hi}
    (h₁ : a.toInt - b.toInt < lo.toInt)
    (h₂ : lo.toInt ≤ a.toInt - b.toInt + period lo hi) :
    (wrapping_sub a b).toInt = a.toInt - b.toInt + period lo hi :=
  toInt_ofIntWrap_add_period (lo_le_hi a) h₁ h₂

/-! ### The overflowing variant -/

/-- Overflowing subtraction: the wrapped value together with an overflow flag. -/
def overflowing_sub (a b : BoundedInt64 lo hi) : BoundedInt64 lo hi × Bool :=
  (wrapping_sub a b, decide (¬ InRange lo hi (exactSub a b)))

@[simp] theorem overflowing_sub_fst (a b : BoundedInt64 lo hi) :
    (overflowing_sub a b).1 = wrapping_sub a b := rfl

theorem overflowing_sub_snd_iff {a b : BoundedInt64 lo hi} :
    (overflowing_sub a b).2 = true ↔ subOverflows a b := by
  unfold overflowing_sub subOverflows; simp

/-- Exactness: if the flag is `false`, the value returned is the exact difference. -/
theorem toInt_overflowing_sub_of_not_flag {a b : BoundedInt64 lo hi}
    (h : (overflowing_sub a b).2 = false) :
    (overflowing_sub a b).1.toInt = a.toInt - b.toInt := by
  have hn : ¬ subOverflows a b := by
    intro hc; rw [← overflowing_sub_snd_iff] at hc; rw [h] at hc; exact Bool.noConfusion hc
  exact toInt_wrapping_sub_of_not_overflows hn

/-! ### The saturating variant -/

/-- Saturating subtraction: the exact difference, clamped to `[lo, hi]`. -/
def saturating_sub (a b : BoundedInt64 lo hi) : BoundedInt64 lo hi :=
  ofIntSat (lo_le_hi a) (exactSub a b)

@[simp] theorem toInt_saturating_sub (a b : BoundedInt64 lo hi) :
    (saturating_sub a b).toInt = max lo.toInt (min (a.toInt - b.toInt) hi.toInt) := by
  unfold saturating_sub exactSub; rw [toInt_ofIntSat]

/-- Exactness: saturating subtraction returns the exact difference when there is no overflow. -/
theorem toInt_saturating_sub_of_not_overflows {a b : BoundedInt64 lo hi}
    (h : ¬ subOverflows a b) : (saturating_sub a b).toInt = a.toInt - b.toInt :=
  ofIntSat_of_inRange (lo_le_hi a) (Decidable.of_not_not h)

/-- Above the upper bound, saturating subtraction returns `hi`. -/
theorem toInt_saturating_sub_of_gt_hi {a b : BoundedInt64 lo hi}
    (h : hi.toInt < a.toInt - b.toInt) : (saturating_sub a b).toInt = hi.toInt := by
  rw [toInt_saturating_sub]
  have := lo_toInt_le_hi_toInt a
  omega

/-- Below the lower bound, saturating subtraction returns `lo`. -/
theorem toInt_saturating_sub_of_lt_lo {a b : BoundedInt64 lo hi}
    (h : a.toInt - b.toInt < lo.toInt) : (saturating_sub a b).toInt = lo.toInt := by
  rw [toInt_saturating_sub]
  have := lo_toInt_le_hi_toInt a
  omega

/-! ### Agreement of the four variants in the exact case -/

/-- When the exact difference is representable, all four variants denote it. -/
theorem sub_variants_agree {a b c : BoundedInt64 lo hi} (h : checked_sub a b = some c) :
    c.toInt = a.toInt - b.toInt ∧
      (wrapping_sub a b).toInt = a.toInt - b.toInt ∧
      (overflowing_sub a b).1.toInt = a.toInt - b.toInt ∧
      (overflowing_sub a b).2 = false ∧
      (saturating_sub a b).toInt = a.toInt - b.toInt := by
  have hval := toInt_of_checked_sub h
  have hn : ¬ subOverflows a b := by
    rw [subOverflows_iff, ← hval]
    have h₁ := lo_le_toInt c
    have h₂ := toInt_le_hi c
    omega
  have hflag : (overflowing_sub a b).2 = false := by
    cases hb : (overflowing_sub a b).2 with
    | false => rfl
    | true => exact absurd (overflowing_sub_snd_iff.mp hb) hn
  exact ⟨hval, toInt_wrapping_sub_of_not_overflows hn,
    toInt_wrapping_sub_of_not_overflows hn, hflag,
    toInt_saturating_sub_of_not_overflows hn⟩

end BoundedInt64
