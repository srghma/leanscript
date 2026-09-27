import IntUInt53.BoundedInt64.Basic

/-!
# Addition on `BoundedInt64`

The four variants of addition:

* `checked_add`     — `none` when the exact sum leaves `[lo, hi]`;
* `overflowing_add` — the wrapped value together with a flag;
* `wrapping_add`    — reduction modulo the period `hi - lo + 1`;
* `saturating_add`  — the exact sum, clamped to `[lo, hi]`.

Everything is specified through `toInt`, i.e. through exact integer arithmetic.
Whenever the exact sum is representable, all four variants return it.
-/

set_option autoImplicit false

namespace BoundedInt64

variable {lo hi : Int64}

/-- The exact sum of the integers denoted by `a` and `b`. -/
def exactAdd (a b : BoundedInt64 lo hi) : Int := a.toInt + b.toInt

/-- Addition overflows when the exact sum leaves the range. -/
def addOverflows (a b : BoundedInt64 lo hi) : Prop := ¬ InRange lo hi (exactAdd a b)

instance (a b : BoundedInt64 lo hi) : Decidable (addOverflows a b) := by
  unfold addOverflows; infer_instance

theorem addOverflows_iff {a b : BoundedInt64 lo hi} :
    addOverflows a b ↔ (a.toInt + b.toInt < lo.toInt ∨ hi.toInt < a.toInt + b.toInt) := by
  unfold addOverflows InRange exactAdd; omega

/-! ### The checked variant -/

/-- Checked addition: `none` exactly when the exact sum is out of range. -/
def checked_add (a b : BoundedInt64 lo hi) : Option (BoundedInt64 lo hi) :=
  ofInt? lo hi (exactAdd a b)

theorem checked_add_eq_some_iff {a b c : BoundedInt64 lo hi} :
    checked_add a b = some c ↔ c.toInt = a.toInt + b.toInt :=
  ofInt?_eq_some_iff

/-- Exactness: whenever checked addition succeeds, its result is the exact sum. -/
theorem toInt_of_checked_add {a b c : BoundedInt64 lo hi} (h : checked_add a b = some c) :
    c.toInt = a.toInt + b.toInt := checked_add_eq_some_iff.mp h

theorem checked_add_eq_none_iff {a b : BoundedInt64 lo hi} :
    checked_add a b = none ↔ addOverflows a b := ofInt?_eq_none_iff

/-- Checked addition succeeds, with the exact sum, whenever that value is in range. -/
theorem checked_add_of_not_overflows {a b : BoundedInt64 lo hi} (h : ¬ addOverflows a b) :
    ∃ c, checked_add a b = some c ∧ c.toInt = a.toInt + b.toInt := by
  have hr : InRange lo hi (exactAdd a b) := Decidable.of_not_not h
  exact ⟨ofIntMem lo hi (exactAdd a b) hr.1 hr.2, ofInt?_of_inRange hr, by simp [exactAdd]⟩

/-! ### The wrapping variant -/

/-- Wrapping addition: the exact sum reduced modulo the period `hi - lo + 1`. -/
def wrapping_add (a b : BoundedInt64 lo hi) : BoundedInt64 lo hi :=
  ofIntWrap (lo_le_hi a) (exactAdd a b)

@[simp] theorem toInt_wrapping_add (a b : BoundedInt64 lo hi) :
    (wrapping_add a b).toInt = lo.toInt + (a.toInt + b.toInt - lo.toInt) % period lo hi := by
  unfold wrapping_add exactAdd; rw [toInt_ofIntWrap]

/-- Exactness: wrapping addition returns the exact sum when there is no overflow. -/
theorem toInt_wrapping_add_of_not_overflows {a b : BoundedInt64 lo hi}
    (h : ¬ addOverflows a b) : (wrapping_add a b).toInt = a.toInt + b.toInt :=
  ofIntWrap_of_inRange (lo_le_hi a) (Decidable.of_not_not h)

/-- Above the upper bound — and within one period of it — wrapping addition subtracts
exactly one period. -/
theorem toInt_wrapping_add_of_gt_hi {a b : BoundedInt64 lo hi}
    (h₁ : hi.toInt < a.toInt + b.toInt)
    (h₂ : a.toInt + b.toInt - period lo hi ≤ hi.toInt) :
    (wrapping_add a b).toInt = a.toInt + b.toInt - period lo hi :=
  toInt_ofIntWrap_sub_period (lo_le_hi a) h₁ h₂

/-- Below the lower bound — and within one period of it — wrapping addition adds
exactly one period. -/
theorem toInt_wrapping_add_of_lt_lo {a b : BoundedInt64 lo hi}
    (h₁ : a.toInt + b.toInt < lo.toInt)
    (h₂ : lo.toInt ≤ a.toInt + b.toInt + period lo hi) :
    (wrapping_add a b).toInt = a.toInt + b.toInt + period lo hi :=
  toInt_ofIntWrap_add_period (lo_le_hi a) h₁ h₂

/-! ### The overflowing variant -/

/-- Overflowing addition: the wrapped value together with an overflow flag. -/
def overflowing_add (a b : BoundedInt64 lo hi) : BoundedInt64 lo hi × Bool :=
  (wrapping_add a b, decide (¬ InRange lo hi (exactAdd a b)))

@[simp] theorem overflowing_add_fst (a b : BoundedInt64 lo hi) :
    (overflowing_add a b).1 = wrapping_add a b := rfl

theorem overflowing_add_snd_iff {a b : BoundedInt64 lo hi} :
    (overflowing_add a b).2 = true ↔ addOverflows a b := by
  unfold overflowing_add addOverflows; simp

/-- Exactness: if the flag is `false`, the value returned is the exact sum. -/
theorem toInt_overflowing_add_of_not_flag {a b : BoundedInt64 lo hi}
    (h : (overflowing_add a b).2 = false) :
    (overflowing_add a b).1.toInt = a.toInt + b.toInt := by
  have hn : ¬ addOverflows a b := by
    intro hc; rw [← overflowing_add_snd_iff] at hc; rw [h] at hc; exact Bool.noConfusion hc
  exact toInt_wrapping_add_of_not_overflows hn

/-! ### The saturating variant -/

/-- Saturating addition: the exact sum, clamped to `[lo, hi]`. -/
def saturating_add (a b : BoundedInt64 lo hi) : BoundedInt64 lo hi :=
  ofIntSat (lo_le_hi a) (exactAdd a b)

@[simp] theorem toInt_saturating_add (a b : BoundedInt64 lo hi) :
    (saturating_add a b).toInt = max lo.toInt (min (a.toInt + b.toInt) hi.toInt) := by
  unfold saturating_add exactAdd; rw [toInt_ofIntSat]

/-- Exactness: saturating addition returns the exact sum when there is no overflow. -/
theorem toInt_saturating_add_of_not_overflows {a b : BoundedInt64 lo hi}
    (h : ¬ addOverflows a b) : (saturating_add a b).toInt = a.toInt + b.toInt :=
  ofIntSat_of_inRange (lo_le_hi a) (Decidable.of_not_not h)

/-- Above the upper bound, saturating addition returns `hi`. -/
theorem toInt_saturating_add_of_gt_hi {a b : BoundedInt64 lo hi}
    (h : hi.toInt < a.toInt + b.toInt) : (saturating_add a b).toInt = hi.toInt := by
  rw [toInt_saturating_add]
  have := lo_toInt_le_hi_toInt a
  omega

/-- Below the lower bound, saturating addition returns `lo`. -/
theorem toInt_saturating_add_of_lt_lo {a b : BoundedInt64 lo hi}
    (h : a.toInt + b.toInt < lo.toInt) : (saturating_add a b).toInt = lo.toInt := by
  rw [toInt_saturating_add]
  have := lo_toInt_le_hi_toInt a
  omega

/-! ### Agreement of the four variants in the exact case -/

/-- When the exact sum is representable, all four variants denote it. -/
theorem add_variants_agree {a b c : BoundedInt64 lo hi} (h : checked_add a b = some c) :
    c.toInt = a.toInt + b.toInt ∧
      (wrapping_add a b).toInt = a.toInt + b.toInt ∧
      (overflowing_add a b).1.toInt = a.toInt + b.toInt ∧
      (overflowing_add a b).2 = false ∧
      (saturating_add a b).toInt = a.toInt + b.toInt := by
  have hval := toInt_of_checked_add h
  have hn : ¬ addOverflows a b := by
    rw [addOverflows_iff, ← hval]
    have h₁ := lo_le_toInt c
    have h₂ := toInt_le_hi c
    omega
  have hflag : (overflowing_add a b).2 = false := by
    cases hb : (overflowing_add a b).2 with
    | false => rfl
    | true => exact absurd (overflowing_add_snd_iff.mp hb) hn
  exact ⟨hval, toInt_wrapping_add_of_not_overflows hn,
    toInt_wrapping_add_of_not_overflows hn, hflag,
    toInt_saturating_add_of_not_overflows hn⟩

/-! ### Algebraic laws of wrapping addition -/

theorem wrapping_add_comm (a b : BoundedInt64 lo hi) :
    wrapping_add a b = wrapping_add b a := by
  apply ext
  simp only [toInt_wrapping_add, Int.add_comm]

end BoundedInt64
