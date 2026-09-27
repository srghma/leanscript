import IntUInt53.BoundedInt64.Basic

/-!
# Multiplication on `BoundedInt64`

The four variants of multiplication:

* `checked_mul`     — `none` when the exact product leaves `[lo, hi]`;
* `overflowing_mul` — the wrapped value together with a flag;
* `wrapping_mul`    — reduction modulo the period `hi - lo + 1`;
* `saturating_mul`  — the exact product, clamped to `[lo, hi]`.

Everything is specified through `toInt`, i.e. through exact integer arithmetic.
Whenever the exact product is representable, all four variants return it.
-/

set_option autoImplicit false

namespace BoundedInt64

variable {lo hi : Int64}

/-- The exact product of the integers denoted by `a` and `b`. -/
def exactMul (a b : BoundedInt64 lo hi) : Int := a.toInt * b.toInt

/-- Multiplication overflows when the exact product leaves the range. -/
def mulOverflows (a b : BoundedInt64 lo hi) : Prop := ¬ InRange lo hi (exactMul a b)

instance (a b : BoundedInt64 lo hi) : Decidable (mulOverflows a b) := by
  unfold mulOverflows; infer_instance

theorem mulOverflows_iff {a b : BoundedInt64 lo hi} :
    mulOverflows a b ↔ (a.toInt * b.toInt < lo.toInt ∨ hi.toInt < a.toInt * b.toInt) := by
  unfold mulOverflows InRange exactMul; omega

/-! ### The checked variant -/

/-- Checked multiplication: `none` exactly when the exact product is out of range. -/
def checked_mul (a b : BoundedInt64 lo hi) : Option (BoundedInt64 lo hi) :=
  ofInt? lo hi (exactMul a b)

theorem checked_mul_eq_some_iff {a b c : BoundedInt64 lo hi} :
    checked_mul a b = some c ↔ c.toInt = a.toInt * b.toInt :=
  ofInt?_eq_some_iff

/-- Exactness: whenever checked multiplication succeeds, its result is the exact product. -/
theorem toInt_of_checked_mul {a b c : BoundedInt64 lo hi} (h : checked_mul a b = some c) :
    c.toInt = a.toInt * b.toInt := checked_mul_eq_some_iff.mp h

theorem checked_mul_eq_none_iff {a b : BoundedInt64 lo hi} :
    checked_mul a b = none ↔ mulOverflows a b := ofInt?_eq_none_iff

/-- Checked multiplication succeeds, with the exact product, whenever that value is in range. -/
theorem checked_mul_of_not_overflows {a b : BoundedInt64 lo hi} (h : ¬ mulOverflows a b) :
    ∃ c, checked_mul a b = some c ∧ c.toInt = a.toInt * b.toInt := by
  have hr : InRange lo hi (exactMul a b) := Decidable.of_not_not h
  exact ⟨ofIntMem lo hi (exactMul a b) hr.1 hr.2, ofInt?_of_inRange hr, by simp [exactMul]⟩

/-! ### The wrapping variant -/

/-- Wrapping multiplication: the exact product reduced modulo the period `hi - lo + 1`. -/
def wrapping_mul (a b : BoundedInt64 lo hi) : BoundedInt64 lo hi :=
  ofIntWrap (lo_le_hi a) (exactMul a b)

@[simp] theorem toInt_wrapping_mul (a b : BoundedInt64 lo hi) :
    (wrapping_mul a b).toInt = lo.toInt + (a.toInt * b.toInt - lo.toInt) % period lo hi := by
  unfold wrapping_mul exactMul; rw [toInt_ofIntWrap]

/-- Exactness: wrapping multiplication returns the exact product when there is no overflow. -/
theorem toInt_wrapping_mul_of_not_overflows {a b : BoundedInt64 lo hi}
    (h : ¬ mulOverflows a b) : (wrapping_mul a b).toInt = a.toInt * b.toInt :=
  ofIntWrap_of_inRange (lo_le_hi a) (Decidable.of_not_not h)

/-- Above the upper bound — and within one period of it — wrapping multiplication subtracts
exactly one period. -/
theorem toInt_wrapping_mul_of_gt_hi {a b : BoundedInt64 lo hi}
    (h₁ : hi.toInt < a.toInt * b.toInt)
    (h₂ : a.toInt * b.toInt - period lo hi ≤ hi.toInt) :
    (wrapping_mul a b).toInt = a.toInt * b.toInt - period lo hi :=
  toInt_ofIntWrap_sub_period (lo_le_hi a) h₁ h₂

/-- Below the lower bound — and within one period of it — wrapping multiplication adds
exactly one period. -/
theorem toInt_wrapping_mul_of_lt_lo {a b : BoundedInt64 lo hi}
    (h₁ : a.toInt * b.toInt < lo.toInt)
    (h₂ : lo.toInt ≤ a.toInt * b.toInt + period lo hi) :
    (wrapping_mul a b).toInt = a.toInt * b.toInt + period lo hi :=
  toInt_ofIntWrap_add_period (lo_le_hi a) h₁ h₂

/-! ### The overflowing variant -/

/-- Overflowing multiplication: the wrapped value together with an overflow flag. -/
def overflowing_mul (a b : BoundedInt64 lo hi) : BoundedInt64 lo hi × Bool :=
  (wrapping_mul a b, decide (¬ InRange lo hi (exactMul a b)))

@[simp] theorem overflowing_mul_fst (a b : BoundedInt64 lo hi) :
    (overflowing_mul a b).1 = wrapping_mul a b := rfl

theorem overflowing_mul_snd_iff {a b : BoundedInt64 lo hi} :
    (overflowing_mul a b).2 = true ↔ mulOverflows a b := by
  unfold overflowing_mul mulOverflows; simp

/-- Exactness: if the flag is `false`, the value returned is the exact product. -/
theorem toInt_overflowing_mul_of_not_flag {a b : BoundedInt64 lo hi}
    (h : (overflowing_mul a b).2 = false) :
    (overflowing_mul a b).1.toInt = a.toInt * b.toInt := by
  have hn : ¬ mulOverflows a b := by
    intro hc; rw [← overflowing_mul_snd_iff] at hc; rw [h] at hc; exact Bool.noConfusion hc
  exact toInt_wrapping_mul_of_not_overflows hn

/-! ### The saturating variant -/

/-- Saturating multiplication: the exact product, clamped to `[lo, hi]`. -/
def saturating_mul (a b : BoundedInt64 lo hi) : BoundedInt64 lo hi :=
  ofIntSat (lo_le_hi a) (exactMul a b)

@[simp] theorem toInt_saturating_mul (a b : BoundedInt64 lo hi) :
    (saturating_mul a b).toInt = max lo.toInt (min (a.toInt * b.toInt) hi.toInt) := by
  unfold saturating_mul exactMul; rw [toInt_ofIntSat]

/-- Exactness: saturating multiplication returns the exact product when there is no overflow. -/
theorem toInt_saturating_mul_of_not_overflows {a b : BoundedInt64 lo hi}
    (h : ¬ mulOverflows a b) : (saturating_mul a b).toInt = a.toInt * b.toInt :=
  ofIntSat_of_inRange (lo_le_hi a) (Decidable.of_not_not h)

/-- Above the upper bound, saturating multiplication returns `hi`. -/
theorem toInt_saturating_mul_of_gt_hi {a b : BoundedInt64 lo hi}
    (h : hi.toInt < a.toInt * b.toInt) : (saturating_mul a b).toInt = hi.toInt := by
  rw [toInt_saturating_mul]
  have := lo_toInt_le_hi_toInt a
  omega

/-- Below the lower bound, saturating multiplication returns `lo`. -/
theorem toInt_saturating_mul_of_lt_lo {a b : BoundedInt64 lo hi}
    (h : a.toInt * b.toInt < lo.toInt) : (saturating_mul a b).toInt = lo.toInt := by
  rw [toInt_saturating_mul]
  have := lo_toInt_le_hi_toInt a
  omega

/-! ### Agreement of the four variants in the exact case -/

/-- When the exact product is representable, all four variants denote it. -/
theorem mul_variants_agree {a b c : BoundedInt64 lo hi} (h : checked_mul a b = some c) :
    c.toInt = a.toInt * b.toInt ∧
      (wrapping_mul a b).toInt = a.toInt * b.toInt ∧
      (overflowing_mul a b).1.toInt = a.toInt * b.toInt ∧
      (overflowing_mul a b).2 = false ∧
      (saturating_mul a b).toInt = a.toInt * b.toInt := by
  have hval := toInt_of_checked_mul h
  have hn : ¬ mulOverflows a b := by
    rw [mulOverflows_iff, ← hval]
    have h₁ := lo_le_toInt c
    have h₂ := toInt_le_hi c
    omega
  have hflag : (overflowing_mul a b).2 = false := by
    cases hb : (overflowing_mul a b).2 with
    | false => rfl
    | true => exact absurd (overflowing_mul_snd_iff.mp hb) hn
  exact ⟨hval, toInt_wrapping_mul_of_not_overflows hn,
    toInt_wrapping_mul_of_not_overflows hn, hflag,
    toInt_saturating_mul_of_not_overflows hn⟩

/-! ### Commutativity of wrapping multiplication -/

theorem wrapping_mul_comm (a b : BoundedInt64 lo hi) :
    wrapping_mul a b = wrapping_mul b a := by
  apply ext
  simp only [toInt_wrapping_mul, Int.mul_comm]

end BoundedInt64
