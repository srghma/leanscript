import IntUInt53.TopBoundedUInt64.Basic

/-!
# Multiplication on `TopBoundedUInt64`

The four variants of multiplication:

* `checked_mul`     — `none` when the exact product does not fit;
* `overflowing_mul` — the wrapped value together with a flag;
* `wrapping_mul`    — the exact product modulo the period `hi + 1`;
* `saturating_mul`  — the exact product, clamped at `hi`.

The exact product is computed in `Nat`, so it is never truncated before the
chosen overflow behaviour is applied: unlike a machine multiplication, the
value each variant is specified against is the true mathematical product.
-/

set_option autoImplicit false

namespace TopBoundedUInt64

variable {hi : UInt64}

/-- The exact product of the numbers denoted by `a` and `b`. -/
def exactMul (a b : TopBoundedUInt64 hi) : Nat := a.toNat * b.toNat

/-- Multiplication overflows when the exact product exceeds the bound. -/
def mulOverflows (a b : TopBoundedUInt64 hi) : Prop := ¬ InRange hi (exactMul a b)

instance (a b : TopBoundedUInt64 hi) : Decidable (mulOverflows a b) := by
  unfold mulOverflows; infer_instance

theorem mulOverflows_iff {a b : TopBoundedUInt64 hi} :
    mulOverflows a b ↔ hi.toNat < a.toNat * b.toNat := by
  unfold mulOverflows InRange exactMul; omega

/-! ### The checked variant -/

/-- Checked multiplication: `none` exactly when the exact product is out of range. -/
def checked_mul (a b : TopBoundedUInt64 hi) : Option (TopBoundedUInt64 hi) :=
  ofNat? hi (exactMul a b)

theorem checked_mul_eq_some_iff {a b c : TopBoundedUInt64 hi} :
    checked_mul a b = some c ↔ c.toNat = a.toNat * b.toNat :=
  ofNat?_eq_some_iff

/-- Exactness: whenever checked multiplication succeeds, its result is the exact product. -/
theorem toNat_of_checked_mul {a b c : TopBoundedUInt64 hi} (h : checked_mul a b = some c) :
    c.toNat = a.toNat * b.toNat := checked_mul_eq_some_iff.mp h

theorem checked_mul_eq_none_iff {a b : TopBoundedUInt64 hi} :
    checked_mul a b = none ↔ mulOverflows a b := ofNat?_eq_none_iff

/-- Checked multiplication succeeds, with the exact product, whenever that product is
in range. -/
theorem checked_mul_of_not_overflows {a b : TopBoundedUInt64 hi} (h : ¬ mulOverflows a b) :
    ∃ c, checked_mul a b = some c ∧ c.toNat = a.toNat * b.toNat := by
  have hr : InRange hi (exactMul a b) := by
    unfold mulOverflows at h; exact Decidable.of_not_not h
  exact ⟨ofNatLe hi (exactMul a b) hr, ofNat?_of_inRange hr, by simp [exactMul]⟩

/-! ### The wrapping variant -/

/-- Wrapping multiplication: the exact product reduced modulo the period `hi + 1`. -/
def wrapping_mul (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi :=
  ofNatWrap hi (exactMul a b)

@[simp] theorem toNat_wrapping_mul (a b : TopBoundedUInt64 hi) :
    (wrapping_mul a b).toNat = (a.toNat * b.toNat) % period hi := by
  unfold wrapping_mul exactMul; rw [toNat_ofNatWrap]

/-- Exactness: wrapping multiplication returns the exact product when there is no
overflow. -/
theorem toNat_wrapping_mul_of_not_overflows {a b : TopBoundedUInt64 hi}
    (h : ¬ mulOverflows a b) : (wrapping_mul a b).toNat = a.toNat * b.toNat := by
  rw [toNat_wrapping_mul]
  exact Nat.mod_eq_of_lt (inRange_iff_lt_period.mp (Decidable.of_not_not h))

/-! ### The overflowing variant -/

/-- Overflowing multiplication: the wrapped value together with an overflow flag. -/
def overflowing_mul (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi × Bool :=
  (wrapping_mul a b, decide (hi.toNat < exactMul a b))

@[simp] theorem overflowing_mul_fst (a b : TopBoundedUInt64 hi) :
    (overflowing_mul a b).1 = wrapping_mul a b := rfl

theorem overflowing_mul_snd_iff {a b : TopBoundedUInt64 hi} :
    (overflowing_mul a b).2 = true ↔ mulOverflows a b := by
  unfold overflowing_mul exactMul
  rw [mulOverflows_iff]
  simp

/-- Exactness: if the flag is `false`, the value returned is the exact product. -/
theorem toNat_overflowing_mul_of_not_flag {a b : TopBoundedUInt64 hi}
    (h : (overflowing_mul a b).2 = false) :
    (overflowing_mul a b).1.toNat = a.toNat * b.toNat := by
  have hn : ¬ mulOverflows a b := by
    intro hc; rw [← overflowing_mul_snd_iff] at hc; rw [h] at hc; exact Bool.noConfusion hc
  exact toNat_wrapping_mul_of_not_overflows hn

/-! ### The saturating variant -/

/-- Saturating multiplication: the exact product, clamped at the bound `hi`. -/
def saturating_mul (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi :=
  ofNatSat hi (exactMul a b)

@[simp] theorem toNat_saturating_mul (a b : TopBoundedUInt64 hi) :
    (saturating_mul a b).toNat = min (a.toNat * b.toNat) hi.toNat := by
  unfold saturating_mul exactMul; rw [toNat_ofNatSat]

/-- Exactness: saturating multiplication returns the exact product when there is no
overflow. -/
theorem toNat_saturating_mul_of_not_overflows {a b : TopBoundedUInt64 hi}
    (h : ¬ mulOverflows a b) : (saturating_mul a b).toNat = a.toNat * b.toNat := by
  rw [toNat_saturating_mul]
  exact Nat.min_eq_left (Decidable.of_not_not h)

/-- On overflow, saturating multiplication returns the bound. -/
theorem saturating_mul_of_overflows {a b : TopBoundedUInt64 hi} (h : mulOverflows a b) :
    saturating_mul a b = maxVal hi := by
  apply ext
  rw [toNat_saturating_mul, toNat_maxVal]
  rw [mulOverflows_iff] at h
  omega

/-! ### Agreement of the four variants in the exact case -/

/-- When the exact product is representable, all four variants denote it. -/
theorem mul_variants_agree {a b c : TopBoundedUInt64 hi} (h : checked_mul a b = some c) :
    c.toNat = a.toNat * b.toNat ∧
      (wrapping_mul a b).toNat = a.toNat * b.toNat ∧
      (overflowing_mul a b).1.toNat = a.toNat * b.toNat ∧
      (overflowing_mul a b).2 = false ∧
      (saturating_mul a b).toNat = a.toNat * b.toNat := by
  have hval := toNat_of_checked_mul h
  have hn : ¬ mulOverflows a b := by
    rw [mulOverflows_iff, Nat.not_lt, ← hval]
    exact toNat_le c
  have hflag : (overflowing_mul a b).2 = false := by
    cases hb : (overflowing_mul a b).2 with
    | false => rfl
    | true => exact absurd (overflowing_mul_snd_iff.mp hb) hn
  exact ⟨hval, toNat_wrapping_mul_of_not_overflows hn,
    toNat_wrapping_mul_of_not_overflows hn, hflag,
    toNat_saturating_mul_of_not_overflows hn⟩

/-! ### Algebraic laws of wrapping multiplication -/

theorem wrapping_mul_comm (a b : TopBoundedUInt64 hi) :
    wrapping_mul a b = wrapping_mul b a := by
  apply ext; simp [Nat.mul_comm]

theorem wrapping_mul_assoc (a b c : TopBoundedUInt64 hi) :
    wrapping_mul (wrapping_mul a b) c = wrapping_mul a (wrapping_mul b c) := by
  apply ext
  simp only [toNat_wrapping_mul]
  rw [Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mul_assoc]

end TopBoundedUInt64
