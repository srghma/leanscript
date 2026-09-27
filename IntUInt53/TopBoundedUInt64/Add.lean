import IntUInt53.TopBoundedUInt64.Basic

/-!
# Addition on `TopBoundedUInt64`

The four variants of addition, in the style of the rest of the development:

* `checked_add`     — `none` when the exact sum does not fit;
* `overflowing_add` — the wrapped value together with a flag;
* `wrapping_add`    — reduction modulo the period `hi + 1`;
* `saturating_add`  — the exact sum, clamped at `hi`.

Each is specified by the natural number it denotes, so every statement below is
about exact arithmetic on `Nat`: no rounding, no approximation, no drift.
Whenever the exact sum is representable, all four variants return it.
-/

set_option autoImplicit false

namespace TopBoundedUInt64

variable {hi : UInt64}

/-- The exact sum of the numbers denoted by `a` and `b`. -/
def exactAdd (a b : TopBoundedUInt64 hi) : Nat := a.toNat + b.toNat

/-- Addition overflows when the exact sum exceeds the bound. -/
def addOverflows (a b : TopBoundedUInt64 hi) : Prop := ¬ InRange hi (exactAdd a b)

instance (a b : TopBoundedUInt64 hi) : Decidable (addOverflows a b) := by
  unfold addOverflows; infer_instance

theorem addOverflows_iff {a b : TopBoundedUInt64 hi} :
    addOverflows a b ↔ hi.toNat < a.toNat + b.toNat := by
  unfold addOverflows InRange exactAdd; omega

/-! ### The checked variant -/

/-- Checked addition: `none` exactly when the exact sum is out of range. -/
def checked_add (a b : TopBoundedUInt64 hi) : Option (TopBoundedUInt64 hi) :=
  ofNat? hi (exactAdd a b)

theorem checked_add_eq_some_iff {a b c : TopBoundedUInt64 hi} :
    checked_add a b = some c ↔ c.toNat = a.toNat + b.toNat :=
  ofNat?_eq_some_iff

/-- Exactness: whenever checked addition succeeds, its result is the exact sum. -/
theorem toNat_of_checked_add {a b c : TopBoundedUInt64 hi} (h : checked_add a b = some c) :
    c.toNat = a.toNat + b.toNat := checked_add_eq_some_iff.mp h

theorem checked_add_eq_none_iff {a b : TopBoundedUInt64 hi} :
    checked_add a b = none ↔ addOverflows a b := ofNat?_eq_none_iff

theorem checked_add_isSome_iff {a b : TopBoundedUInt64 hi} :
    (checked_add a b).isSome ↔ ¬ addOverflows a b := by
  cases h : checked_add a b with
  | none => simp [checked_add_eq_none_iff.mp h]
  | some c =>
    have : ¬ addOverflows a b := by
      rw [addOverflows_iff, Nat.not_lt, ← toNat_of_checked_add h]
      exact toNat_le c
    simp [this]

/-- Checked addition succeeds, with the exact sum, whenever that sum is in range. -/
theorem checked_add_of_not_overflows {a b : TopBoundedUInt64 hi} (h : ¬ addOverflows a b) :
    ∃ c, checked_add a b = some c ∧ c.toNat = a.toNat + b.toNat := by
  have hr : InRange hi (exactAdd a b) := by
    unfold addOverflows at h; exact Decidable.of_not_not h
  exact ⟨ofNatLe hi (exactAdd a b) hr, ofNat?_of_inRange hr, by simp [exactAdd]⟩

/-! ### The wrapping variant -/

/-- Wrapping addition: the exact sum reduced modulo the period `hi + 1`. -/
def wrapping_add (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi :=
  ofNatWrap hi (exactAdd a b)

@[simp] theorem toNat_wrapping_add (a b : TopBoundedUInt64 hi) :
    (wrapping_add a b).toNat = (a.toNat + b.toNat) % period hi := by
  unfold wrapping_add exactAdd; rw [toNat_ofNatWrap]

/-- Exactness: wrapping addition returns the exact sum when there is no overflow. -/
theorem toNat_wrapping_add_of_not_overflows {a b : TopBoundedUInt64 hi}
    (h : ¬ addOverflows a b) : (wrapping_add a b).toNat = a.toNat + b.toNat := by
  rw [toNat_wrapping_add]
  exact Nat.mod_eq_of_lt (inRange_iff_lt_period.mp (Decidable.of_not_not h))

/-- On overflow, wrapping addition subtracts exactly one period. -/
theorem toNat_wrapping_add_of_overflows {a b : TopBoundedUInt64 hi} (h : addOverflows a b) :
    (wrapping_add a b).toNat = a.toNat + b.toNat - period hi := by
  rw [toNat_wrapping_add]
  rw [addOverflows_iff] at h
  have hb := toNat_le a
  have hb' := toNat_le b
  have hp : period hi = hi.toNat + 1 := rfl
  have h1 : a.toNat + b.toNat - period hi < period hi := by omega
  have h2 : a.toNat + b.toNat = (a.toNat + b.toNat - period hi) + period hi := by omega
  rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt h1]
  omega

/-! ### The overflowing variant -/

/-- Overflowing addition: the wrapped value together with an overflow flag. -/
def overflowing_add (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi × Bool :=
  (wrapping_add a b, decide (hi.toNat < exactAdd a b))

@[simp] theorem overflowing_add_fst (a b : TopBoundedUInt64 hi) :
    (overflowing_add a b).1 = wrapping_add a b := rfl

/-- The flag says exactly whether the addition overflowed. -/
theorem overflowing_add_snd_iff {a b : TopBoundedUInt64 hi} :
    (overflowing_add a b).2 = true ↔ addOverflows a b := by
  unfold overflowing_add exactAdd
  rw [addOverflows_iff]
  simp

/-- Exactness: if the flag is `false`, the value returned is the exact sum. -/
theorem toNat_overflowing_add_of_not_flag {a b : TopBoundedUInt64 hi}
    (h : (overflowing_add a b).2 = false) :
    (overflowing_add a b).1.toNat = a.toNat + b.toNat := by
  have hn : ¬ addOverflows a b := by
    intro hc; rw [← overflowing_add_snd_iff] at hc; rw [h] at hc; exact Bool.noConfusion hc
  exact toNat_wrapping_add_of_not_overflows hn

/-! ### The saturating variant -/

/-- Saturating addition: the exact sum, clamped at the bound `hi`. -/
def saturating_add (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi :=
  ofNatSat hi (exactAdd a b)

@[simp] theorem toNat_saturating_add (a b : TopBoundedUInt64 hi) :
    (saturating_add a b).toNat = min (a.toNat + b.toNat) hi.toNat := by
  unfold saturating_add exactAdd; rw [toNat_ofNatSat]

/-- Exactness: saturating addition returns the exact sum when there is no overflow. -/
theorem toNat_saturating_add_of_not_overflows {a b : TopBoundedUInt64 hi}
    (h : ¬ addOverflows a b) : (saturating_add a b).toNat = a.toNat + b.toNat := by
  rw [toNat_saturating_add]
  exact Nat.min_eq_left (Decidable.of_not_not h)

/-- On overflow, saturating addition returns the bound. -/
theorem saturating_add_of_overflows {a b : TopBoundedUInt64 hi} (h : addOverflows a b) :
    saturating_add a b = maxVal hi := by
  apply ext
  rw [toNat_saturating_add, toNat_maxVal]
  rw [addOverflows_iff] at h
  omega

/-! ### Agreement of the four variants in the exact case -/

/-- When the exact sum is representable, all four variants denote it. -/
theorem add_variants_agree {a b c : TopBoundedUInt64 hi} (h : checked_add a b = some c) :
    c.toNat = a.toNat + b.toNat ∧
      (wrapping_add a b).toNat = a.toNat + b.toNat ∧
      (overflowing_add a b).1.toNat = a.toNat + b.toNat ∧
      (overflowing_add a b).2 = false ∧
      (saturating_add a b).toNat = a.toNat + b.toNat := by
  have hval := toNat_of_checked_add h
  have hn : ¬ addOverflows a b := by
    rw [addOverflows_iff, Nat.not_lt, ← hval]
    exact toNat_le c
  have hflag : (overflowing_add a b).2 = false := by
    have := overflowing_add_snd_iff (a := a) (b := b)
    cases hb : (overflowing_add a b).2 with
    | false => rfl
    | true => exact absurd (this.mp hb) hn
  exact ⟨hval, toNat_wrapping_add_of_not_overflows hn,
    toNat_wrapping_add_of_not_overflows hn, hflag,
    toNat_saturating_add_of_not_overflows hn⟩

/-! ### Algebraic laws of wrapping addition -/

theorem wrapping_add_comm (a b : TopBoundedUInt64 hi) :
    wrapping_add a b = wrapping_add b a := by
  apply ext; simp [Nat.add_comm]

theorem wrapping_add_assoc (a b c : TopBoundedUInt64 hi) :
    wrapping_add (wrapping_add a b) c = wrapping_add a (wrapping_add b c) := by
  apply ext
  simp only [toNat_wrapping_add]
  rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

theorem wrapping_add_minVal (a : TopBoundedUInt64 hi) : wrapping_add a (minVal hi) = a := by
  apply ext
  simp only [toNat_wrapping_add, toNat_minVal, Nat.add_zero]
  exact Nat.mod_eq_of_lt (toNat_lt_period a)

end TopBoundedUInt64
