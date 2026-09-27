import IntUInt53.TopBoundedUInt64.Basic

/-!
# Subtraction on `TopBoundedUInt64`

The four variants of subtraction:

* `checked_sub`     — `none` when the exact difference is negative;
* `overflowing_sub` — the wrapped value together with a flag;
* `wrapping_sub`    — the difference taken modulo the period `hi + 1`;
* `saturating_sub`  — the exact difference, clamped at `0`.

As for addition, everything is specified through `toNat`, i.e. through exact
natural-number arithmetic, and all four variants agree with the exact
difference whenever that difference is representable.
-/

set_option autoImplicit false

namespace TopBoundedUInt64

variable {hi : UInt64}

/-- Subtraction overflows (underflows) when the subtrahend is the larger value. -/
def subOverflows (a b : TopBoundedUInt64 hi) : Prop := a.toNat < b.toNat

instance (a b : TopBoundedUInt64 hi) : Decidable (subOverflows a b) := by
  unfold subOverflows; infer_instance

/-! ### The checked variant -/

/-- Checked subtraction: `none` exactly when `a < b`. -/
def checked_sub (a b : TopBoundedUInt64 hi) : Option (TopBoundedUInt64 hi) :=
  if b.toNat ≤ a.toNat then
    some (ofNatLe hi (a.toNat - b.toNat) (Nat.le_trans (Nat.sub_le _ _) (toNat_le a)))
  else none

theorem checked_sub_eq_none_iff {a b : TopBoundedUInt64 hi} :
    checked_sub a b = none ↔ subOverflows a b := by
  unfold checked_sub subOverflows
  split <;> simp_all <;> omega

/-- Exactness: whenever checked subtraction succeeds, its result is the exact difference. -/
theorem toNat_of_checked_sub {a b c : TopBoundedUInt64 hi} (h : checked_sub a b = some c) :
    c.toNat = a.toNat - b.toNat := by
  unfold checked_sub at h
  split at h
  · rw [← Option.some.inj h, toNat_ofNatLe]
  · exact absurd h (by simp)

theorem checked_sub_eq_some_iff {a b c : TopBoundedUInt64 hi} :
    checked_sub a b = some c ↔ b.toNat ≤ a.toNat ∧ c.toNat = a.toNat - b.toNat := by
  constructor
  · intro h
    refine ⟨?_, toNat_of_checked_sub h⟩
    unfold checked_sub at h
    split at h
    · assumption
    · exact absurd h (by simp)
  · rintro ⟨hle, hv⟩
    unfold checked_sub
    rw [ite_eq_left hle]
    exact congrArg some (ext (by rw [toNat_ofNatLe, hv]))

/-- Checked subtraction succeeds, with the exact difference, when `b ≤ a`. -/
theorem checked_sub_of_not_overflows {a b : TopBoundedUInt64 hi} (h : ¬ subOverflows a b) :
    ∃ c, checked_sub a b = some c ∧ c.toNat = a.toNat - b.toNat := by
  have hle : b.toNat ≤ a.toNat := Nat.not_lt.mp h
  exact ⟨ofNatLe hi (a.toNat - b.toNat) (Nat.le_trans (Nat.sub_le _ _) (toNat_le a)),
    checked_sub_eq_some_iff.mpr ⟨hle, by simp⟩, by simp⟩

/-! ### The wrapping variant -/

/-- Wrapping subtraction: `a - b` computed modulo the period `hi + 1`.
Adding one period before subtracting keeps the computation inside `Nat`. -/
def wrapping_sub (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi :=
  ofNatWrap hi (a.toNat + (period hi - b.toNat))

@[simp] theorem toNat_wrapping_sub (a b : TopBoundedUInt64 hi) :
    (wrapping_sub a b).toNat = (a.toNat + period hi - b.toNat) % period hi := by
  unfold wrapping_sub
  rw [toNat_ofNatWrap]
  have hb := toNat_lt_period b
  have : a.toNat + (period hi - b.toNat) = a.toNat + period hi - b.toNat := by omega
  rw [this]

/-- Exactness: wrapping subtraction returns the exact difference when `b ≤ a`. -/
theorem toNat_wrapping_sub_of_not_overflows {a b : TopBoundedUInt64 hi}
    (h : ¬ subOverflows a b) : (wrapping_sub a b).toNat = a.toNat - b.toNat := by
  have hle : b.toNat ≤ a.toNat := Nat.not_lt.mp h
  have ha := toNat_lt_period a
  rw [toNat_wrapping_sub]
  have h1 : a.toNat + period hi - b.toNat = (a.toNat - b.toNat) + period hi := by omega
  rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- On underflow, wrapping subtraction adds exactly one period. -/
theorem toNat_wrapping_sub_of_overflows {a b : TopBoundedUInt64 hi} (h : subOverflows a b) :
    (wrapping_sub a b).toNat = a.toNat + period hi - b.toNat := by
  unfold subOverflows at h
  have hb := toNat_lt_period b
  rw [toNat_wrapping_sub]
  exact Nat.mod_eq_of_lt (by omega)

/-! ### The overflowing variant -/

/-- Overflowing subtraction: the wrapped value together with an underflow flag. -/
def overflowing_sub (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi × Bool :=
  (wrapping_sub a b, decide (a.toNat < b.toNat))

@[simp] theorem overflowing_sub_fst (a b : TopBoundedUInt64 hi) :
    (overflowing_sub a b).1 = wrapping_sub a b := rfl

theorem overflowing_sub_snd_iff {a b : TopBoundedUInt64 hi} :
    (overflowing_sub a b).2 = true ↔ subOverflows a b := by
  unfold overflowing_sub subOverflows; simp

/-- Exactness: if the flag is `false`, the value returned is the exact difference. -/
theorem toNat_overflowing_sub_of_not_flag {a b : TopBoundedUInt64 hi}
    (h : (overflowing_sub a b).2 = false) :
    (overflowing_sub a b).1.toNat = a.toNat - b.toNat := by
  have hn : ¬ subOverflows a b := by
    intro hc; rw [← overflowing_sub_snd_iff] at hc; rw [h] at hc; exact Bool.noConfusion hc
  exact toNat_wrapping_sub_of_not_overflows hn

/-! ### The saturating variant -/

/-- Saturating subtraction: the exact difference, clamped at `0`. -/
def saturating_sub (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi :=
  ofNatLe hi (a.toNat - b.toNat) (Nat.le_trans (Nat.sub_le _ _) (toNat_le a))

@[simp] theorem toNat_saturating_sub (a b : TopBoundedUInt64 hi) :
    (saturating_sub a b).toNat = a.toNat - b.toNat := by
  unfold saturating_sub; rw [toNat_ofNatLe]

/-- On underflow, saturating subtraction returns `0`. -/
theorem saturating_sub_of_overflows {a b : TopBoundedUInt64 hi} (h : subOverflows a b) :
    saturating_sub a b = minVal hi := by
  apply ext
  rw [toNat_saturating_sub, toNat_minVal]
  unfold subOverflows at h
  omega

/-! ### Agreement of the four variants in the exact case -/

/-- When `b ≤ a`, all four variants denote the exact difference. -/
theorem sub_variants_agree {a b c : TopBoundedUInt64 hi} (h : checked_sub a b = some c) :
    c.toNat = a.toNat - b.toNat ∧
      (wrapping_sub a b).toNat = a.toNat - b.toNat ∧
      (overflowing_sub a b).1.toNat = a.toNat - b.toNat ∧
      (overflowing_sub a b).2 = false ∧
      (saturating_sub a b).toNat = a.toNat - b.toNat := by
  obtain ⟨hle, hval⟩ := checked_sub_eq_some_iff.mp h
  have hn : ¬ subOverflows a b := by unfold subOverflows; omega
  have hflag : (overflowing_sub a b).2 = false := by
    unfold overflowing_sub; simp; omega
  exact ⟨hval, toNat_wrapping_sub_of_not_overflows hn,
    toNat_wrapping_sub_of_not_overflows hn, hflag, toNat_saturating_sub a b⟩

end TopBoundedUInt64
