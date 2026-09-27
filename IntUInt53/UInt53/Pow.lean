import IntUInt53.UInt53.Mul

/-!
# Exponentiation on `UInt53`

`a ^ k` grows quickly, so exponentiation comes in the usual four variants,
each specified through the exact natural number `a.toNat ^ k`:

* `checked_pow` — `none` when `a ^ k` exceeds `MAX`;
* `overflowing_pow`, `wrapping_pow`, `saturating_pow` — as elsewhere.

Modular exponentiation `powMod?` is separate: `a ^ k % m` is always in range
for a nonzero modulus `m`, so it is reported as `none` only on `m = 0`.  It is
computed from the exact `Nat` power, hence exact.
-/

set_option autoImplicit false

open TopBoundedUInt64

namespace UInt53

/-- The exact power of the number denoted by `a`. -/
def exactPow (a : UInt53) (k : Nat) : Nat := a.toNat ^ k

/-- Exponentiation overflows when `a ^ k` exceeds `MAX`. -/
def powOverflows (a : UInt53) (k : Nat) : Prop := MAX < exactPow a k

instance (a : UInt53) (k : Nat) : Decidable (powOverflows a k) := by
  unfold powOverflows; infer_instance

/-- Checked exponentiation: `none` exactly when `a ^ k` is out of range. -/
def checked_pow (a : UInt53) (k : Nat) : Option UInt53 := ofNat? (exactPow a k)

/-- Wrapping exponentiation: `a ^ k` reduced modulo `SIZE`. -/
def wrapping_pow (a : UInt53) (k : Nat) : UInt53 := ofNatWrap (exactPow a k)

/-- Overflowing exponentiation: the wrapped value together with a flag. -/
def overflowing_pow (a : UInt53) (k : Nat) : UInt53 × Bool :=
  (wrapping_pow a k, decide (MAX < exactPow a k))

/-- Saturating exponentiation: `a ^ k`, clamped at `MAX`. -/
def saturating_pow (a : UInt53) (k : Nat) : UInt53 := ofNatSat (exactPow a k)

theorem checked_pow_eq_some_iff {a : UInt53} {k : Nat} {c : UInt53} :
    checked_pow a k = some c ↔ c.toNat = a.toNat ^ k := ofNat?_eq_some_iff

theorem checked_pow_eq_none_iff {a : UInt53} {k : Nat} :
    checked_pow a k = none ↔ MAX < a.toNat ^ k := ofNat?_eq_none_iff

@[simp] theorem toNat_wrapping_pow (a : UInt53) (k : Nat) :
    (wrapping_pow a k).toNat = a.toNat ^ k % SIZE := by
  unfold wrapping_pow exactPow; rw [toNat_ofNatWrap]

@[simp] theorem toNat_saturating_pow (a : UInt53) (k : Nat) :
    (saturating_pow a k).toNat = min (a.toNat ^ k) MAX := by
  unfold saturating_pow exactPow; rw [toNat_ofNatSat]

theorem overflowing_pow_snd_iff {a : UInt53} {k : Nat} :
    (overflowing_pow a k).2 = true ↔ MAX < a.toNat ^ k := by
  unfold overflowing_pow exactPow; simp

/-- **All four variants of exponentiation are exact** whenever `a ^ k` is
representable. -/
theorem pow_variants_exact {a : UInt53} {k : Nat} (h : a.toNat ^ k ≤ MAX) :
    (∃ c, checked_pow a k = some c ∧ c.toNat = a.toNat ^ k) ∧
      (wrapping_pow a k).toNat = a.toNat ^ k ∧
      (overflowing_pow a k).1.toNat = a.toNat ^ k ∧
      (overflowing_pow a k).2 = false ∧
      (saturating_pow a k).toNat = a.toNat ^ k := by
  have hwrap : (wrapping_pow a k).toNat = a.toNat ^ k := by
    rw [toNat_wrapping_pow]
    exact Nat.mod_eq_of_lt (by unfold MAX at h; rw [SIZE_eq]; omega)
  refine ⟨⟨ofNat (a.toNat ^ k) h, ofNat?_eq_some_iff.mpr (by rw [toNat_ofNat]; rfl),
    by rw [toNat_ofNat]⟩, hwrap, hwrap, ?_, ?_⟩
  · cases hb : (overflowing_pow a k).2 with
    | false => rfl
    | true => exact absurd (overflowing_pow_snd_iff.mp hb) (by omega)
  · rw [toNat_saturating_pow]
    exact Nat.min_eq_left h

/-- Raising to the power `0` gives `1`. -/
theorem checked_pow_zero (a : UInt53) : checked_pow a 0 = some (ofNat 1) := by
  refine ofNat?_eq_some_iff.mpr ?_
  rw [toNat_ofNat]
  unfold exactPow
  rw [Nat.pow_zero]

/-! ### Modular exponentiation -/

/-- Modular exponentiation `a ^ k % m`, computed from the exact power; `none`
exactly when the modulus is zero. -/
def powMod? (a : UInt53) (k : Nat) (m : UInt53) : Option UInt53 :=
  if m.toNat = 0 then none else ofNat? (a.toNat ^ k % m.toNat)

/-- Modular exponentiation is exact and always succeeds for a nonzero modulus. -/
theorem powMod?_exact {a m : UInt53} {k : Nat} (h : m.toNat ≠ 0) :
    ∃ c, powMod? a k m = some c ∧ c.toNat = a.toNat ^ k % m.toNat := by
  have hlt : a.toNat ^ k % m.toNat ≤ MAX := by
    have h₁ : a.toNat ^ k % m.toNat < m.toNat := Nat.mod_lt _ (Nat.pos_of_ne_zero h)
    have h₂ := le_MAX m
    omega
  refine ⟨ofNat _ hlt, ?_, by rw [toNat_ofNat]⟩
  unfold powMod?
  rw [ite_eq_right h]
  exact ofNat?_eq_some_iff.mpr (by rw [toNat_ofNat])

theorem powMod?_eq_none_iff {a m : UInt53} {k : Nat} :
    powMod? a k m = none ↔ m.toNat = 0 := by
  unfold powMod?
  split
  · next h => simp [h]
  · next h =>
    constructor
    · intro hn
      have hlt : a.toNat ^ k % m.toNat ≤ MAX := by
        have h₁ : a.toNat ^ k % m.toNat < m.toNat := Nat.mod_lt _ (Nat.pos_of_ne_zero h)
        have h₂ := le_MAX m
        omega
      rw [ofNat?_eq_none_iff] at hn
      omega
    · intro hz; exact absurd hz h

/-! ### Exact arithmetic, concretely -/

/-- `2 ^ 10 = 1024`, exactly. -/
theorem checked_pow_two_ten : checked_pow (ofNat 2) 10 = some (ofNat 1024) := by decide

/-- `2 ^ 52` is the largest power of two that fits. -/
theorem checked_pow_two_52 :
    checked_pow (ofNat 2) 52 = some (ofNat 4503599627370496) := by decide

/-- `2 ^ 53` does not fit, and is reported. -/
theorem checked_pow_two_53 : checked_pow (ofNat 2) 53 = none := by decide

/-- `3 ^ 100 % 7 = 4`, computed exactly even though `3 ^ 100` is astronomically
larger than `MAX`. -/
theorem powMod_three_hundred : powMod? (ofNat 3) 100 (ofNat 7) = some (ofNat 4) := by
  decide

end UInt53
