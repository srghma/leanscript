import IntUInt53.UInt53.Div
import IntUInt53.UInt53.Pow

/-!
# Logarithms and rounding on `UInt53`

Three operations that are often wanted next to the arithmetic ones, each with
its full specification:

* `ilog2 a` — the floor of the binary logarithm, characterised by
  `2 ^ ilog2 a ≤ a < 2 ^ (ilog2 a + 1)` for `a ≠ 0`;
* `next_multiple_of` — the least multiple of `b` that is at least `a`, in the
  usual four variants because that multiple can exceed `MAX`;
* `next_power_of_two` — the least power of two that is at least `a`, checked
  and saturating.
-/

set_option autoImplicit false

open TopBoundedUInt64

namespace UInt53

/-! ### The binary logarithm -/

/-- The floor of the binary logarithm of a `UInt53` (`0` at `0`). -/
def ilog2 (a : UInt53) : Nat := a.toNat.log2

/-- The defining property of `ilog2`: it is the exponent of the largest power
of two below `a`. -/
theorem ilog2_spec {a : UInt53} (h : a.toNat ≠ 0) :
    2 ^ ilog2 a ≤ a.toNat ∧ a.toNat < 2 ^ (ilog2 a + 1) :=
  ⟨Nat.log2_self_le h, Nat.lt_log2_self⟩

/-- The binary logarithm of a `UInt53` is at most `52`. -/
theorem ilog2_le (a : UInt53) : ilog2 a ≤ 52 := by
  by_cases h : a.toNat = 0
  · unfold ilog2; rw [h]; decide
  · have h₁ : 2 ^ ilog2 a ≤ a.toNat := Nat.log2_self_le h
    have h₂ := le_MAX a
    unfold MAX at h₂
    refine Decidable.byContradiction (fun hc => ?_)
    have h₃ : (2 : Nat) ^ 53 ≤ 2 ^ ilog2 a :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega

/-! ### Rounding up to a multiple -/

/-- The least multiple of `b` that is at least `a` (equal to `a` when `b` is `0`). -/
def exactNextMultiple (a b : UInt53) : Nat :=
  if b.toNat = 0 then a.toNat else a.toNat + (b.toNat - a.toNat % b.toNat) % b.toNat

/-- Checked rounding up: `none` when the multiple exceeds `MAX`. -/
def checked_next_multiple_of (a b : UInt53) : Option UInt53 :=
  ofNat? (exactNextMultiple a b)

/-- Wrapping rounding up. -/
def wrapping_next_multiple_of (a b : UInt53) : UInt53 := ofNatWrap (exactNextMultiple a b)

/-- Overflowing rounding up: the wrapped value together with a flag. -/
def overflowing_next_multiple_of (a b : UInt53) : UInt53 × Bool :=
  (wrapping_next_multiple_of a b, decide (MAX < exactNextMultiple a b))

/-- Saturating rounding up. -/
def saturating_next_multiple_of (a b : UInt53) : UInt53 :=
  ofNatSat (exactNextMultiple a b)

/-- The rounded value is a multiple of `b`, at least `a`, and less than `a + b`;
these three properties characterise the least multiple of `b` above `a`. -/
theorem exactNextMultiple_spec {a b : UInt53} (h : b.toNat ≠ 0) :
    exactNextMultiple a b % b.toNat = 0 ∧
      a.toNat ≤ exactNextMultiple a b ∧
      exactNextMultiple a b < a.toNat + b.toNat := by
  have hb : 0 < b.toNat := Nat.pos_of_ne_zero h
  unfold exactNextMultiple
  rw [ite_eq_right h]
  have hr : a.toNat % b.toNat < b.toNat := Nat.mod_lt _ hb
  have hkey : (b.toNat - a.toNat % b.toNat) % b.toNat
      = if a.toNat % b.toNat = 0 then 0 else b.toNat - a.toNat % b.toNat := by
    by_cases h0 : a.toNat % b.toNat = 0
    · rw [ite_eq_left h0, h0, Nat.sub_zero, Nat.mod_self]
    · rw [ite_eq_right h0, Nat.mod_eq_of_lt (by omega)]
  rw [hkey]
  by_cases h0 : a.toNat % b.toNat = 0
  · rw [ite_eq_left h0, Nat.add_zero]
    exact ⟨h0, Nat.le_refl _, by omega⟩
  · rw [ite_eq_right h0]
    refine ⟨?_, by omega, by omega⟩
    have hthis : a.toNat + (b.toNat - a.toNat % b.toNat)
        = b.toNat + b.toNat * (a.toNat / b.toNat) := by
      have := Nat.div_add_mod a.toNat b.toNat
      omega
    rw [hthis, Nat.add_mul_mod_self_left, Nat.mod_self]

/-- **All four variants agree** whenever the rounded value is representable. -/
theorem next_multiple_of_variants_exact {a b : UInt53}
    (h : exactNextMultiple a b ≤ MAX) :
    (∃ c, checked_next_multiple_of a b = some c ∧ c.toNat = exactNextMultiple a b) ∧
      (wrapping_next_multiple_of a b).toNat = exactNextMultiple a b ∧
      (overflowing_next_multiple_of a b).1.toNat = exactNextMultiple a b ∧
      (overflowing_next_multiple_of a b).2 = false ∧
      (saturating_next_multiple_of a b).toNat = exactNextMultiple a b := by
  have hwrap : (wrapping_next_multiple_of a b).toNat = exactNextMultiple a b := by
    unfold wrapping_next_multiple_of
    rw [toNat_ofNatWrap]
    exact Nat.mod_eq_of_lt (by unfold MAX at h; rw [SIZE_eq]; omega)
  refine ⟨⟨ofNat _ h, ofNat?_eq_some_iff.mpr (by rw [toNat_ofNat]), by rw [toNat_ofNat]⟩,
    hwrap, hwrap, ?_, ?_⟩
  · unfold overflowing_next_multiple_of
    simpa using by omega
  · unfold saturating_next_multiple_of
    rw [toNat_ofNatSat]
    exact Nat.min_eq_left h

/-! ### Rounding up to a power of two -/

/-- The least power of two that is at least `a`. -/
def exactNextPowerOfTwo (a : UInt53) : Nat :=
  if a.toNat ≤ 1 then 1 else 2 ^ (Nat.log2 (a.toNat - 1) + 1)

/-- Checked rounding up to a power of two: `none` when it exceeds `MAX`. -/
def checked_next_power_of_two (a : UInt53) : Option UInt53 :=
  ofNat? (exactNextPowerOfTwo a)

/-- Saturating rounding up to a power of two. -/
def saturating_next_power_of_two (a : UInt53) : UInt53 :=
  ofNatSat (exactNextPowerOfTwo a)

/-- The result is a power of two and is at least `a`. -/
theorem exactNextPowerOfTwo_spec (a : UInt53) :
    (∃ k, exactNextPowerOfTwo a = 2 ^ k) ∧ a.toNat ≤ exactNextPowerOfTwo a := by
  unfold exactNextPowerOfTwo
  by_cases h : a.toNat ≤ 1
  · rw [ite_eq_left h]
    exact ⟨⟨0, rfl⟩, by omega⟩
  · rw [ite_eq_right h]
    refine ⟨⟨Nat.log2 (a.toNat - 1) + 1, rfl⟩, ?_⟩
    have := Nat.lt_log2_self (n := a.toNat - 1)
    omega

/-- It is the *least* such power: halving it drops below `a` (for `a ≥ 2`). -/
theorem exactNextPowerOfTwo_least {a : UInt53} (h : 2 ≤ a.toNat) :
    2 ^ (Nat.log2 (a.toNat - 1)) < a.toNat := by
  have h₁ : a.toNat - 1 ≠ 0 := by omega
  have := Nat.log2_self_le h₁
  omega

/-! ### Exact arithmetic, concretely -/

/-- `ilog2 1024 = 10`. -/
theorem ilog2_1024 : ilog2 (ofNat 1024) = 10 := by decide

/-- The next multiple of `7` at or above `10` is `14`. -/
theorem next_multiple_ten_seven :
    checked_next_multiple_of (ofNat 10) (ofNat 7) = some (ofNat 14) := by decide

/-- A value that is already a multiple is left alone. -/
theorem next_multiple_fourteen_seven :
    checked_next_multiple_of (ofNat 14) (ofNat 7) = some (ofNat 14) := by decide

/-- Rounding `MAX` up to a multiple of `2` overflows, and is reported. -/
theorem next_multiple_max_two :
    checked_next_multiple_of maxVal (ofNat 2) = none := by decide

/-- The next power of two at or above `1000` is `1024`. -/
theorem next_power_of_two_1000 :
    checked_next_power_of_two (ofNat 1000) = some (ofNat 1024) := by decide

/-- Above `2 ^ 52` there is no representable power of two, and this is reported. -/
theorem next_power_of_two_max : checked_next_power_of_two maxVal = none := by decide

end UInt53
