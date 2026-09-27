import IntUInt53.UInt53.Bits
import IntUInt53.UInt53.Log
import IntUInt53.TopBoundedUInt64AndBoundedInt64Common.NatBits

/-!
# Counting bits of a `UInt53`

* `popCount a` — the number of one bits, at most `53`;
* `trailingZeros a` — the number of trailing zero bits (`53` at `0`), with the
  bit at that position set and every lower bit clear;
* `leadingZeros a` — the number of leading zero bits within the 53-bit width
  (`53` at `0`), characterised through the binary logarithm.
-/

set_option autoImplicit false

namespace UInt53

/-- The number of one bits of a `UInt53`. -/
def popCount (a : UInt53) : Nat := NatBits.popCountFuel 53 a.toNat

theorem popCount_eq (a : UInt53) : popCount a = NatBits.popCount a.toNat :=
  NatBits.popCountFuel_eq 53 a.toNat (lt_two_pow_53 a)

/-- A `UInt53` has at most `53` one bits. -/
theorem popCount_le (a : UInt53) : popCount a ≤ 53 := by
  rw [popCount_eq]
  exact NatBits.popCount_le 53 a.toNat (lt_two_pow_53 a)

/-- Only zero has no one bits. -/
theorem popCount_eq_zero_iff {a : UInt53} : popCount a = 0 ↔ a = minVal := by
  rw [popCount_eq, NatBits.popCount_eq_zero_iff, TopBoundedUInt64.ext_iff, toNat_minVal]
  rfl

/-- The number of trailing zero bits; `53` for the value `0`. -/
def trailingZeros (a : UInt53) : Nat :=
  if a.toNat = 0 then 53 else NatBits.ctzFuel 53 a.toNat

theorem trailingZeros_of_ne_zero {a : UInt53} (h : a.toNat ≠ 0) :
    trailingZeros a = NatBits.ctz a.toNat := by
  unfold trailingZeros
  rw [ite_eq_right h]
  exact NatBits.ctzFuel_eq 53 a.toNat (lt_two_pow_53 a)

/-- For a nonzero value the bit at `trailingZeros` is set. -/
theorem testBit_trailingZeros {a : UInt53} (h : a.toNat ≠ 0) :
    a.toNat.testBit (trailingZeros a) = true := by
  rw [trailingZeros_of_ne_zero h]
  exact NatBits.testBit_ctz a.toNat h

/-- Every bit below `trailingZeros` is clear. -/
theorem testBit_lt_trailingZeros {a : UInt53} {i : Nat} (h : a.toNat ≠ 0)
    (hi : i < trailingZeros a) : a.toNat.testBit i = false := by
  rw [trailingZeros_of_ne_zero h] at hi
  exact NatBits.testBit_lt_ctz a.toNat i hi

/-- The number of leading zero bits within the 53-bit width; `53` at `0`. -/
def leadingZeros (a : UInt53) : Nat :=
  if a.toNat = 0 then 53 else 52 - ilog2 a

/-- For a nonzero value, the leading zeros count the positions above the
highest set bit: `2 ^ (52 - leadingZeros a) ≤ a < 2 ^ (53 - leadingZeros a)`. -/
theorem leadingZeros_spec {a : UInt53} (h : a.toNat ≠ 0) :
    2 ^ (52 - leadingZeros a) ≤ a.toNat ∧ a.toNat < 2 ^ (53 - leadingZeros a) := by
  have hle : ilog2 a ≤ 52 := ilog2_le a
  have hspec := ilog2_spec h
  unfold leadingZeros
  rw [ite_eq_right h]
  have h₁ : 52 - (52 - ilog2 a) = ilog2 a := by omega
  have h₂ : 53 - (52 - ilog2 a) = ilog2 a + 1 := by omega
  rw [h₁, h₂]
  exact hspec

/-- The leading zeros of a nonzero value are at most `52`. -/
theorem leadingZeros_le {a : UInt53} (h : a.toNat ≠ 0) : leadingZeros a ≤ 52 := by
  unfold leadingZeros
  rw [ite_eq_right h]
  omega

/-! ### Concretely -/

/-- `popCount 7 = 3`. -/
theorem popCount_seven : popCount (ofNat 7) = 3 := by decide

/-- `popCount MAX = 53`: every bit of the largest value is set. -/
theorem popCount_max : popCount maxVal = 53 := by decide

/-- `8 = 2 ^ 3` has three trailing zeros. -/
theorem trailingZeros_eight : trailingZeros (ofNat 8) = 3 := by decide

/-- Zero has all `53` bits zero, leading and trailing. -/
theorem zeros_of_minVal : trailingZeros minVal = 53 ∧ leadingZeros minVal = 53 := by
  constructor <;> decide

/-- `1` has `52` leading zeros. -/
theorem leadingZeros_one : leadingZeros (ofNat 1) = 52 := by decide

end UInt53
