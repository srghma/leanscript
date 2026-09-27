import IntUInt53.UInt53.Basic
import IntUInt53.TopBoundedUInt64AndBoundedInt64Common.Radix

/-!
# Serialising a `UInt53`

Two positional representations, both with a proved round trip.

* **Bytes.**  `toBytes a` is the little-endian list of the seven bytes of `a`;
  seven bytes suffice because `2 ^ 53 ≤ 256 ^ 7 = 2 ^ 56`.  `ofBytes?` reads
  such a list back, returning `none` on a list that does not denote a value in
  range.
* **Decimal digits.**  `toDecimal a` is the little-endian list of sixteen
  decimal digits of `a` (`MAX < 10 ^ 16`), and `ofDecimal?` reads it back.

The round-trip theorems `ofBytes?_toBytes` and `ofDecimal?_toDecimal` say that
nothing is lost in either direction, and the digits are proved to be genuine
digits (`< 256`, respectively `< 10`).
-/

set_option autoImplicit false

namespace UInt53

/-! ### Bytes -/

/-- The seven bytes of a `UInt53`, least significant first. -/
def toBytes (a : UInt53) : List Nat := Radix.digits 256 7 a.toNat

/-- Read a little-endian list of bytes; `none` if the value is out of range. -/
def ofBytes? (l : List Nat) : Option UInt53 := ofNat? (Radix.ofDigits 256 l)

@[simp] theorem length_toBytes (a : UInt53) : (toBytes a).length = 7 := by
  unfold toBytes; rw [Radix.length_digits]

/-- Every entry of `toBytes` really is a byte. -/
theorem toBytes_lt (a : UInt53) : ∀ b ∈ toBytes a, b < 256 :=
  Radix.digit_lt 256 (by decide) 7 a.toNat

/-- Reading the bytes back gives the exact value. -/
theorem ofDigits_toBytes (a : UInt53) : Radix.ofDigits 256 (toBytes a) = a.toNat := by
  unfold toBytes
  refine Radix.ofDigits_digits 256 (by decide) 7 a.toNat ?_
  have := le_MAX a
  unfold MAX at this
  omega

/-- **Round trip**: serialising and deserialising returns the original value. -/
theorem ofBytes?_toBytes (a : UInt53) : ofBytes? (toBytes a) = some a := by
  unfold ofBytes?
  rw [ofDigits_toBytes]
  exact ofNat?_eq_some_iff.mpr rfl

/-! ### Decimal digits -/

/-- The sixteen decimal digits of a `UInt53`, least significant first. -/
def toDecimal (a : UInt53) : List Nat := Radix.digits 10 16 a.toNat

/-- Read a little-endian list of decimal digits; `none` if out of range. -/
def ofDecimal? (l : List Nat) : Option UInt53 := ofNat? (Radix.ofDigits 10 l)

@[simp] theorem length_toDecimal (a : UInt53) : (toDecimal a).length = 16 := by
  unfold toDecimal; rw [Radix.length_digits]

/-- Every entry of `toDecimal` really is a decimal digit. -/
theorem toDecimal_lt (a : UInt53) : ∀ d ∈ toDecimal a, d < 10 :=
  Radix.digit_lt 10 (by decide) 16 a.toNat

theorem ofDigits_toDecimal (a : UInt53) : Radix.ofDigits 10 (toDecimal a) = a.toNat := by
  unfold toDecimal
  refine Radix.ofDigits_digits 10 (by decide) 16 a.toNat ?_
  have := le_MAX a
  unfold MAX at this
  omega

/-- **Round trip** for the decimal representation. -/
theorem ofDecimal?_toDecimal (a : UInt53) : ofDecimal? (toDecimal a) = some a := by
  unfold ofDecimal?
  rw [ofDigits_toDecimal]
  exact ofNat?_eq_some_iff.mpr rfl

/-! ### Concretely -/

/-- `258 = 2 + 1 * 256`, so its bytes are `2, 1, 0, 0, 0, 0, 0`. -/
theorem toBytes_258 : toBytes (ofNat 258) = [2, 1, 0, 0, 0, 0, 0] := by decide

/-- The decimal digits of `1234`, least significant first. -/
theorem toDecimal_1234 :
    toDecimal (ofNat 1234) = [4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide

/-- A byte list denoting a number above `MAX` is rejected. -/
theorem ofBytes?_out_of_range :
    ofBytes? [0, 0, 0, 0, 0, 0, 255] = none := by decide

end UInt53
