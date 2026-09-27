import IntUInt53.Int53.Basic
import IntUInt53.TopBoundedUInt64AndBoundedInt64Common.Radix

/-!
# Serialising an `Int53`

Sign and magnitude: an `Int53` is stored as a sign bit together with the seven
little-endian bytes of its absolute value (seven bytes suffice because
`MAX = 2 ^ 53 - 1 < 256 ^ 7`).  This matches the symmetric range exactly — the
two representations of zero are the only redundancy, and both read back as
zero.

`ofBytes?` returns `none` on data that does not denote a value in range, and
`ofBytes?_toBytes` is the round trip.
-/

set_option autoImplicit false

namespace Int53

/-- The sign bit (`true` for negative) and the seven bytes of the magnitude. -/
def toBytes (a : Int53) : Bool × List Nat :=
  (decide (a.toInt < 0), Radix.digits 256 7 a.toInt.natAbs)

/-- Read a sign bit and a little-endian list of bytes; `none` if out of range. -/
def ofBytes? (s : Bool) (l : List Nat) : Option Int53 :=
  ofInt? (if s then -(Radix.ofDigits 256 l : Int) else (Radix.ofDigits 256 l : Int))

@[simp] theorem length_toBytes (a : Int53) : (toBytes a).2.length = 7 := by
  unfold toBytes; rw [Radix.length_digits]

/-- Every entry of `toBytes` really is a byte. -/
theorem toBytes_lt (a : Int53) : ∀ b ∈ (toBytes a).2, b < 256 :=
  Radix.digit_lt 256 (by decide) 7 a.toInt.natAbs

theorem ofDigits_toBytes (a : Int53) :
    Radix.ofDigits 256 (toBytes a).2 = a.toInt.natAbs := by
  unfold toBytes
  refine Radix.ofDigits_digits 256 (by decide) 7 a.toInt.natAbs ?_
  have h₁ := le_MAX a
  have h₂ := MIN_le a
  unfold MAX MIN at *
  omega

/-- **Round trip**: serialising and deserialising returns the original value. -/
theorem ofBytes?_toBytes (a : Int53) : ofBytes? (toBytes a).1 (toBytes a).2 = some a := by
  unfold ofBytes?
  rw [ofDigits_toBytes]
  refine ofInt?_eq_some_iff.mpr ?_
  show a.toInt = if (toBytes a).1 then -(a.toInt.natAbs : Int) else (a.toInt.natAbs : Int)
  unfold toBytes
  by_cases h : a.toInt < 0 <;> simp [h] <;> omega

/-! ### Concretely -/

/-- `-258` has sign bit `true` and magnitude bytes `2, 1, 0, …`. -/
theorem toBytes_neg_258 :
    toBytes (ofInt (-258)) = (true, [2, 1, 0, 0, 0, 0, 0]) := by decide

/-- `258` has sign bit `false` and the same magnitude bytes. -/
theorem toBytes_258 : toBytes (ofInt 258) = (false, [2, 1, 0, 0, 0, 0, 0]) := by decide

/-- Both encodings of zero read back as zero. -/
theorem ofBytes?_zero :
    ofBytes? true [0, 0, 0, 0, 0, 0, 0] = some zero ∧
      ofBytes? false [0, 0, 0, 0, 0, 0, 0] = some zero := by
  constructor <;> decide

/-- A magnitude above `MAX` is rejected. -/
theorem ofBytes?_out_of_range : ofBytes? false [0, 0, 0, 0, 0, 0, 255] = none := by decide

end Int53
