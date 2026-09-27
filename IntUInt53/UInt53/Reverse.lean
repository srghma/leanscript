import IntUInt53.UInt53.Bits
import IntUInt53.TopBoundedUInt64AndBoundedInt64Common.Radix

/-!
# Reversing the bits of a `UInt53`

`reverseBits a` reverses the 53 bits of `a`: bit `i` of the result is bit
`52 - i` of `a`.  It is defined through the base-2 digit list of the value —
write the 53 bits, reverse the list, read it back — which makes the main
theorem easy to state and to prove: reversing twice is the identity, so no
information is lost.
-/

set_option autoImplicit false

namespace UInt53

/-- The 53 bits of `a`, least significant first. -/
def bits (a : UInt53) : List Nat := Radix.digits 2 53 a.toNat

@[simp] theorem length_bits (a : UInt53) : (bits a).length = 53 := by
  unfold bits; rw [Radix.length_digits]

theorem bits_lt (a : UInt53) : ∀ b ∈ bits a, b < 2 :=
  Radix.digit_lt 2 (by decide) 53 a.toNat

theorem ofDigits_bits (a : UInt53) : Radix.ofDigits 2 (bits a) = a.toNat :=
  Radix.ofDigits_digits 2 (by decide) 53 a.toNat (lt_two_pow_53 a)

/-- Read a list of 53 bits back, as a `UInt53`. -/
def ofBits (l : List Nat) (hlen : l.length = 53) (hbit : ∀ b ∈ l, b < 2) : UInt53 :=
  ofNat (Radix.ofDigits 2 l)
    (le_MAX_of_lt_two_pow_53 (by
      have h := Radix.ofDigits_lt 2 (by decide) l hbit
      rw [hlen] at h
      exact h))

@[simp] theorem toNat_ofBits (l : List Nat) (hlen : l.length = 53) (hbit : ∀ b ∈ l, b < 2) :
    (ofBits l hlen hbit).toNat = Radix.ofDigits 2 l := by
  unfold ofBits
  exact toNat_ofNat (Radix.ofDigits 2 l) _

/-- Reading back the bits of a value returns that value. -/
theorem ofBits_bits (a : UInt53) :
    ofBits (bits a) (length_bits a) (bits_lt a) = a :=
  TopBoundedUInt64.ext (by rw [toNat_ofBits, ofDigits_bits])

/-- The bits of `a`, in reverse order. -/
def reverseBits (a : UInt53) : UInt53 :=
  ofBits (bits a).reverse (by rw [List.length_reverse, length_bits])
    (fun b hb => bits_lt a b (List.mem_reverse.mp hb))

theorem bits_reverseBits (a : UInt53) : bits (reverseBits a) = (bits a).reverse := by
  unfold bits reverseBits
  have hlen : (Radix.digits 2 53 a.toNat).reverse.length = 53 := by
    rw [List.length_reverse, Radix.length_digits]
  have hbit : ∀ b ∈ (Radix.digits 2 53 a.toNat).reverse, b < 2 :=
    fun b hb => bits_lt a b (List.mem_reverse.mp hb)
  have key := Radix.digits_ofDigits 2 (by decide)
    (Radix.digits 2 53 a.toNat).reverse hbit
  rw [hlen] at key
  rw [toNat_ofBits]
  exact key

/-- **Reversal loses nothing**: reversing the bits twice is the identity. -/
theorem reverseBits_reverseBits (a : UInt53) : reverseBits (reverseBits a) = a := by
  apply TopBoundedUInt64.ext
  have h : (bits (reverseBits a)).reverse = bits a := by
    rw [bits_reverseBits, List.reverse_reverse]
  show (ofBits (bits (reverseBits a)).reverse _ _).toNat = a.toNat
  rw [toNat_ofBits, h, ofDigits_bits]

/-! ### Concretely -/

set_option maxRecDepth 10000 in
/-- Reversing the bits of `1` moves the bit to the top: `2 ^ 52`. -/
theorem reverseBits_one : reverseBits (ofNat 1) = ofNat 4503599627370496 := by decide

set_option maxRecDepth 10000 in
/-- Reversing the bits of `MAX`, all of which are set, changes nothing. -/
theorem reverseBits_max : reverseBits maxVal = maxVal := by decide

end UInt53
