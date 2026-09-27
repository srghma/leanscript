import IntUInt53.UInt53.Bits

/-!
# Rotations on `UInt53`

A `UInt53` is a 53-bit word, so rotating its bits is meaningful: the bits that
leave at the top re-enter at the bottom.  For `k ≤ 53`,

```
rotateLeft a k = (a % 2 ^ (53 - k)) * 2 ^ k + a / 2 ^ (53 - k)
```

is the exact description of that operation on the denoted number, and
`rotateRight a k = rotateLeft a (53 - k)`.

Rotation is a bijection — nothing is ever lost, unlike a shift — which is what
`rotateRight_rotateLeft` says.
-/

set_option autoImplicit false

open TopBoundedUInt64

namespace UInt53

/-- The exact value of `a` rotated left by `k` bits (for `k ≤ 53`). -/
def exactRotateLeft (a : UInt53) (k : Nat) : Nat :=
  (a.toNat % 2 ^ (53 - k)) * 2 ^ k + a.toNat / 2 ^ (53 - k)

theorem exactRotateLeft_lt {a : UInt53} {k : Nat} (hk : k ≤ 53) :
    exactRotateLeft a k < 2 ^ 53 := by
  have hsplit : 2 ^ (53 - k) * 2 ^ k = 2 ^ 53 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hlow : a.toNat % 2 ^ (53 - k) < 2 ^ (53 - k) :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have hhigh : a.toNat / 2 ^ (53 - k) < 2 ^ k := by
    refine Nat.div_lt_of_lt_mul ?_
    rw [hsplit]
    exact lt_two_pow_53 a
  have hmul : (a.toNat % 2 ^ (53 - k)) * 2 ^ k ≤ (2 ^ (53 - k) - 1) * 2 ^ k :=
    Nat.mul_le_mul_right _ (by omega)
  have hexp : (2 ^ (53 - k) - 1) * 2 ^ k + 2 ^ k = 2 ^ 53 := by
    have hone : 2 ^ (53 - k) - 1 + 1 = 2 ^ (53 - k) := by
      have := Nat.two_pow_pos (53 - k)
      omega
    calc (2 ^ (53 - k) - 1) * 2 ^ k + 2 ^ k
        = (2 ^ (53 - k) - 1 + 1) * 2 ^ k := by rw [Nat.succ_mul]
      _ = 2 ^ (53 - k) * 2 ^ k := by rw [hone]
      _ = 2 ^ 53 := hsplit
  unfold exactRotateLeft
  omega

/-- Rotate the 53 bits of `a` left by `k` places (`k ≤ 53`). -/
def rotateLeft (a : UInt53) (k : Nat) (hk : k ≤ 53 := by decide) : UInt53 :=
  TopBoundedUInt64.ofNatLe _ (exactRotateLeft a k)
    (le_MAX_of_lt_two_pow_53 (exactRotateLeft_lt hk))

/-- Rotate the 53 bits of `a` right by `k` places (`k ≤ 53`). -/
def rotateRight (a : UInt53) (k : Nat) (hk : k ≤ 53 := by decide) : UInt53 :=
  rotateLeft a (53 - k) (by omega)

@[simp] theorem toNat_rotateLeft (a : UInt53) (k : Nat) (hk : k ≤ 53) :
    (rotateLeft a k hk).toNat = exactRotateLeft a k := by
  unfold rotateLeft; exact toNat_ofNatLe _ _

@[simp] theorem toNat_rotateRight (a : UInt53) (k : Nat) (hk : k ≤ 53) :
    (rotateRight a k hk).toNat = exactRotateLeft a (53 - k) := by
  unfold rotateRight; rw [toNat_rotateLeft]

/-- **Rotation loses nothing**: rotating left by `k` and then right by `k`
returns the original value. -/
theorem rotateRight_rotateLeft (a : UInt53) (k : Nat) (hk : k ≤ 53) :
    rotateRight (rotateLeft a k hk) k hk = a := by
  apply TopBoundedUInt64.ext
  rw [toNat_rotateRight]
  have hsplit : 2 ^ (53 - k) * 2 ^ k = 2 ^ 53 := by
    rw [← Nat.pow_add]; congr 1; omega
  have hhigh : a.toNat / 2 ^ (53 - k) < 2 ^ k := by
    refine Nat.div_lt_of_lt_mul ?_
    rw [hsplit]
    exact lt_two_pow_53 a
  have hk' : 53 - (53 - k) = k := by omega
  unfold exactRotateLeft
  rw [hk', toNat_rotateLeft]
  unfold exactRotateLeft
  have hcomm : (a.toNat % 2 ^ (53 - k)) * 2 ^ k + a.toNat / 2 ^ (53 - k)
      = a.toNat / 2 ^ (53 - k) + (a.toNat % 2 ^ (53 - k)) * 2 ^ k := by
    omega
  rw [hcomm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hhigh,
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hhigh, Nat.zero_add]
  exact Nat.div_add_mod' a.toNat (2 ^ (53 - k))

/-- Rotating by `0` does nothing. -/
theorem rotateLeft_zero (a : UInt53) : rotateLeft a 0 (by decide) = a := by
  apply TopBoundedUInt64.ext
  rw [toNat_rotateLeft]
  unfold exactRotateLeft
  rw [Nat.sub_zero, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt (lt_two_pow_53 a),
    Nat.div_eq_of_lt (lt_two_pow_53 a), Nat.add_zero]

/-- Rotating by the full width does nothing either. -/
theorem rotateLeft_full (a : UInt53) : rotateLeft a 53 (by decide) = a := by
  apply TopBoundedUInt64.ext
  rw [toNat_rotateLeft]
  unfold exactRotateLeft
  rw [Nat.sub_self, Nat.pow_zero, Nat.mod_one, Nat.zero_mul, Nat.div_one, Nat.zero_add]

/-! ### Concretely -/

/-- Rotating `1` left by one place gives `2`. -/
theorem rotateLeft_one_one : rotateLeft (ofNat 1) 1 = ofNat 2 := by decide

/-- Rotating `1` right by one place brings the bit round to the top:
`2 ^ 52 = 4503599627370496`. -/
theorem rotateRight_one_one : rotateRight (ofNat 1) 1 = ofNat 4503599627370496 := by
  decide

end UInt53
