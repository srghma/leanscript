module

public import RuntimeSpec.Model

@[expose] public section

set_option autoImplicit false

/-!
# The arithmetic of the unsigned fixed-width integers written inline

The backend writes the arithmetic and bitwise operations of `UInt8`, `UInt16`, `UInt32` and (at
the `BigInt` representation) `UInt64` inline (`scripts/js_ops_inline.json`), instead of calling
their functions in `runtime.js`; each operand is read once, from left to right, so the inline
form computes its arguments exactly as a call does:

| operation | `UInt8` (`UInt16`: `65535`) | `UInt32` | `UInt64` (`BigInt`) |
|---|---|---|---|
| `add` | `(a + b) & 255` | `(a + b) >>> 0` | `BigInt.asUintN(64, a + b)` |
| `sub` | `(a - b) & 255` | `(a - b) >>> 0` | `BigInt.asUintN(64, a - b)` |
| `mul` | `(a * b) & 255` | `Math.imul(a, b) >>> 0` | `BigInt.asUintN(64, a * b)` |
| `neg` | `-a & 255` | `-a >>> 0` | `BigInt.asUintN(64, -a)` |
| `complement` | `~a & 255` | `~a >>> 0` | `BigInt.asUintN(64, ~a)` |
| `land` | `a & b` | `(a & b) >>> 0` | `a & b` |
| `lor` | `a \| b` | `(a \| b) >>> 0` | `a \| b` |
| `xor` | `a ^ b` | `(a ^ b) >>> 0` | `a ^ b` |

Most are the bodies of the functions of `runtime.js`; the bitwise operations of `UInt8`,
`UInt16` and `UInt64` drop the final mask (`& 255`, `BigInt.asUintN(64, …)`) of the runtime,
which is the identity on the result of a bitwise operation of two values of the width.

These theorems prove each form equal to the Lean operation in the model of `RuntimeSpec.Model`
(a `uint8`/`uint16`/`uint32` is a value's `toNat`, so is a `BigInt` `UInt64`), on every
argument of the representation.  The model is extended by `Math.imul`, by `~` on a `number`,
and by the bitwise operators of `BigInt` on non-negative values.
-/

namespace RuntimeSpec

/-- `Math.imul(x, y)`: the product of `ToInt32(x)` and `ToInt32(y)` modulo `2^32`, read back
signed. -/
def imul (x y : Int) : Int := (toI32 x * toI32 y).toInt

/-- `~x` on a `number`: the complement of `ToInt32(x)`, read back signed. -/
def bnot (x : Int) : Int := (~~~toI32 x).toInt

/-- `x & y` on two non-negative `BigInt`s: the bitwise and of the naturals. -/
def bigAnd (x y : Nat) : Nat := x &&& y
/-- `x | y` on two non-negative `BigInt`s. -/
def bigOr (x y : Nat) : Nat := x ||| y
/-- `x ^ y` on two non-negative `BigInt`s. -/
def bigXor (x y : Nat) : Nat := x ^^^ y

/-! ## Helpers -/

private theorem toInt_small (v : BitVec 32) (h : v.toNat < 2 ^ 31) : v.toInt = v.toNat := by
  rw [BitVec.toInt_eq_toNat_cond]; split <;> omega

private theorem toI32_nat (n : Nat) (h : n < 2 ^ 32) : (toI32 n).toNat = n := by
  rw [toI32, BitVec.ofInt_natCast, BitVec.toNat_ofNat]; omega

private theorem toI32_toNat_int (x : Int) : ((toI32 x).toNat : Int) = x % 4294967296 := by
  simp [toI32, BitVec.toNat_ofInt]; omega

private theorem toI32_toInt (v : BitVec 32) : toI32 v.toInt = v := BitVec.ofInt_toInt

private theorem ushr_zero (x : Int) : ushr x 0 = ((toI32 x).toNat : Int) := by
  simp [ushr, shiftCount, toI32]

private theorem ushr_zero_mod (x : Int) : ushr x 0 = x % 4294967296 := by
  rw [ushr_zero, toI32_toNat_int]

private theorem toI32_uint32 (a : UInt32) : toI32 (a.toNat : Int) = a.toBitVec := by
  rw [toI32, BitVec.ofInt_natCast]; simp

/-- `x & (2^k - 1)` is `x` modulo `2^k`, for `k ≤ 31`. -/
private theorem band_mask (x : Int) (k : Nat) (hk : k ≤ 31) :
    band x (2 ^ k - 1 : Nat) = x % (2 ^ k : Nat) := by
  have hk' : 2 ^ k ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) hk
  have h1 : (toI32 x &&& toI32 ((2 ^ k - 1 : Nat) : Int)).toNat = (toI32 x).toNat % 2 ^ k := by
    rw [BitVec.toNat_and, toI32_nat _ (by omega), Nat.and_two_pow_sub_one_eq_mod]
  have hlt := Nat.mod_lt (toI32 x).toNat (Nat.two_pow_pos k)
  rw [band, toInt_small _ (by rw [h1]; omega), h1, Int.natCast_emod, toI32_toNat_int]
  have hd : ((2 ^ k : Nat) : Int) ∣ 4294967296 := by
    have : (2 ^ k : Nat) ∣ 2 ^ 32 := Nat.pow_dvd_pow 2 (by omega)
    exact Int.natCast_dvd_natCast.mpr this
  exact Int.emod_emod_of_dvd x hd

/-- `~a` of a value below `2^31` is `-a - 1`. -/
private theorem bnot_small (a : Nat) (h : a < 2 ^ 31) : bnot a = -(a : Int) - 1 := by
  rw [bnot, BitVec.toInt_not, toI32_nat _ (by omega)]
  simp only [Int.bmod, Nat.reducePow]
  split <;> omega

private theorem band255 (x : Int) : band x 255 = x % 256 := band_mask x 8 (by decide)
private theorem band65535 (x : Int) : band x 65535 = x % 65536 := band_mask x 16 (by decide)

/-- A bitwise operation of two values below `2^k` (`k ≤ 31`) on `number`s is the one of the
naturals. -/
private theorem bitwise_small (op : BitVec 32 → BitVec 32 → BitVec 32) (f : Nat → Nat → Nat)
    (hop : ∀ u v : BitVec 32, (op u v).toNat = f u.toNat v.toNat) (k : Nat) (hk : k ≤ 31)
    (a b : Nat) (ha : a < 2 ^ k) (hb : b < 2 ^ k) (hf : f a b < 2 ^ k) :
    (op (toI32 a) (toI32 b)).toInt = (f a b : Int) := by
  have hk' : 2 ^ k ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) hk
  have h1 : (op (toI32 a) (toI32 b)).toNat = f a b := by
    rw [hop, toI32_nat _ (by omega), toI32_nat _ (by omega)]
  rw [toInt_small _ (by rw [h1]; omega), h1]

/-! ## `UInt32` -/

/-- `(a + b) >>> 0` is `UInt32.add`. -/
theorem uint32_add_inline (a b : UInt32) :
    ushr ((a.toNat : Int) + b.toNat) 0 = ((a + b).toNat : Int) := by
  rw [ushr_zero_mod, UInt32.toNat_add]; simp only [Nat.reducePow] at *; omega

/-- `(a - b) >>> 0` is `UInt32.sub`. -/
theorem uint32_sub_inline (a b : UInt32) :
    ushr ((a.toNat : Int) - b.toNat) 0 = ((a - b).toNat : Int) := by
  rw [ushr_zero_mod, UInt32.toNat_sub]
  have : a.toNat < 4294967296 := a.toNat_lt
  have : b.toNat < 4294967296 := b.toNat_lt
  simp only [Nat.reducePow] at *; omega

/-- `Math.imul(a, b) >>> 0` is `UInt32.mul`. -/
theorem uint32_mul_inline (a b : UInt32) :
    ushr (imul a.toNat b.toNat) 0 = ((a * b).toNat : Int) := by
  rw [ushr_zero, imul, toI32_toInt, toI32_uint32, toI32_uint32]; rfl

/-- `-a >>> 0` is `UInt32.neg`. -/
theorem uint32_neg_inline (a : UInt32) : ushr (-(a.toNat : Int)) 0 = ((-a).toNat : Int) := by
  rw [ushr_zero_mod, UInt32.toNat_neg]
  have : a.toNat < 4294967296 := a.toNat_lt
  simp only [UInt32.size] at *; omega

/-- `~a >>> 0` is `UInt32.complement`. -/
theorem uint32_complement_inline (a : UInt32) :
    ushr (bnot a.toNat) 0 = ((~~~a).toNat : Int) := by
  rw [ushr_zero, bnot, toI32_toInt, toI32_uint32]; rfl

/-- `(a & b) >>> 0` is `UInt32.land`. -/
theorem uint32_land_inline (a b : UInt32) :
    ushr (band a.toNat b.toNat) 0 = ((a &&& b).toNat : Int) := by
  rw [ushr_zero, band, toI32_toInt, toI32_uint32, toI32_uint32]; rfl

/-- `(a | b) >>> 0` is `UInt32.lor`. -/
theorem uint32_lor_inline (a b : UInt32) :
    ushr (bor a.toNat b.toNat) 0 = ((a ||| b).toNat : Int) := by
  rw [ushr_zero, bor, toI32_toInt, toI32_uint32, toI32_uint32]; rfl

/-- `(a ^ b) >>> 0` is `UInt32.xor`. -/
theorem uint32_xor_inline (a b : UInt32) :
    ushr (bxor a.toNat b.toNat) 0 = ((a ^^^ b).toNat : Int) := by
  rw [ushr_zero, bxor, toI32_toInt, toI32_uint32, toI32_uint32]; rfl

/-! ## `UInt8` -/

/-- `(a + b) & 255` is `UInt8.add`. -/
theorem uint8_add_inline (a b : UInt8) :
    band ((a.toNat : Int) + b.toNat) 255 = ((a + b).toNat : Int) := by
  rw [band255, UInt8.toNat_add]; simp only [Nat.reducePow] at *; omega

/-- `(a - b) & 255` is `UInt8.sub`. -/
theorem uint8_sub_inline (a b : UInt8) :
    band ((a.toNat : Int) - b.toNat) 255 = ((a - b).toNat : Int) := by
  rw [band255, UInt8.toNat_sub]
  have : a.toNat < 256 := a.toNat_lt
  have : b.toNat < 256 := b.toNat_lt
  simp only [Nat.reducePow] at *; omega

/-- `(a * b) & 255` is `UInt8.mul` (the product, below `2^16`, is exact). -/
theorem uint8_mul_inline (a b : UInt8) :
    band ((a.toNat : Int) * b.toNat) 255 = ((a * b).toNat : Int) := by
  rw [band255, UInt8.toNat_mul]; simp only [Nat.reducePow]
  rw [Int.natCast_emod, Int.natCast_mul]; rfl

/-- `-a & 255` is `UInt8.neg`. -/
theorem uint8_neg_inline (a : UInt8) : band (-(a.toNat : Int)) 255 = ((-a).toNat : Int) := by
  rw [band255, UInt8.toNat_neg]
  have : a.toNat < 256 := a.toNat_lt
  simp only [UInt8.size] at *; omega

/-- `~a & 255` is `UInt8.complement`. -/
theorem uint8_complement_inline (a : UInt8) :
    band (bnot a.toNat) 255 = ((~~~a).toNat : Int) := by
  have ha : a.toNat < 256 := a.toNat_lt
  have h1 : bnot a.toNat = -(a.toNat : Int) - 1 := bnot_small a.toNat (by omega)
  rw [band255, h1, UInt8.toNat_not]
  simp only [UInt8.size]; omega

/-- `a & b` is `UInt8.land` (the and of two values below `2^8` is below `2^8`). -/
theorem uint8_land_inline (a b : UInt8) : band a.toNat b.toNat = ((a &&& b).toNat : Int) := by
  have ha : a.toNat < 2 ^ 8 := a.toNat_lt
  have hb : b.toNat < 2 ^ 8 := b.toNat_lt
  rw [band, bitwise_small _ _ BitVec.toNat_and 8 (by decide) _ _ ha hb
    (Nat.and_lt_two_pow _ hb), UInt8.toNat_and]

/-- `a | b` is `UInt8.lor`. -/
theorem uint8_lor_inline (a b : UInt8) : bor a.toNat b.toNat = ((a ||| b).toNat : Int) := by
  have ha : a.toNat < 2 ^ 8 := a.toNat_lt
  have hb : b.toNat < 2 ^ 8 := b.toNat_lt
  rw [bor, bitwise_small _ _ BitVec.toNat_or 8 (by decide) _ _ ha hb
    (Nat.or_lt_two_pow ha hb), UInt8.toNat_or]

/-- `a ^ b` is `UInt8.xor`. -/
theorem uint8_xor_inline (a b : UInt8) : bxor a.toNat b.toNat = ((a ^^^ b).toNat : Int) := by
  have ha : a.toNat < 2 ^ 8 := a.toNat_lt
  have hb : b.toNat < 2 ^ 8 := b.toNat_lt
  rw [bxor, bitwise_small _ _ BitVec.toNat_xor 8 (by decide) _ _ ha hb
    (Nat.xor_lt_two_pow ha hb), UInt8.toNat_xor]

/-! ## `UInt16` -/

/-- `(a + b) & 65535` is `UInt16.add`. -/
theorem uint16_add_inline (a b : UInt16) :
    band ((a.toNat : Int) + b.toNat) 65535 = ((a + b).toNat : Int) := by
  rw [band65535, UInt16.toNat_add]; simp only [Nat.reducePow] at *; omega

/-- `(a - b) & 65535` is `UInt16.sub`. -/
theorem uint16_sub_inline (a b : UInt16) :
    band ((a.toNat : Int) - b.toNat) 65535 = ((a - b).toNat : Int) := by
  rw [band65535, UInt16.toNat_sub]
  have : a.toNat < 65536 := a.toNat_lt
  have : b.toNat < 65536 := b.toNat_lt
  simp only [Nat.reducePow] at *; omega

/-- `(a * b) & 65535` is `UInt16.mul` (the product, below `2^32`, is exact). -/
theorem uint16_mul_inline (a b : UInt16) :
    band ((a.toNat : Int) * b.toNat) 65535 = ((a * b).toNat : Int) := by
  rw [band65535, UInt16.toNat_mul]; simp only [Nat.reducePow]
  rw [Int.natCast_emod, Int.natCast_mul]; rfl

/-- `-a & 65535` is `UInt16.neg`. -/
theorem uint16_neg_inline (a : UInt16) :
    band (-(a.toNat : Int)) 65535 = ((-a).toNat : Int) := by
  rw [band65535, UInt16.toNat_neg]
  have : a.toNat < 65536 := a.toNat_lt
  simp only [UInt16.size] at *; omega

/-- `~a & 65535` is `UInt16.complement`. -/
theorem uint16_complement_inline (a : UInt16) :
    band (bnot a.toNat) 65535 = ((~~~a).toNat : Int) := by
  have ha : a.toNat < 65536 := a.toNat_lt
  have h1 : bnot a.toNat = -(a.toNat : Int) - 1 := bnot_small a.toNat (by omega)
  rw [band65535, h1, UInt16.toNat_not]
  simp only [UInt16.size]; omega

/-- `a & b` is `UInt16.land`. -/
theorem uint16_land_inline (a b : UInt16) : band a.toNat b.toNat = ((a &&& b).toNat : Int) := by
  have ha : a.toNat < 2 ^ 16 := a.toNat_lt
  have hb : b.toNat < 2 ^ 16 := b.toNat_lt
  rw [band, bitwise_small _ _ BitVec.toNat_and 16 (by decide) _ _ ha hb
    (Nat.and_lt_two_pow _ hb), UInt16.toNat_and]

/-- `a | b` is `UInt16.lor`. -/
theorem uint16_lor_inline (a b : UInt16) : bor a.toNat b.toNat = ((a ||| b).toNat : Int) := by
  have ha : a.toNat < 2 ^ 16 := a.toNat_lt
  have hb : b.toNat < 2 ^ 16 := b.toNat_lt
  rw [bor, bitwise_small _ _ BitVec.toNat_or 16 (by decide) _ _ ha hb
    (Nat.or_lt_two_pow ha hb), UInt16.toNat_or]

/-- `a ^ b` is `UInt16.xor`. -/
theorem uint16_xor_inline (a b : UInt16) : bxor a.toNat b.toNat = ((a ^^^ b).toNat : Int) := by
  have ha : a.toNat < 2 ^ 16 := a.toNat_lt
  have hb : b.toNat < 2 ^ 16 := b.toNat_lt
  rw [bxor, bitwise_small _ _ BitVec.toNat_xor 16 (by decide) _ _ ha hb
    (Nat.xor_lt_two_pow ha hb), UInt16.toNat_xor]

/-! ## `UInt64` at the `BigInt` representation -/

/-- `BigInt.asUintN(64, a + b)` is `UInt64.add`. -/
theorem uint64_add_inline (a b : UInt64) :
    asUintN 64 ((a.toNat : Int) + b.toNat) = ((a + b).toNat : Int) := by
  rw [asUintN, UInt64.toNat_add]; simp only [Nat.reducePow] at *; omega

/-- `BigInt.asUintN(64, a - b)` is `UInt64.sub`. -/
theorem uint64_sub_inline (a b : UInt64) :
    asUintN 64 ((a.toNat : Int) - b.toNat) = ((a - b).toNat : Int) := by
  rw [asUintN, UInt64.toNat_sub]
  have : a.toNat < 18446744073709551616 := a.toNat_lt
  have : b.toNat < 18446744073709551616 := b.toNat_lt
  simp only [Nat.reducePow] at *; omega

/-- `BigInt.asUintN(64, a * b)` is `UInt64.mul`. -/
theorem uint64_mul_inline (a b : UInt64) :
    asUintN 64 ((a.toNat : Int) * b.toNat) = ((a * b).toNat : Int) := by
  rw [asUintN, UInt64.toNat_mul, Int.natCast_emod, Int.natCast_mul]

/-- `BigInt.asUintN(64, -a)` is `UInt64.neg`. -/
theorem uint64_neg_inline (a : UInt64) :
    asUintN 64 (-(a.toNat : Int)) = ((-a).toNat : Int) := by
  rw [asUintN, UInt64.toNat_neg]
  have : a.toNat < 18446744073709551616 := a.toNat_lt
  simp only [UInt64.size, Nat.reducePow] at *; omega

/-- `BigInt.asUintN(64, ~a)` (`~a` is `-a - 1` on a `BigInt`) is `UInt64.complement`. -/
theorem uint64_complement_inline (a : UInt64) :
    asUintN 64 (-(a.toNat : Int) - 1) = ((~~~a).toNat : Int) := by
  rw [asUintN, UInt64.toNat_not]
  have : a.toNat < 18446744073709551616 := a.toNat_lt
  simp only [UInt64.size, Nat.reducePow] at *; omega

/-- `a & b` is `UInt64.land`. -/
theorem uint64_land_inline (a b : UInt64) : bigAnd a.toNat b.toNat = (a &&& b).toNat :=
  (UInt64.toNat_and a b).symm

/-- `a | b` is `UInt64.lor`. -/
theorem uint64_lor_inline (a b : UInt64) : bigOr a.toNat b.toNat = (a ||| b).toNat :=
  (UInt64.toNat_or a b).symm

/-- `a ^ b` is `UInt64.xor`. -/
theorem uint64_xor_inline (a b : UInt64) : bigXor a.toNat b.toNat = (a ^^^ b).toNat :=
  (UInt64.toNat_xor a b).symm

/-- The runtime's `BigInt.asUintN(64, a & b)` (and the same for `|`, `^`) is the inline `a & b`:
the bitwise operation of two values below `2^64` is below `2^64`. -/
theorem uint64_bitwise_mask (a b : UInt64) :
    asUintN 64 (bigAnd a.toNat b.toNat) = bigAnd a.toNat b.toNat ∧
    asUintN 64 (bigOr a.toNat b.toNat) = bigOr a.toNat b.toNat ∧
    asUintN 64 (bigXor a.toNat b.toNat) = bigXor a.toNat b.toNat := by
  have ha : a.toNat < 2 ^ 64 := a.toNat_lt
  have hb : b.toNat < 2 ^ 64 := b.toNat_lt
  have h1 := Nat.and_lt_two_pow a.toNat hb
  have h2 := Nat.or_lt_two_pow ha hb
  have h3 := Nat.xor_lt_two_pow ha hb
  simp only [asUintN, bigAnd, bigOr, bigXor, ← Int.natCast_emod]
  refine ⟨?_, ?_, ?_⟩ <;> congr 1 <;> exact Nat.mod_eq_of_lt (by assumption)

end RuntimeSpec
