module

public import RuntimeSpec.Correct
public import RuntimeSpec.InlineUInt

@[expose] public section

set_option autoImplicit false

/-!
# The arithmetic of the signed small integers, and the divisions, written inline

The backend writes the arithmetic and bitwise operations of `Int8`, `Int16` and `Int32`, and
the division of all six 8/16/32-bit types, inline (`scripts/js_ops_inline.json`) instead of
calling their functions in `runtime.js`.  Each operand is read once, from left to right, so an
inline form computes its arguments exactly as a call does:

| operation | `Int8` (`Int16`: `16`) | `Int32` |
|---|---|---|
| `add` | `((a + b) << 24) >> 24` | `(a + b) \| 0` |
| `sub` | `((a - b) << 24) >> 24` | `(a - b) \| 0` |
| `mul` | `((a * b) << 24) >> 24` | `Math.imul(a, b)` |
| `neg` | `(-a << 24) >> 24` | `-a \| 0` |
| `div` | `((a / b) << 24) >> 24` | `(a / b) \| 0` |
| `complement` | `~a` | `~a` |
| `land`, `lor`, `xor` | `a & b`, `a \| b`, `a ^ b` | `a & b`, `a \| b`, `a ^ b` |

and the division of `UInt8`/`UInt16` as `(a / b) | 0`, of `UInt32` as `(a / b) >>> 0`.

The arithmetic forms are the bodies of the runtime's functions (`Math.imul(a, b) | 0` and
`(a & b) | 0` lose their `| 0`, which is the identity on a signed 32-bit result).  The bitwise
forms drop the runtime's final `<< 24 >> 24`: the bitwise operation of two sign-extended 8-bit
values is sign-extended already.  The division forms drop the runtime's test `b === 0 ? 0 : …`
(which reads `b` twice) and its `Math.trunc` / `Math.floor`.

## The division in the model

`a / b` is a non-integral `number`; only `ToInt32(a / b)` matters to `| 0`, `<<` and `>>>`.  For
two safe integers `a`, `b`, `ToInt32(a / b)` is `ToInt32(a.tdiv b)` (`Int.tdiv`, the quotient
truncated toward zero):

* if `b ≠ 0` and the quotient `q = a / b` is not an integer, it is at least `1/|b|` away from
  every integer, while the rounding error of the division is at most `|q| · 2^-53 < 1/|b|`
  (as `|a| < 2^53`), so the rounded quotient truncates to `a.tdiv b`; an integral quotient is
  safe, hence exact;
* if `b = 0`, `a / b` is `Infinity`, `-Infinity` or `NaN`, and `ToInt32` of each is `0`, which
  is `a.tdiv 0`.

So `(a / b) | 0` is modelled by `bor (a.tdiv b) 0`, `(a / b) >>> 0` by `ushr (a.tdiv b) 0` and
`(a / b) << 24` by `shl (a.tdiv b) 24` (the same assumption as the model's module doc, extended to
`b = 0`).

These theorems prove each form equal to the Lean operation in the model of `RuntimeSpec.Model`
(an `Int8`/`Int16`/`Int32` is its `toInt`, a `UInt8`/`UInt16`/`UInt32` its `toNat`).
-/

namespace RuntimeSpec

/-! ## Helpers -/

private theorem int8_wrap (x : Int) : sar (shl x 24) 24 = x.bmod (2 ^ 8) := by
  rw [← New.int53__lean_int8_of_int, int53__lean_int8_of_int_correct, Int8.toInt_ofInt]

private theorem int16_wrap (x : Int) : sar (shl x 16) 16 = x.bmod (2 ^ 16) := by
  rw [← New.int53__lean_int16_of_int, int53__lean_int16_of_int_correct, Int16.toInt_ofInt]

private theorem int32_wrap (x : Int) : bor x 0 = x.bmod (2 ^ 32) := by
  rw [← New.int53__lean_int32_of_int, int53__lean_int32_of_int_correct, Int32.toInt_ofInt]

private theorem toI32_sext {w : Nat} (x : BitVec w) : toI32 x.toInt = x.signExtend 32 := rfl

/-- A bitwise operation of two sign-extended values is the sign extension of the operation. -/
private theorem bitwise_sext {w : Nat} (hw : w ≤ 32)
    (op : {n : Nat} → BitVec n → BitVec n → BitVec n)
    (hop : ∀ (x y : BitVec w), (op x y).signExtend 32 = op (x.signExtend 32) (y.signExtend 32))
    (x y : BitVec w) : (op (toI32 x.toInt) (toI32 y.toInt)).toInt = (op x y).toInt := by
  rw [toI32_sext, toI32_sext, ← hop, BitVec.toInt_signExtend_of_le hw]

private theorem bnot32 (y : BitVec 32) : (~~~y).toInt = -y.toInt - 1 := by
  rw [BitVec.toInt_not, BitVec.toInt_eq_toNat_cond]
  have := y.isLt
  simp only [Int.bmod_def]
  split <;> split <;> omega

private theorem bnot_sext {w : Nat} (hw' : w ≤ 32) (x : BitVec w) :
    (~~~toI32 x.toInt).toInt = -x.toInt - 1 := by
  rw [bnot32, toI32_sext, BitVec.toInt_signExtend_of_le hw']

/-! ## `Int8` -/

/-- `((a + b) << 24) >> 24` is `Int8.add`. -/
theorem int8_add_inline (a b : Int8) : sar (shl (a.toInt + b.toInt) 24) 24 = (a + b).toInt := by
  rw [int8_wrap, Int8.toInt_add]

/-- `((a - b) << 24) >> 24` is `Int8.sub`. -/
theorem int8_sub_inline (a b : Int8) : sar (shl (a.toInt - b.toInt) 24) 24 = (a - b).toInt := by
  rw [int8_wrap, Int8.toInt_sub]

/-- `((a * b) << 24) >> 24` is `Int8.mul` (the product of two 8-bit values is exact). -/
theorem int8_mul_inline (a b : Int8) : sar (shl (a.toInt * b.toInt) 24) 24 = (a * b).toInt := by
  rw [int8_wrap, Int8.toInt_mul]

/-- `(-a << 24) >> 24` is `Int8.neg`. -/
theorem int8_neg_inline (a : Int8) : sar (shl (-a.toInt) 24) 24 = (-a).toInt := by
  rw [int8_wrap, Int8.toInt_neg]

/-- `((a / b) << 24) >> 24` is `Int8.div` (including `b = 0` and `-128 / -1`). -/
theorem int8_div_inline (a b : Int8) :
    sar (shl (a.toInt.tdiv b.toInt) 24) 24 = (a / b).toInt := by
  rw [int8_wrap, Int8.toInt_div]

/-- `~a` is `Int8.complement`. -/
theorem int8_complement_inline (a : Int8) : bnot a.toInt = (~~~a).toInt := by
  rw [bnot, ← Int8.toInt_toBitVec, bnot_sext (by decide), Int8.toInt_toBitVec,
    Int8.toInt_not, Int.bmod_eq_of_le_mul_two] <;>
  · have := a.le_toInt; have := a.toInt_lt; omega

/-- `a & b` is `Int8.land`. -/
theorem int8_land_inline (a b : Int8) : band a.toInt b.toInt = (a &&& b).toInt := by
  rw [band, ← Int8.toInt_toBitVec, ← Int8.toInt_toBitVec b,
    bitwise_sext (by decide) (· &&& ·) (fun _ _ => BitVec.signExtend_and), ← Int8.toBitVec_and,
    Int8.toInt_toBitVec]

/-- `a | b` is `Int8.lor`. -/
theorem int8_lor_inline (a b : Int8) : bor a.toInt b.toInt = (a ||| b).toInt := by
  rw [bor, ← Int8.toInt_toBitVec, ← Int8.toInt_toBitVec b,
    bitwise_sext (by decide) (· ||| ·) (fun _ _ => BitVec.signExtend_or), ← Int8.toBitVec_or,
    Int8.toInt_toBitVec]

/-- `a ^ b` is `Int8.xor`. -/
theorem int8_xor_inline (a b : Int8) : bxor a.toInt b.toInt = (a ^^^ b).toInt := by
  rw [bxor, ← Int8.toInt_toBitVec, ← Int8.toInt_toBitVec b,
    bitwise_sext (by decide) (· ^^^ ·) (fun _ _ => BitVec.signExtend_xor), ← Int8.toBitVec_xor,
    Int8.toInt_toBitVec]

/-! ## `Int16` -/

/-- `((a + b) << 16) >> 16` is `Int16.add`. -/
theorem int16_add_inline (a b : Int16) : sar (shl (a.toInt + b.toInt) 16) 16 = (a + b).toInt := by
  rw [int16_wrap, Int16.toInt_add]

/-- `((a - b) << 16) >> 16` is `Int16.sub`. -/
theorem int16_sub_inline (a b : Int16) : sar (shl (a.toInt - b.toInt) 16) 16 = (a - b).toInt := by
  rw [int16_wrap, Int16.toInt_sub]

/-- `((a * b) << 16) >> 16` is `Int16.mul` (the product of two 16-bit values is exact). -/
theorem int16_mul_inline (a b : Int16) : sar (shl (a.toInt * b.toInt) 16) 16 = (a * b).toInt := by
  rw [int16_wrap, Int16.toInt_mul]

/-- `(-a << 16) >> 16` is `Int16.neg`. -/
theorem int16_neg_inline (a : Int16) : sar (shl (-a.toInt) 16) 16 = (-a).toInt := by
  rw [int16_wrap, Int16.toInt_neg]

/-- `((a / b) << 16) >> 16` is `Int16.div` (including `b = 0` and `-32768 / -1`). -/
theorem int16_div_inline (a b : Int16) :
    sar (shl (a.toInt.tdiv b.toInt) 16) 16 = (a / b).toInt := by
  rw [int16_wrap, Int16.toInt_div]

/-- `~a` is `Int16.complement`. -/
theorem int16_complement_inline (a : Int16) : bnot a.toInt = (~~~a).toInt := by
  rw [bnot, ← Int16.toInt_toBitVec, bnot_sext (by decide), Int16.toInt_toBitVec,
    Int16.toInt_not, Int.bmod_eq_of_le_mul_two] <;>
  · have := a.le_toInt; have := a.toInt_lt; omega

/-- `a & b` is `Int16.land`. -/
theorem int16_land_inline (a b : Int16) : band a.toInt b.toInt = (a &&& b).toInt := by
  rw [band, ← Int16.toInt_toBitVec, ← Int16.toInt_toBitVec b,
    bitwise_sext (by decide) (· &&& ·) (fun _ _ => BitVec.signExtend_and), ← Int16.toBitVec_and,
    Int16.toInt_toBitVec]

/-- `a | b` is `Int16.lor`. -/
theorem int16_lor_inline (a b : Int16) : bor a.toInt b.toInt = (a ||| b).toInt := by
  rw [bor, ← Int16.toInt_toBitVec, ← Int16.toInt_toBitVec b,
    bitwise_sext (by decide) (· ||| ·) (fun _ _ => BitVec.signExtend_or), ← Int16.toBitVec_or,
    Int16.toInt_toBitVec]

/-- `a ^ b` is `Int16.xor`. -/
theorem int16_xor_inline (a b : Int16) : bxor a.toInt b.toInt = (a ^^^ b).toInt := by
  rw [bxor, ← Int16.toInt_toBitVec, ← Int16.toInt_toBitVec b,
    bitwise_sext (by decide) (· ^^^ ·) (fun _ _ => BitVec.signExtend_xor), ← Int16.toBitVec_xor,
    Int16.toInt_toBitVec]

/-! ## `Int32` -/

private theorem toI32_int32 (a : Int32) : toI32 a.toInt = a.toBitVec := by
  rw [← Int32.toInt_toBitVec]; exact BitVec.ofInt_toInt

/-- `(a + b) | 0` is `Int32.add`. -/
theorem int32_add_inline (a b : Int32) : bor (a.toInt + b.toInt) 0 = (a + b).toInt := by
  rw [int32_wrap, Int32.toInt_add]

/-- `(a - b) | 0` is `Int32.sub`. -/
theorem int32_sub_inline (a b : Int32) : bor (a.toInt - b.toInt) 0 = (a - b).toInt := by
  rw [int32_wrap, Int32.toInt_sub]

/-- `Math.imul(a, b)` is `Int32.mul`. -/
theorem int32_mul_inline (a b : Int32) : imul a.toInt b.toInt = (a * b).toInt := by
  rw [imul, toI32_int32, toI32_int32, ← Int32.toBitVec_mul, Int32.toInt_toBitVec]

/-- `-a | 0` is `Int32.neg`. -/
theorem int32_neg_inline (a : Int32) : bor (-a.toInt) 0 = (-a).toInt := by
  rw [int32_wrap, Int32.toInt_neg]

/-- `(a / b) | 0` is `Int32.div` (including `b = 0` and `-2^31 / -1`). -/
theorem int32_div_inline (a b : Int32) : bor (a.toInt.tdiv b.toInt) 0 = (a / b).toInt := by
  rw [int32_wrap, Int32.toInt_div]

/-- `~a` is `Int32.complement`. -/
theorem int32_complement_inline (a : Int32) : bnot a.toInt = (~~~a).toInt := by
  rw [bnot, toI32_int32, ← Int32.toBitVec_not, Int32.toInt_toBitVec]

/-- `a & b` is `Int32.land`. -/
theorem int32_land_inline (a b : Int32) : band a.toInt b.toInt = (a &&& b).toInt := by
  rw [band, toI32_int32, toI32_int32, ← Int32.toBitVec_and, Int32.toInt_toBitVec]

/-- `a | b` is `Int32.lor`. -/
theorem int32_lor_inline (a b : Int32) : bor a.toInt b.toInt = (a ||| b).toInt := by
  rw [bor, toI32_int32, toI32_int32, ← Int32.toBitVec_or, Int32.toInt_toBitVec]

/-- `a ^ b` is `Int32.xor`. -/
theorem int32_xor_inline (a b : Int32) : bxor a.toInt b.toInt = (a ^^^ b).toInt := by
  rw [bxor, toI32_int32, toI32_int32, ← Int32.toBitVec_xor, Int32.toInt_toBitVec]

/-! ## The unsigned divisions -/

private theorem tdiv_nat (a b : Nat) : (a : Int).tdiv b = ((a / b : Nat) : Int) := rfl

/-- `(a / b) | 0` is `UInt8.div` (including `b = 0`). -/
theorem uint8_div_inline (a b : UInt8) :
    bor ((a.toNat : Int).tdiv b.toNat) 0 = ((a / b).toNat : Int) := by
  rw [int32_wrap, UInt8.toNat_div, tdiv_nat, Int.bmod_eq_of_le_mul_two] <;>
  · have := a.toNat_lt; have := Nat.div_le_self a.toNat b.toNat
    generalize a.toNat / b.toNat = q at *; omega

/-- `(a / b) | 0` is `UInt16.div` (including `b = 0`). -/
theorem uint16_div_inline (a b : UInt16) :
    bor ((a.toNat : Int).tdiv b.toNat) 0 = ((a / b).toNat : Int) := by
  rw [int32_wrap, UInt16.toNat_div, tdiv_nat, Int.bmod_eq_of_le_mul_two] <;>
  · have := a.toNat_lt; have := Nat.div_le_self a.toNat b.toNat
    generalize a.toNat / b.toNat = q at *; omega

/-- `(a / b) >>> 0` is `UInt32.div` (including `b = 0`). -/
theorem uint32_div_inline (a b : UInt32) :
    ushr ((a.toNat : Int).tdiv b.toNat) 0 = ((a / b).toNat : Int) := by
  rw [UInt32.toNat_div, tdiv_nat]
  have := a.toNat_lt; have := Nat.div_le_self a.toNat b.toNat
  generalize a.toNat / b.toNat = q at *
  simp [ushr, shiftCount, toI32]
  omega

end RuntimeSpec
