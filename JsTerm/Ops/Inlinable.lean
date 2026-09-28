module

public import JsTerm.Ty.Basic
public import JsTerm.Ops.Basic
public import LeanScript.Term.Extern.NameElab

@[expose] public section

set_option autoImplicit false

/-!
# The operations of `JsTerm` written inline

**Generated** by `scripts/gen_js_ops.py`; do not edit.

`JsOpInlinable`: the operations written in place of their call as a JavaScript operator,
conversion or literal over their arguments (`JsOpInlinable.template`, a `JsInline`); they never
throw.  The families, their names and their effects are explained in `JsTerm.Ops.Basic`.
-/

namespace MoreJs

/-- The operations written inline, indexed by their effects, the types of their arguments
    and the type of their result. -/
inductive JsOpInlinable : Effectfulness → MayThrow → List JsTy → JsTy → Type where
  /-- `BigInt(a.length)` (Array.size) -/
  | bigint_nat__lean_array_get_size : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpInlinable .pure .doesntThrow [A] (.terminal .bigint_nat)
  /-- `a.length` (Array.size) -/
  | uint53__lean_array_get_size : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpInlinable .pure .doesntThrow [A] (.terminal .uint53)
  /-- `a` (Array.toList) -/
  | array__lean_array_to_list : (α : JsTy) → JsOpInlinable .pure .doesntThrow [(.array α)] (.list α)
  /-- `[]` (Array.emptyWithCapacity) -/
  | bigint_nat__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity : (α : JsTy) → JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat)] (.array α)
  /-- `new C(0)` (Array.emptyWithCapacity) -/
  | typedArray__bigint_nat__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity : (t : JsTypedElem) → JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat)] (.typedArray t)
  /-- `[]` (Array.emptyWithCapacity) -/
  | uint53__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity : (α : JsTy) → JsOpInlinable .pure .doesntThrow [(.terminal .uint53)] (.array α)
  /-- `new C(0)` (Array.emptyWithCapacity) -/
  | typedArray__uint53__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity : (t : JsTypedElem) → JsOpInlinable .pure .doesntThrow [(.terminal .uint53)] (.typedArray t)
  /-- `[]` (Array.mkEmpty) -/
  | bigint_nat__lean_mk_empty_array_with_capacity__Array_mkEmpty : (α : JsTy) → JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat)] (.array α)
  /-- `new C(0)` (Array.mkEmpty) -/
  | typedArray__bigint_nat__lean_mk_empty_array_with_capacity__Array_mkEmpty : (t : JsTypedElem) → JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat)] (.typedArray t)
  /-- `[]` (Array.mkEmpty) -/
  | uint53__lean_mk_empty_array_with_capacity__Array_mkEmpty : (α : JsTy) → JsOpInlinable .pure .doesntThrow [(.terminal .uint53)] (.array α)
  /-- `new C(0)` (Array.mkEmpty) -/
  | typedArray__uint53__lean_mk_empty_array_with_capacity__Array_mkEmpty : (t : JsTypedElem) → JsOpInlinable .pure .doesntThrow [(.terminal .uint53)] (.typedArray t)
  /-- `a` (Array.mk) -/
  | array__lean_array_mk : (α : JsTy) → JsOpInlinable .pure .doesntThrow [(.list α)] (.array α)
  /-- `C.from(a)` (Array.mk) -/
  | typedArray__lean_array_mk : (t : JsTypedElem) → JsOpInlinable .pure .doesntThrow [(.list (.terminal t.leaf))] (.typedArray t)
  /-- `a` (UInt32.ofBitVec) -/
  | bitvec32__lean_uint32_of_nat_mk : JsOpInlinable .pure .doesntThrow [(.terminal (.bitvec_small 32 (by decide) (by decide)))] (.terminal .uint32)
  /-- `a === b` (UInt32.decEq) -/
  | uint32__lean_uint32_dec_eq : JsOpInlinable .pure .doesntThrow [(.terminal .uint32), (.terminal .uint32)] (.terminal .bool)
  /-- `a < b` (UInt32.decLt) -/
  | uint32__lean_uint32_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .uint32), (.terminal .uint32)] (.terminal .bool)
  /-- `a` (UInt8.toBitVec) -/
  | uint8__lean_uint8_to_nat__UInt8_toBitVec : JsOpInlinable .pure .doesntThrow [(.terminal .uint8)] (.terminal (.bitvec_small 8 (by decide) (by decide)))
  /-- `a < b` (Nat.decLt) -/
  | bigint_nat__lean_nat_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bool)
  /-- `a < b` (Nat.decLt) -/
  | uint53__lean_nat_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .bool)
  /-- `a < b` (UInt8.decLt) -/
  | uint8__lean_uint8_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .uint8), (.terminal .uint8)] (.terminal .bool)
  /-- `a <= b` (UInt32.decLe) -/
  | uint32__lean_uint32_dec_le : JsOpInlinable .pure .doesntThrow [(.terminal .uint32), (.terminal .uint32)] (.terminal .bool)
  /-- `a === b` (Nat.decEq) -/
  | bigint_nat__lean_nat_dec_eq__Nat_decEq : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bool)
  /-- `a === b` (Nat.decEq) -/
  | uint53__lean_nat_dec_eq__Nat_decEq : JsOpInlinable .pure .doesntThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .bool)
  /-- `a === b` (Nat.beq) -/
  | bigint_nat__lean_nat_dec_eq__Nat_beq : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bool)
  /-- `a === b` (Nat.beq) -/
  | uint53__lean_nat_dec_eq__Nat_beq : JsOpInlinable .pure .doesntThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .bool)
  /-- `a <= b` (UInt8.decLe) -/
  | uint8__lean_uint8_dec_le : JsOpInlinable .pure .doesntThrow [(.terminal .uint8), (.terminal .uint8)] (.terminal .bool)
  /-- `a <= b` (Nat.ble) -/
  | bigint_nat__lean_nat_dec_le__Nat_ble : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bool)
  /-- `a <= b` (Nat.ble) -/
  | uint53__lean_nat_dec_le__Nat_ble : JsOpInlinable .pure .doesntThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .bool)
  /-- `a <= b` (Nat.decLe) -/
  | bigint_nat__lean_nat_dec_le__Nat_decLe : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bool)
  /-- `a <= b` (Nat.decLe) -/
  | uint53__lean_nat_dec_le__Nat_decLe : JsOpInlinable .pure .doesntThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .bool)
  /-- `a + b` (Nat.add) -/
  | bigint_nat__lean_nat_add : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- `a` (UInt16.toBitVec) -/
  | uint16__lean_uint16_to_nat__UInt16_toBitVec : JsOpInlinable .pure .doesntThrow [(.terminal .uint16)] (.terminal (.bitvec_small 16 (by decide) (by decide)))
  /-- `a` (UInt16.ofBitVec) -/
  | bitvec16__lean_uint16_of_nat_mk : JsOpInlinable .pure .doesntThrow [(.terminal (.bitvec_small 16 (by decide) (by decide)))] (.terminal .uint16)
  /-- `a === b` (UInt16.decEq) -/
  | uint16__lean_uint16_dec_eq : JsOpInlinable .pure .doesntThrow [(.terminal .uint16), (.terminal .uint16)] (.terminal .bool)
  /-- `a === b` (String.decEq) -/
  | string__lean_string_dec_eq : JsOpInlinable .pure .doesntThrow [(.terminal .string), (.terminal .string)] (.terminal .bool)
  /-- `a` (UInt64.toBitVec) -/
  | bigint_nat__bigint_bitvec64__lean_uint64_to_nat__UInt64_toBitVec : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat)] (.terminal (.bigint_bitvec_big 64 (by decide)))
  /-- `BigInt(a)` (UInt64.toBitVec) -/
  | uint53__bigint_bitvec64__lean_uint64_to_nat__UInt64_toBitVec : JsOpInlinable .pure .doesntThrow [(.terminal .uint53)] (.terminal (.bigint_bitvec_big 64 (by decide)))
  /-- `a` (UInt64.toBitVec) -/
  | uint53__int53_bitvec64__lean_uint64_to_nat__UInt64_toBitVec : JsOpInlinable .pure .doesntThrow [(.terminal .uint53)] (.terminal (.int53_bitvec_big 64 (by decide)))
  /-- `a` (UInt64.ofBitVec) -/
  | bigint_bitvec64__bigint_nat__lean_uint64_of_nat_mk : JsOpInlinable .pure .doesntThrow [(.terminal (.bigint_bitvec_big 64 (by decide)))] (.terminal .bigint_nat)
  /-- `BigInt(a)` (UInt64.ofBitVec) -/
  | int53_bitvec64__bigint_nat__lean_uint64_of_nat_mk : JsOpInlinable .pure .doesntThrow [(.terminal (.int53_bitvec_big 64 (by decide)))] (.terminal .bigint_nat)
  /-- `a` (UInt64.ofBitVec) -/
  | int53_bitvec64__uint53__lean_uint64_of_nat_mk : JsOpInlinable .pure .doesntThrow [(.terminal (.int53_bitvec_big 64 (by decide)))] (.terminal .uint53)
  /-- `BigInt(a)` (UInt32.toNat) -/
  | bigint_nat__lean_uint32_to_nat__UInt32_toNat : JsOpInlinable .pure .doesntThrow [(.terminal .uint32)] (.terminal .bigint_nat)
  /-- `a` (UInt32.toNat) -/
  | uint53__lean_uint32_to_nat__UInt32_toNat : JsOpInlinable .pure .doesntThrow [(.terminal .uint32)] (.terminal .uint53)
  /-- `a` (UInt32.toBitVec) -/
  | uint32__lean_uint32_to_nat__UInt32_toBitVec : JsOpInlinable .pure .doesntThrow [(.terminal .uint32)] (.terminal (.bitvec_small 32 (by decide) (by decide)))
  /-- `a === b` (UInt64.decEq) -/
  | bigint_nat__lean_uint64_dec_eq : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bool)
  /-- `a === b` (UInt64.decEq) -/
  | uint53__lean_uint64_dec_eq : JsOpInlinable .pure .doesntThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .bool)
  /-- `a` (UInt8.ofBitVec) -/
  | bitvec8__lean_uint8_of_nat_mk : JsOpInlinable .pure .doesntThrow [(.terminal (.bitvec_small 8 (by decide) (by decide)))] (.terminal .uint8)
  /-- `a === b` (UInt8.decEq) -/
  | uint8__lean_uint8_dec_eq : JsOpInlinable .pure .doesntThrow [(.terminal .uint8), (.terminal .uint8)] (.terminal .bool)
  /-- `a * b` (Nat.mul) -/
  | bigint_nat__lean_nat_mul : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- `a || b` (strictOr) -/
  | bool__lean_strict_or : JsOpInlinable .pure .doesntThrow [(.terminal .bool), (.terminal .bool)] (.terminal .bool)
  /-- `a && b` (strictAnd) -/
  | bool__lean_strict_and : JsOpInlinable .pure .doesntThrow [(.terminal .bool), (.terminal .bool)] (.terminal .bool)
  /-- `a` (Int.ofNat) -/
  | bigint_nat__bigint_int__lean_nat_to_int : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat)] (.terminal .bigint_int)
  /-- `BigInt(a)` (Int.ofNat) -/
  | uint53__bigint_int__lean_nat_to_int : JsOpInlinable .pure .doesntThrow [(.terminal .uint53)] (.terminal .bigint_int)
  /-- `a` (Int.ofNat) -/
  | uint53__int53__lean_nat_to_int : JsOpInlinable .pure .doesntThrow [(.terminal .uint53)] (.terminal .int53)
  /-- `a <= b` (Int.decLe) -/
  | bigint_int__lean_int_dec_le : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bool)
  /-- `a <= b` (Int.decLe) -/
  | int53__lean_int_dec_le : JsOpInlinable .pure .doesntThrow [(.terminal .int53), (.terminal .int53)] (.terminal .bool)
  /-- `a < b` (Int.decLt) -/
  | bigint_int__lean_int_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bool)
  /-- `a < b` (Int.decLt) -/
  | int53__lean_int_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .int53), (.terminal .int53)] (.terminal .bool)
  /-- `a === b` (Int.decEq) -/
  | bigint_int__lean_int_dec_eq : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bool)
  /-- `a === b` (Int.decEq) -/
  | int53__lean_int_dec_eq : JsOpInlinable .pure .doesntThrow [(.terminal .int53), (.terminal .int53)] (.terminal .bool)
  /-- `a * b` (Int.mul) -/
  | bigint_int__lean_int_mul : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- `a >= 0n` (Int.decNonneg) -/
  | bigint_int__lean_int_dec_nonneg : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_int)] (.terminal .bool)
  /-- `a >= 0` (Int.decNonneg) -/
  | int53__lean_int_dec_nonneg : JsOpInlinable .pure .doesntThrow [(.terminal .int53)] (.terminal .bool)
  /-- `a + b` (Int.add) -/
  | bigint_int__lean_int_add : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- `-a` (Int.neg) -/
  | bigint_int__lean_int_neg : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_int)] (.terminal .bigint_int)
  /-- `a - b` (Int.sub) -/
  | bigint_int__lean_int_sub : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- `a ^ b` (Nat.xor) -/
  | bigint_nat__lean_nat_lxor : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- `a << b` (Nat.shiftLeft) -/
  | bigint_nat__lean_nat_shiftl : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- `a >> b` (Nat.shiftRight) -/
  | bigint_nat__lean_nat_shiftr : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- `a & b` (Nat.land) -/
  | bigint_nat__lean_nat_land : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- `a | b` (Nat.lor) -/
  | bigint_nat__lean_nat_lor : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- `a` (UInt64.toNat) -/
  | bigint_nat__lean_uint64_to_nat__UInt64_toNat : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- `BigInt(a)` (UInt64.toNat) -/
  | uint53__bigint_nat__lean_uint64_to_nat__UInt64_toNat : JsOpInlinable .pure .doesntThrow [(.terminal .uint53)] (.terminal .bigint_nat)
  /-- `a` (UInt64.toNat) -/
  | uint53__lean_uint64_to_nat__UInt64_toNat : JsOpInlinable .pure .doesntThrow [(.terminal .uint53)] (.terminal .uint53)
  /-- `a` (UInt16.toUInt32) -/
  | uint16__lean_uint16_to_uint32 : JsOpInlinable .pure .doesntThrow [(.terminal .uint16)] (.terminal .uint32)
  /-- `BigInt(a)` (UInt32.toUInt64) -/
  | bigint_nat__lean_uint32_to_uint64 : JsOpInlinable .pure .doesntThrow [(.terminal .uint32)] (.terminal .bigint_nat)
  /-- `a` (UInt32.toUInt64) -/
  | uint53__lean_uint32_to_uint64 : JsOpInlinable .pure .doesntThrow [(.terminal .uint32)] (.terminal .uint53)
  /-- `BigInt(a)` (UInt16.toNat) -/
  | bigint_nat__lean_uint16_to_nat__UInt16_toNat : JsOpInlinable .pure .doesntThrow [(.terminal .uint16)] (.terminal .bigint_nat)
  /-- `a` (UInt16.toNat) -/
  | uint53__lean_uint16_to_nat__UInt16_toNat : JsOpInlinable .pure .doesntThrow [(.terminal .uint16)] (.terminal .uint53)
  /-- `BigInt(a)` (UInt8.toUInt64) -/
  | bigint_nat__lean_uint8_to_uint64 : JsOpInlinable .pure .doesntThrow [(.terminal .uint8)] (.terminal .bigint_nat)
  /-- `a` (UInt8.toUInt64) -/
  | uint53__lean_uint8_to_uint64 : JsOpInlinable .pure .doesntThrow [(.terminal .uint8)] (.terminal .uint53)
  /-- `BigInt(a)` (UInt8.toNat) -/
  | bigint_nat__lean_uint8_to_nat__UInt8_toNat : JsOpInlinable .pure .doesntThrow [(.terminal .uint8)] (.terminal .bigint_nat)
  /-- `a` (UInt8.toNat) -/
  | uint53__lean_uint8_to_nat__UInt8_toNat : JsOpInlinable .pure .doesntThrow [(.terminal .uint8)] (.terminal .uint53)
  /-- `a` (UInt8.toUInt32) -/
  | uint8__lean_uint8_to_uint32 : JsOpInlinable .pure .doesntThrow [(.terminal .uint8)] (.terminal .uint32)
  /-- `BigInt(a)` (UInt16.toUInt64) -/
  | bigint_nat__lean_uint16_to_uint64 : JsOpInlinable .pure .doesntThrow [(.terminal .uint16)] (.terminal .bigint_nat)
  /-- `a` (UInt16.toUInt64) -/
  | uint53__lean_uint16_to_uint64 : JsOpInlinable .pure .doesntThrow [(.terminal .uint16)] (.terminal .uint53)
  /-- `a` (UInt8.toUInt16) -/
  | uint8__lean_uint8_to_uint16 : JsOpInlinable .pure .doesntThrow [(.terminal .uint8)] (.terminal .uint16)
  /-- `a < b` (UInt16.decLt) -/
  | uint16__lean_uint16_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .uint16), (.terminal .uint16)] (.terminal .bool)
  /-- `a <= b` (UInt16.decLe) -/
  | uint16__lean_uint16_dec_le : JsOpInlinable .pure .doesntThrow [(.terminal .uint16), (.terminal .uint16)] (.terminal .bool)
  /-- `a <= b` (UInt64.decLe) -/
  | bigint_nat__lean_uint64_dec_le : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bool)
  /-- `a <= b` (UInt64.decLe) -/
  | uint53__lean_uint64_dec_le : JsOpInlinable .pure .doesntThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .bool)
  /-- `a < b` (UInt64.decLt) -/
  | bigint_nat__lean_uint64_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bool)
  /-- `a < b` (UInt64.decLt) -/
  | uint53__lean_uint64_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .bool)
  /-- `a` (Int8.toInt16) -/
  | int8__lean_int8_to_int16 : JsOpInlinable .pure .doesntThrow [(.terminal .int8)] (.terminal .int16)
  /-- `a === b` (Int8.decEq) -/
  | int8__lean_int8_dec_eq : JsOpInlinable .pure .doesntThrow [(.terminal .int8), (.terminal .int8)] (.terminal .bool)
  /-- `a < b` (Int8.decLt) -/
  | int8__lean_int8_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .int8), (.terminal .int8)] (.terminal .bool)
  /-- `a` (Int8.toInt32) -/
  | int8__lean_int8_to_int32 : JsOpInlinable .pure .doesntThrow [(.terminal .int8)] (.terminal .int32)
  /-- `BigInt(a)` (Int8.toInt64) -/
  | bigint_int__lean_int8_to_int64 : JsOpInlinable .pure .doesntThrow [(.terminal .int8)] (.terminal .bigint_int)
  /-- `a` (Int8.toInt64) -/
  | int53__lean_int8_to_int64 : JsOpInlinable .pure .doesntThrow [(.terminal .int8)] (.terminal .int53)
  /-- `a <= b` (Int8.decLe) -/
  | int8__lean_int8_dec_le : JsOpInlinable .pure .doesntThrow [(.terminal .int8), (.terminal .int8)] (.terminal .bool)
  /-- `BigInt(a)` (Int8.toInt) -/
  | bigint_int__lean_int8_to_int : JsOpInlinable .pure .doesntThrow [(.terminal .int8)] (.terminal .bigint_int)
  /-- `a` (Int8.toInt) -/
  | int53__lean_int8_to_int : JsOpInlinable .pure .doesntThrow [(.terminal .int8)] (.terminal .int53)
  /-- `a <= b` (Int16.decLe) -/
  | int16__lean_int16_dec_le : JsOpInlinable .pure .doesntThrow [(.terminal .int16), (.terminal .int16)] (.terminal .bool)
  /-- `a < b` (Int16.decLt) -/
  | int16__lean_int16_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .int16), (.terminal .int16)] (.terminal .bool)
  /-- `BigInt(a)` (Int16.toInt) -/
  | bigint_int__lean_int16_to_int : JsOpInlinable .pure .doesntThrow [(.terminal .int16)] (.terminal .bigint_int)
  /-- `a` (Int16.toInt) -/
  | int53__lean_int16_to_int : JsOpInlinable .pure .doesntThrow [(.terminal .int16)] (.terminal .int53)
  /-- `a === b` (Int16.decEq) -/
  | int16__lean_int16_dec_eq : JsOpInlinable .pure .doesntThrow [(.terminal .int16), (.terminal .int16)] (.terminal .bool)
  /-- `a` (Int16.toInt32) -/
  | int16__lean_int16_to_int32 : JsOpInlinable .pure .doesntThrow [(.terminal .int16)] (.terminal .int32)
  /-- `BigInt(a)` (Int16.toInt64) -/
  | bigint_int__lean_int16_to_int64 : JsOpInlinable .pure .doesntThrow [(.terminal .int16)] (.terminal .bigint_int)
  /-- `a` (Int16.toInt64) -/
  | int53__lean_int16_to_int64 : JsOpInlinable .pure .doesntThrow [(.terminal .int16)] (.terminal .int53)
  /-- `a <= b` (Int32.decLe) -/
  | int32__lean_int32_dec_le : JsOpInlinable .pure .doesntThrow [(.terminal .int32), (.terminal .int32)] (.terminal .bool)
  /-- `BigInt(a)` (Int32.toInt64) -/
  | bigint_int__lean_int32_to_int64 : JsOpInlinable .pure .doesntThrow [(.terminal .int32)] (.terminal .bigint_int)
  /-- `a` (Int32.toInt64) -/
  | int53__lean_int32_to_int64 : JsOpInlinable .pure .doesntThrow [(.terminal .int32)] (.terminal .int53)
  /-- `a === b` (Int32.decEq) -/
  | int32__lean_int32_dec_eq : JsOpInlinable .pure .doesntThrow [(.terminal .int32), (.terminal .int32)] (.terminal .bool)
  /-- `a < b` (Int32.decLt) -/
  | int32__lean_int32_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .int32), (.terminal .int32)] (.terminal .bool)
  /-- `BigInt(a)` (Int32.toInt) -/
  | bigint_int__lean_int32_to_int : JsOpInlinable .pure .doesntThrow [(.terminal .int32)] (.terminal .bigint_int)
  /-- `a` (Int32.toInt) -/
  | int53__lean_int32_to_int : JsOpInlinable .pure .doesntThrow [(.terminal .int32)] (.terminal .int53)
  /-- `a < b` (Int64.decLt) -/
  | bigint_int__lean_int64_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bool)
  /-- `a < b` (Int64.decLt) -/
  | int53__lean_int64_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .int53), (.terminal .int53)] (.terminal .bool)
  /-- `a === b` (Int64.decEq) -/
  | bigint_int__lean_int64_dec_eq : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bool)
  /-- `a === b` (Int64.decEq) -/
  | int53__lean_int64_dec_eq : JsOpInlinable .pure .doesntThrow [(.terminal .int53), (.terminal .int53)] (.terminal .bool)
  /-- `a <= b` (Int64.decLe) -/
  | bigint_int__lean_int64_dec_le : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bool)
  /-- `a <= b` (Int64.decLe) -/
  | int53__lean_int64_dec_le : JsOpInlinable .pure .doesntThrow [(.terminal .int53), (.terminal .int53)] (.terminal .bool)
  /-- `a` (Int64.toInt) -/
  | bigint_int__lean_int64_to_int_sint : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_int)] (.terminal .bigint_int)
  /-- `BigInt(a)` (Int64.toInt) -/
  | int53__bigint_int__lean_int64_to_int_sint : JsOpInlinable .pure .doesntThrow [(.terminal .int53)] (.terminal .bigint_int)
  /-- `a` (Int64.toInt) -/
  | int53__lean_int64_to_int_sint : JsOpInlinable .pure .doesntThrow [(.terminal .int53)] (.terminal .int53)
  /-- `a + b` (String.Internal.append) -/
  | string__lean_string_append__String_Internal_append : JsOpInlinable .pure .doesntThrow [(.terminal .string), (.terminal .string)] (.terminal .string)
  /-- `a + b` (String.push) -/
  | string__lean_string_push : JsOpInlinable .pure .doesntThrow [(.terminal .string), (.terminal .string)] (.terminal .string)
  /-- `a + b` (String.append) -/
  | string__lean_string_append__String_append : JsOpInlinable .pure .doesntThrow [(.terminal .string), (.terminal .string)] (.terminal .string)
  /-- `a < b` (String.decidableLT) -/
  | string__lean_string_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .string), (.terminal .string)] (.terminal .bool)
  /-- `a` (UInt8.toFloat) -/
  | uint8__lean_uint8_to_float : JsOpInlinable .pure .doesntThrow [(.terminal .uint8)] (.terminal .float)
  /-- `a` (Float.toModel) -/
  | float__lean_float_to_bits__Float_toModel : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `a` (Float.ofModel) -/
  | float__lean_float_of_bits__Float_ofModel : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.log10(a)` (Float.log10) -/
  | float__log10 : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.cbrt(a)` (Float.cbrt) -/
  | float__cbrt : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.log(a)` (Float.log) -/
  | float__log : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `a / b` (Float.div) -/
  | float__lean_float_div : JsOpInlinable .pure .doesntThrow [(.terminal .float), (.terminal .float)] (.terminal .float)
  /-- `a === b` (Float.beq) -/
  | float__lean_float_beq : JsOpInlinable .pure .doesntThrow [(.terminal .float), (.terminal .float)] (.terminal .bool)
  /-- `Math.tan(a)` (Float.tan) -/
  | float__tan : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.tanh(a)` (Float.tanh) -/
  | float__tanh : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.pow(2, a)` (Float.exp2) -/
  | float__exp2 : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `a` (UInt32.toFloat) -/
  | uint32__lean_uint32_to_float : JsOpInlinable .pure .doesntThrow [(.terminal .uint32)] (.terminal .float)
  /-- `a <= b` (Float.decLe) -/
  | float__lean_float_decLe__Float_decLe : JsOpInlinable .pure .doesntThrow [(.terminal .float), (.terminal .float)] (.terminal .bool)
  /-- `a <= b` (Float.le) -/
  | float__lean_float_decLe__Float_le : JsOpInlinable .pure .doesntThrow [(.terminal .float), (.terminal .float)] (.terminal .bool)
  /-- `Math.sqrt(a)` (Float.sqrt) -/
  | float__sqrt : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.acos(a)` (Float.acos) -/
  | float__acos : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.atan(a)` (Float.atan) -/
  | float__atan : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.acosh(a)` (Float.acosh) -/
  | float__acosh : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.floor(a)` (Float.floor) -/
  | float__floor : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.abs(a)` (Float.abs) -/
  | float__fabs : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Number(a)` (UInt64.toFloat) -/
  | bigint_nat__lean_uint64_to_float : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat)] (.terminal .float)
  /-- `a` (UInt64.toFloat) -/
  | uint53__lean_uint64_to_float : JsOpInlinable .pure .doesntThrow [(.terminal .uint53)] (.terminal .float)
  /-- `a < b` (Float.decLt) -/
  | float__lean_float_decLt__Float_decLt : JsOpInlinable .pure .doesntThrow [(.terminal .float), (.terminal .float)] (.terminal .bool)
  /-- `a < b` (Float.lt) -/
  | float__lean_float_decLt__Float_lt : JsOpInlinable .pure .doesntThrow [(.terminal .float), (.terminal .float)] (.terminal .bool)
  /-- `Math.sin(a)` (Float.sin) -/
  | float__sin : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.cosh(a)` (Float.cosh) -/
  | float__cosh : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.exp(a)` (Float.exp) -/
  | float__exp : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.ceil(a)` (Float.ceil) -/
  | float__ceil : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.cos(a)` (Float.cos) -/
  | float__cos : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.log2(a)` (Float.log2) -/
  | float__log2 : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.atanh(a)` (Float.atanh) -/
  | float__atanh : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.atan2(a, b)` (Float.atan2) -/
  | float__atan2 : JsOpInlinable .pure .doesntThrow [(.terminal .float), (.terminal .float)] (.terminal .float)
  /-- `Math.sinh(a)` (Float.sinh) -/
  | float__sinh : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.asinh(a)` (Float.asinh) -/
  | float__asinh : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `a * b` (Float.mul) -/
  | float__lean_float_mul : JsOpInlinable .pure .doesntThrow [(.terminal .float), (.terminal .float)] (.terminal .float)
  /-- `a` (UInt16.toFloat) -/
  | uint16__lean_uint16_to_float : JsOpInlinable .pure .doesntThrow [(.terminal .uint16)] (.terminal .float)
  /-- `Math.asin(a)` (Float.asin) -/
  | float__asin : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.pow(a, b)` (Float.pow) -/
  | float__pow : JsOpInlinable .pure .doesntThrow [(.terminal .float), (.terminal .float)] (.terminal .float)
  /-- `a + b` (Float.add) -/
  | float__lean_float_add : JsOpInlinable .pure .doesntThrow [(.terminal .float), (.terminal .float)] (.terminal .float)
  /-- `a - b` (Float.sub) -/
  | float__lean_float_sub : JsOpInlinable .pure .doesntThrow [(.terminal .float), (.terminal .float)] (.terminal .float)
  /-- `-a` (Float.neg) -/
  | float__lean_float_negate : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `a` (Int32.toFloat) -/
  | int32__lean_int32_to_float : JsOpInlinable .pure .doesntThrow [(.terminal .int32)] (.terminal .float)
  /-- `a` (Int16.toFloat) -/
  | int16__lean_int16_to_float : JsOpInlinable .pure .doesntThrow [(.terminal .int16)] (.terminal .float)
  /-- `a` (Int8.toFloat) -/
  | int8__lean_int8_to_float : JsOpInlinable .pure .doesntThrow [(.terminal .int8)] (.terminal .float)
  /-- `Number(a)` (Int64.toFloat) -/
  | bigint_int__lean_int64_to_float : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_int)] (.terminal .float)
  /-- `a` (Int64.toFloat) -/
  | int53__lean_int64_to_float : JsOpInlinable .pure .doesntThrow [(.terminal .int53)] (.terminal .float)
  /-- `Math.fround(Math.tanh(a))` (Float32.tanh) -/
  | float32__tanhf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.pow(2, a))` (Float32.exp2) -/
  | float32__exp2f : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.log(a))` (Float32.log) -/
  | float32__logf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `a <= b` (Float32.le) -/
  | float32__lean_float32_decLe__Float32_le : JsOpInlinable .pure .doesntThrow [(.terminal .float32), (.terminal .float32)] (.terminal .bool)
  /-- `a <= b` (Float32.decLe) -/
  | float32__lean_float32_decLe__Float32_decLe : JsOpInlinable .pure .doesntThrow [(.terminal .float32), (.terminal .float32)] (.terminal .bool)
  /-- `a` (Float32.toModel) -/
  | float32__lean_float32_to_bits__Float32_toModel : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `a` (Float32.ofModel) -/
  | float32__lean_float32_of_bits__Float32_ofModel : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.atan(a))` (Float32.atan) -/
  | float32__atanf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.acosh(a))` (Float32.acosh) -/
  | float32__acoshf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.asin(a))` (Float32.asin) -/
  | float32__asinf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.pow(a, b))` (Float32.pow) -/
  | float32__powf : JsOpInlinable .pure .doesntThrow [(.terminal .float32), (.terminal .float32)] (.terminal .float32)
  /-- `a === b` (Float32.beq) -/
  | float32__lean_float32_beq : JsOpInlinable .pure .doesntThrow [(.terminal .float32), (.terminal .float32)] (.terminal .bool)
  /-- `a` (UInt8.toFloat32) -/
  | uint8__lean_uint8_to_float32 : JsOpInlinable .pure .doesntThrow [(.terminal .uint8)] (.terminal .float32)
  /-- `Math.fround(Math.tan(a))` (Float32.tan) -/
  | float32__tanf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `a` (Float32.toFloat) -/
  | float32__lean_float32_to_float : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float)
  /-- `Math.fround(Math.log10(a))` (Float32.log10) -/
  | float32__log10f : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.cbrt(a))` (Float32.cbrt) -/
  | float32__cbrtf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.atan2(a, b))` (Float32.atan2) -/
  | float32__atan2f : JsOpInlinable .pure .doesntThrow [(.terminal .float32), (.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.sinh(a))` (Float32.sinh) -/
  | float32__sinhf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.cos(a))` (Float32.cos) -/
  | float32__cosf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `a` (UInt32.toFloat32) -/
  | uint32__lean_uint32_to_float32 : JsOpInlinable .pure .doesntThrow [(.terminal .uint32)] (.terminal .float32)
  /-- `-a` (Float32.neg) -/
  | float32__lean_float32_negate : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.ceil(a)` (Float32.ceil) -/
  | float32__ceilf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.sin(a))` (Float32.sin) -/
  | float32__sinf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.asinh(a))` (Float32.asinh) -/
  | float32__asinhf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.log2(a))` (Float32.log2) -/
  | float32__log2f : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Number(a)` (UInt64.toFloat32) -/
  | bigint_nat__lean_uint64_to_float32 : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat)] (.terminal .float32)
  /-- `Number(a)` (UInt64.toFloat32) -/
  | uint53__lean_uint64_to_float32 : JsOpInlinable .pure .doesntThrow [(.terminal .uint53)] (.terminal .float32)
  /-- `Math.fround(Math.atanh(a))` (Float32.atanh) -/
  | float32__atanhf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.floor(a)` (Float32.floor) -/
  | float32__floorf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.abs(a)` (Float32.abs) -/
  | float32__fabsf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `a < b` (Float32.lt) -/
  | float32__lean_float32_decLt__Float32_lt : JsOpInlinable .pure .doesntThrow [(.terminal .float32), (.terminal .float32)] (.terminal .bool)
  /-- `a < b` (Float32.decLt) -/
  | float32__lean_float32_decLt__Float32_decLt : JsOpInlinable .pure .doesntThrow [(.terminal .float32), (.terminal .float32)] (.terminal .bool)
  /-- `Math.fround(Math.acos(a))` (Float32.acos) -/
  | float32__acosf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.sqrt(a))` (Float32.sqrt) -/
  | float32__sqrtf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `a` (UInt16.toFloat32) -/
  | uint16__lean_uint16_to_float32 : JsOpInlinable .pure .doesntThrow [(.terminal .uint16)] (.terminal .float32)
  /-- `Math.fround(Math.cosh(a))` (Float32.cosh) -/
  | float32__coshf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.exp(a))` (Float32.exp) -/
  | float32__expf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `a` (Int32.toFloat32) -/
  | int32__lean_int32_to_float32 : JsOpInlinable .pure .doesntThrow [(.terminal .int32)] (.terminal .float32)
  /-- `a` (Int8.toFloat32) -/
  | int8__lean_int8_to_float32 : JsOpInlinable .pure .doesntThrow [(.terminal .int8)] (.terminal .float32)
  /-- `a` (Int16.toFloat32) -/
  | int16__lean_int16_to_float32 : JsOpInlinable .pure .doesntThrow [(.terminal .int16)] (.terminal .float32)
  /-- `Number(a)` (Int64.toFloat32) -/
  | bigint_int__lean_int64_to_float32 : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_int)] (.terminal .float32)
  /-- `Number(a)` (Int64.toFloat32) -/
  | int53__lean_int64_to_float32 : JsOpInlinable .pure .doesntThrow [(.terminal .int53)] (.terminal .float32)

namespace JsOpInlinable

/-- The names of the constructors of `JsOpInlinable`, in order. -/
def names : Array String := ctor_names% JsOpInlinable

/-- The name of the operation (the name of its constructor). -/
def name {e : Effectfulness} {t : MayThrow} {σs : List JsTy} {τ : JsTy}
    (op : JsOpInlinable e t σs τ) : String :=
  JsOpInlinable.names[op.ctorIdx]!

/-- The JavaScript of an inlined operation, over its arguments. -/
def template {e : Effectfulness} {t : MayThrow} {σs : List JsTy} {τ : JsTy} :
    JsOpInlinable e t σs τ → JsInline
  | .bigint_nat__lean_array_get_size _ => .call "BigInt" [.member (.arg 0) "length"]
  | .uint53__lean_array_get_size _ => .member (.arg 0) "length"
  | .array__lean_array_to_list _ => .arg 0
  | .bigint_nat__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity _ => .emptyArray
  | .typedArray__bigint_nat__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity t => .new t.kind.ctorName [.num 0]
  | .uint53__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity _ => .emptyArray
  | .typedArray__uint53__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity t => .new t.kind.ctorName [.num 0]
  | .bigint_nat__lean_mk_empty_array_with_capacity__Array_mkEmpty _ => .emptyArray
  | .typedArray__bigint_nat__lean_mk_empty_array_with_capacity__Array_mkEmpty t => .new t.kind.ctorName [.num 0]
  | .uint53__lean_mk_empty_array_with_capacity__Array_mkEmpty _ => .emptyArray
  | .typedArray__uint53__lean_mk_empty_array_with_capacity__Array_mkEmpty t => .new t.kind.ctorName [.num 0]
  | .array__lean_array_mk _ => .arg 0
  | .typedArray__lean_array_mk t => .call (t.kind.ctorName ++ ".from") [.arg 0]
  | .bitvec32__lean_uint32_of_nat_mk => .arg 0
  | .uint32__lean_uint32_dec_eq => .bin "===" (.arg 0) (.arg 1)
  | .uint32__lean_uint32_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .uint8__lean_uint8_to_nat__UInt8_toBitVec => .arg 0
  | .bigint_nat__lean_nat_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .uint53__lean_nat_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .uint8__lean_uint8_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .uint32__lean_uint32_dec_le => .bin "<=" (.arg 0) (.arg 1)
  | .bigint_nat__lean_nat_dec_eq__Nat_decEq => .bin "===" (.arg 0) (.arg 1)
  | .uint53__lean_nat_dec_eq__Nat_decEq => .bin "===" (.arg 0) (.arg 1)
  | .bigint_nat__lean_nat_dec_eq__Nat_beq => .bin "===" (.arg 0) (.arg 1)
  | .uint53__lean_nat_dec_eq__Nat_beq => .bin "===" (.arg 0) (.arg 1)
  | .uint8__lean_uint8_dec_le => .bin "<=" (.arg 0) (.arg 1)
  | .bigint_nat__lean_nat_dec_le__Nat_ble => .bin "<=" (.arg 0) (.arg 1)
  | .uint53__lean_nat_dec_le__Nat_ble => .bin "<=" (.arg 0) (.arg 1)
  | .bigint_nat__lean_nat_dec_le__Nat_decLe => .bin "<=" (.arg 0) (.arg 1)
  | .uint53__lean_nat_dec_le__Nat_decLe => .bin "<=" (.arg 0) (.arg 1)
  | .bigint_nat__lean_nat_add => .bin "+" (.arg 0) (.arg 1)
  | .uint16__lean_uint16_to_nat__UInt16_toBitVec => .arg 0
  | .bitvec16__lean_uint16_of_nat_mk => .arg 0
  | .uint16__lean_uint16_dec_eq => .bin "===" (.arg 0) (.arg 1)
  | .string__lean_string_dec_eq => .bin "===" (.arg 0) (.arg 1)
  | .bigint_nat__bigint_bitvec64__lean_uint64_to_nat__UInt64_toBitVec => .arg 0
  | .uint53__bigint_bitvec64__lean_uint64_to_nat__UInt64_toBitVec => .call "BigInt" [.arg 0]
  | .uint53__int53_bitvec64__lean_uint64_to_nat__UInt64_toBitVec => .arg 0
  | .bigint_bitvec64__bigint_nat__lean_uint64_of_nat_mk => .arg 0
  | .int53_bitvec64__bigint_nat__lean_uint64_of_nat_mk => .call "BigInt" [.arg 0]
  | .int53_bitvec64__uint53__lean_uint64_of_nat_mk => .arg 0
  | .bigint_nat__lean_uint32_to_nat__UInt32_toNat => .call "BigInt" [.arg 0]
  | .uint53__lean_uint32_to_nat__UInt32_toNat => .arg 0
  | .uint32__lean_uint32_to_nat__UInt32_toBitVec => .arg 0
  | .bigint_nat__lean_uint64_dec_eq => .bin "===" (.arg 0) (.arg 1)
  | .uint53__lean_uint64_dec_eq => .bin "===" (.arg 0) (.arg 1)
  | .bitvec8__lean_uint8_of_nat_mk => .arg 0
  | .uint8__lean_uint8_dec_eq => .bin "===" (.arg 0) (.arg 1)
  | .bigint_nat__lean_nat_mul => .bin "*" (.arg 0) (.arg 1)
  | .bool__lean_strict_or => .bin "||" (.arg 0) (.arg 1)
  | .bool__lean_strict_and => .bin "&&" (.arg 0) (.arg 1)
  | .bigint_nat__bigint_int__lean_nat_to_int => .arg 0
  | .uint53__bigint_int__lean_nat_to_int => .call "BigInt" [.arg 0]
  | .uint53__int53__lean_nat_to_int => .arg 0
  | .bigint_int__lean_int_dec_le => .bin "<=" (.arg 0) (.arg 1)
  | .int53__lean_int_dec_le => .bin "<=" (.arg 0) (.arg 1)
  | .bigint_int__lean_int_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .int53__lean_int_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .bigint_int__lean_int_dec_eq => .bin "===" (.arg 0) (.arg 1)
  | .int53__lean_int_dec_eq => .bin "===" (.arg 0) (.arg 1)
  | .bigint_int__lean_int_mul => .bin "*" (.arg 0) (.arg 1)
  | .bigint_int__lean_int_dec_nonneg => .bin ">=" (.arg 0) (.big 0)
  | .int53__lean_int_dec_nonneg => .bin ">=" (.arg 0) (.num 0)
  | .bigint_int__lean_int_add => .bin "+" (.arg 0) (.arg 1)
  | .bigint_int__lean_int_neg => .un "-" (.arg 0)
  | .bigint_int__lean_int_sub => .bin "-" (.arg 0) (.arg 1)
  | .bigint_nat__lean_nat_lxor => .bin "^" (.arg 0) (.arg 1)
  | .bigint_nat__lean_nat_shiftl => .bin "<<" (.arg 0) (.arg 1)
  | .bigint_nat__lean_nat_shiftr => .bin ">>" (.arg 0) (.arg 1)
  | .bigint_nat__lean_nat_land => .bin "&" (.arg 0) (.arg 1)
  | .bigint_nat__lean_nat_lor => .bin "|" (.arg 0) (.arg 1)
  | .bigint_nat__lean_uint64_to_nat__UInt64_toNat => .arg 0
  | .uint53__bigint_nat__lean_uint64_to_nat__UInt64_toNat => .call "BigInt" [.arg 0]
  | .uint53__lean_uint64_to_nat__UInt64_toNat => .arg 0
  | .uint16__lean_uint16_to_uint32 => .arg 0
  | .bigint_nat__lean_uint32_to_uint64 => .call "BigInt" [.arg 0]
  | .uint53__lean_uint32_to_uint64 => .arg 0
  | .bigint_nat__lean_uint16_to_nat__UInt16_toNat => .call "BigInt" [.arg 0]
  | .uint53__lean_uint16_to_nat__UInt16_toNat => .arg 0
  | .bigint_nat__lean_uint8_to_uint64 => .call "BigInt" [.arg 0]
  | .uint53__lean_uint8_to_uint64 => .arg 0
  | .bigint_nat__lean_uint8_to_nat__UInt8_toNat => .call "BigInt" [.arg 0]
  | .uint53__lean_uint8_to_nat__UInt8_toNat => .arg 0
  | .uint8__lean_uint8_to_uint32 => .arg 0
  | .bigint_nat__lean_uint16_to_uint64 => .call "BigInt" [.arg 0]
  | .uint53__lean_uint16_to_uint64 => .arg 0
  | .uint8__lean_uint8_to_uint16 => .arg 0
  | .uint16__lean_uint16_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .uint16__lean_uint16_dec_le => .bin "<=" (.arg 0) (.arg 1)
  | .bigint_nat__lean_uint64_dec_le => .bin "<=" (.arg 0) (.arg 1)
  | .uint53__lean_uint64_dec_le => .bin "<=" (.arg 0) (.arg 1)
  | .bigint_nat__lean_uint64_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .uint53__lean_uint64_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .int8__lean_int8_to_int16 => .arg 0
  | .int8__lean_int8_dec_eq => .bin "===" (.arg 0) (.arg 1)
  | .int8__lean_int8_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .int8__lean_int8_to_int32 => .arg 0
  | .bigint_int__lean_int8_to_int64 => .call "BigInt" [.arg 0]
  | .int53__lean_int8_to_int64 => .arg 0
  | .int8__lean_int8_dec_le => .bin "<=" (.arg 0) (.arg 1)
  | .bigint_int__lean_int8_to_int => .call "BigInt" [.arg 0]
  | .int53__lean_int8_to_int => .arg 0
  | .int16__lean_int16_dec_le => .bin "<=" (.arg 0) (.arg 1)
  | .int16__lean_int16_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .bigint_int__lean_int16_to_int => .call "BigInt" [.arg 0]
  | .int53__lean_int16_to_int => .arg 0
  | .int16__lean_int16_dec_eq => .bin "===" (.arg 0) (.arg 1)
  | .int16__lean_int16_to_int32 => .arg 0
  | .bigint_int__lean_int16_to_int64 => .call "BigInt" [.arg 0]
  | .int53__lean_int16_to_int64 => .arg 0
  | .int32__lean_int32_dec_le => .bin "<=" (.arg 0) (.arg 1)
  | .bigint_int__lean_int32_to_int64 => .call "BigInt" [.arg 0]
  | .int53__lean_int32_to_int64 => .arg 0
  | .int32__lean_int32_dec_eq => .bin "===" (.arg 0) (.arg 1)
  | .int32__lean_int32_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .bigint_int__lean_int32_to_int => .call "BigInt" [.arg 0]
  | .int53__lean_int32_to_int => .arg 0
  | .bigint_int__lean_int64_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .int53__lean_int64_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .bigint_int__lean_int64_dec_eq => .bin "===" (.arg 0) (.arg 1)
  | .int53__lean_int64_dec_eq => .bin "===" (.arg 0) (.arg 1)
  | .bigint_int__lean_int64_dec_le => .bin "<=" (.arg 0) (.arg 1)
  | .int53__lean_int64_dec_le => .bin "<=" (.arg 0) (.arg 1)
  | .bigint_int__lean_int64_to_int_sint => .arg 0
  | .int53__bigint_int__lean_int64_to_int_sint => .call "BigInt" [.arg 0]
  | .int53__lean_int64_to_int_sint => .arg 0
  | .string__lean_string_append__String_Internal_append => .bin "+" (.arg 0) (.arg 1)
  | .string__lean_string_push => .bin "+" (.arg 0) (.arg 1)
  | .string__lean_string_append__String_append => .bin "+" (.arg 0) (.arg 1)
  | .string__lean_string_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .uint8__lean_uint8_to_float => .arg 0
  | .float__lean_float_to_bits__Float_toModel => .arg 0
  | .float__lean_float_of_bits__Float_ofModel => .arg 0
  | .float__log10 => .call "Math.log10" [.arg 0]
  | .float__cbrt => .call "Math.cbrt" [.arg 0]
  | .float__log => .call "Math.log" [.arg 0]
  | .float__lean_float_div => .bin "/" (.arg 0) (.arg 1)
  | .float__lean_float_beq => .bin "===" (.arg 0) (.arg 1)
  | .float__tan => .call "Math.tan" [.arg 0]
  | .float__tanh => .call "Math.tanh" [.arg 0]
  | .float__exp2 => .call "Math.pow" [.num 2, .arg 0]
  | .uint32__lean_uint32_to_float => .arg 0
  | .float__lean_float_decLe__Float_decLe => .bin "<=" (.arg 0) (.arg 1)
  | .float__lean_float_decLe__Float_le => .bin "<=" (.arg 0) (.arg 1)
  | .float__sqrt => .call "Math.sqrt" [.arg 0]
  | .float__acos => .call "Math.acos" [.arg 0]
  | .float__atan => .call "Math.atan" [.arg 0]
  | .float__acosh => .call "Math.acosh" [.arg 0]
  | .float__floor => .call "Math.floor" [.arg 0]
  | .float__fabs => .call "Math.abs" [.arg 0]
  | .bigint_nat__lean_uint64_to_float => .call "Number" [.arg 0]
  | .uint53__lean_uint64_to_float => .arg 0
  | .float__lean_float_decLt__Float_decLt => .bin "<" (.arg 0) (.arg 1)
  | .float__lean_float_decLt__Float_lt => .bin "<" (.arg 0) (.arg 1)
  | .float__sin => .call "Math.sin" [.arg 0]
  | .float__cosh => .call "Math.cosh" [.arg 0]
  | .float__exp => .call "Math.exp" [.arg 0]
  | .float__ceil => .call "Math.ceil" [.arg 0]
  | .float__cos => .call "Math.cos" [.arg 0]
  | .float__log2 => .call "Math.log2" [.arg 0]
  | .float__atanh => .call "Math.atanh" [.arg 0]
  | .float__atan2 => .call "Math.atan2" [.arg 0, .arg 1]
  | .float__sinh => .call "Math.sinh" [.arg 0]
  | .float__asinh => .call "Math.asinh" [.arg 0]
  | .float__lean_float_mul => .bin "*" (.arg 0) (.arg 1)
  | .uint16__lean_uint16_to_float => .arg 0
  | .float__asin => .call "Math.asin" [.arg 0]
  | .float__pow => .call "Math.pow" [.arg 0, .arg 1]
  | .float__lean_float_add => .bin "+" (.arg 0) (.arg 1)
  | .float__lean_float_sub => .bin "-" (.arg 0) (.arg 1)
  | .float__lean_float_negate => .un "-" (.arg 0)
  | .int32__lean_int32_to_float => .arg 0
  | .int16__lean_int16_to_float => .arg 0
  | .int8__lean_int8_to_float => .arg 0
  | .bigint_int__lean_int64_to_float => .call "Number" [.arg 0]
  | .int53__lean_int64_to_float => .arg 0
  | .float32__tanhf => .call "Math.fround" [.call "Math.tanh" [.arg 0]]
  | .float32__exp2f => .call "Math.fround" [.call "Math.pow" [.num 2, .arg 0]]
  | .float32__logf => .call "Math.fround" [.call "Math.log" [.arg 0]]
  | .float32__lean_float32_decLe__Float32_le => .bin "<=" (.arg 0) (.arg 1)
  | .float32__lean_float32_decLe__Float32_decLe => .bin "<=" (.arg 0) (.arg 1)
  | .float32__lean_float32_to_bits__Float32_toModel => .arg 0
  | .float32__lean_float32_of_bits__Float32_ofModel => .arg 0
  | .float32__atanf => .call "Math.fround" [.call "Math.atan" [.arg 0]]
  | .float32__acoshf => .call "Math.fround" [.call "Math.acosh" [.arg 0]]
  | .float32__asinf => .call "Math.fround" [.call "Math.asin" [.arg 0]]
  | .float32__powf => .call "Math.fround" [.call "Math.pow" [.arg 0, .arg 1]]
  | .float32__lean_float32_beq => .bin "===" (.arg 0) (.arg 1)
  | .uint8__lean_uint8_to_float32 => .arg 0
  | .float32__tanf => .call "Math.fround" [.call "Math.tan" [.arg 0]]
  | .float32__lean_float32_to_float => .arg 0
  | .float32__log10f => .call "Math.fround" [.call "Math.log10" [.arg 0]]
  | .float32__cbrtf => .call "Math.fround" [.call "Math.cbrt" [.arg 0]]
  | .float32__atan2f => .call "Math.fround" [.call "Math.atan2" [.arg 0, .arg 1]]
  | .float32__sinhf => .call "Math.fround" [.call "Math.sinh" [.arg 0]]
  | .float32__cosf => .call "Math.fround" [.call "Math.cos" [.arg 0]]
  | .uint32__lean_uint32_to_float32 => .arg 0
  | .float32__lean_float32_negate => .un "-" (.arg 0)
  | .float32__ceilf => .call "Math.ceil" [.arg 0]
  | .float32__sinf => .call "Math.fround" [.call "Math.sin" [.arg 0]]
  | .float32__asinhf => .call "Math.fround" [.call "Math.asinh" [.arg 0]]
  | .float32__log2f => .call "Math.fround" [.call "Math.log2" [.arg 0]]
  | .bigint_nat__lean_uint64_to_float32 => .call "Number" [.arg 0]
  | .uint53__lean_uint64_to_float32 => .call "Number" [.arg 0]
  | .float32__atanhf => .call "Math.fround" [.call "Math.atanh" [.arg 0]]
  | .float32__floorf => .call "Math.floor" [.arg 0]
  | .float32__fabsf => .call "Math.abs" [.arg 0]
  | .float32__lean_float32_decLt__Float32_lt => .bin "<" (.arg 0) (.arg 1)
  | .float32__lean_float32_decLt__Float32_decLt => .bin "<" (.arg 0) (.arg 1)
  | .float32__acosf => .call "Math.fround" [.call "Math.acos" [.arg 0]]
  | .float32__sqrtf => .call "Math.fround" [.call "Math.sqrt" [.arg 0]]
  | .uint16__lean_uint16_to_float32 => .arg 0
  | .float32__coshf => .call "Math.fround" [.call "Math.cosh" [.arg 0]]
  | .float32__expf => .call "Math.fround" [.call "Math.exp" [.arg 0]]
  | .int32__lean_int32_to_float32 => .arg 0
  | .int8__lean_int8_to_float32 => .arg 0
  | .int16__lean_int16_to_float32 => .arg 0
  | .bigint_int__lean_int64_to_float32 => .call "Number" [.arg 0]
  | .int53__lean_int64_to_float32 => .call "Number" [.arg 0]

end JsOpInlinable

end MoreJs

end
