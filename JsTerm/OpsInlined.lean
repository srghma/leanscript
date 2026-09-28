module

public import JsTerm.Ty

@[expose] public section

set_option autoImplicit false

/-!
# The operations of `JsTerm` written inline

**Generated** by `scripts/gen_js_ops.py` from the catalogue of externs
(`LeanScript/LeanInitPureExterns/*.lean`); do not edit.

The operations whose JavaScript is one operator, conversion or literal over their arguments
(`bigint_nat__lean_nat_land` is `a & b`, `uint8__lean_uint8_to_nat__UInt8_toNat` at
`bigint_nat` is `BigInt(a)`): each is printed in place of its call, as its template
(`JsOpInlined.template`, a `JsInline` over the arguments).  The naming is the one of
`JsTerm.OpsImported`.
-/

namespace MoreJs

/-- How an inlined operation is written in JavaScript, over its arguments. -/
inductive JsInline where
  /-- The argument of position `i` (from `0`). -/
  | arg (i : Nat)
  /-- `a op b`, for the JavaScript binary operator `op` (`+`, `&`, `===`, …). -/
  | bin (op : String) (a b : JsInline)
  /-- `op a`, for the JavaScript prefix operator `op` (`-`, `~`, `!`). -/
  | un (op : String) (a : JsInline)
  /-- `f(args)`, `f` a global function (`BigInt`, `Number`, `Uint8Array.from`). -/
  | call (f : String) (args : List JsInline)
  /-- `new C(args)`. -/
  | new (ctor : String) (args : List JsInline)
  /-- An integer `number` literal. -/
  | num (n : Int)
  /-- A `BigInt` literal. -/
  | big (n : Int)
  /-- `[]`. -/
  | emptyArray
  /-- `a.field` (`a.length`). -/
  | member (a : JsInline) (field : String)
  deriving Inhabited, Repr

/-- The operations written inline, indexed by the types of their arguments and of their
    result. -/
inductive JsOpInlined : List JsTy → JsTy → Type where
  /-- `BigInt(a.length)` (Array.size) -/
  | bigint_nat__lean_array_get_size : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpInlined [A] (.terminal .bigint_nat)
  /-- `a.length` (Array.size) -/
  | uint53__lean_array_get_size : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpInlined [A] (.terminal .uint53)
  /-- `a` (Array.toList) -/
  | array__lean_array_to_list : (α : JsTy) → JsOpInlined [(.array α)] (.list α)
  /-- `[]` (Array.emptyWithCapacity) -/
  | bigint_nat__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity : (α : JsTy) → JsOpInlined [(.terminal .bigint_nat)] (.array α)
  /-- `new C(0)` (Array.emptyWithCapacity) -/
  | typedArray__bigint_nat__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity : (k : JsTypedArray) → (e : JsTerminalTy) → JsOpInlined [(.terminal .bigint_nat)] (.typedArray k e)
  /-- `[]` (Array.emptyWithCapacity) -/
  | uint53__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity : (α : JsTy) → JsOpInlined [(.terminal .uint53)] (.array α)
  /-- `new C(0)` (Array.emptyWithCapacity) -/
  | typedArray__uint53__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity : (k : JsTypedArray) → (e : JsTerminalTy) → JsOpInlined [(.terminal .uint53)] (.typedArray k e)
  /-- `[]` (Array.mkEmpty) -/
  | bigint_nat__lean_mk_empty_array_with_capacity__Array_mkEmpty : (α : JsTy) → JsOpInlined [(.terminal .bigint_nat)] (.array α)
  /-- `new C(0)` (Array.mkEmpty) -/
  | typedArray__bigint_nat__lean_mk_empty_array_with_capacity__Array_mkEmpty : (k : JsTypedArray) → (e : JsTerminalTy) → JsOpInlined [(.terminal .bigint_nat)] (.typedArray k e)
  /-- `[]` (Array.mkEmpty) -/
  | uint53__lean_mk_empty_array_with_capacity__Array_mkEmpty : (α : JsTy) → JsOpInlined [(.terminal .uint53)] (.array α)
  /-- `new C(0)` (Array.mkEmpty) -/
  | typedArray__uint53__lean_mk_empty_array_with_capacity__Array_mkEmpty : (k : JsTypedArray) → (e : JsTerminalTy) → JsOpInlined [(.terminal .uint53)] (.typedArray k e)
  /-- `a` (Array.mk) -/
  | array__lean_array_mk : (α : JsTy) → JsOpInlined [(.list α)] (.array α)
  /-- `C.from(a)` (Array.mk) -/
  | typedArray__lean_array_mk : (k : JsTypedArray) → (e : JsTerminalTy) → JsOpInlined [(.list (.terminal e))] (.typedArray k e)
  /-- `a` (UInt32.ofBitVec) -/
  | bitvec32__lean_uint32_of_nat_mk : JsOpInlined [(.terminal (.bitvec_small 32 (by decide) (by decide)))] (.terminal .uint32)
  /-- `a === b` (UInt32.decEq) -/
  | uint32__lean_uint32_dec_eq : JsOpInlined [(.terminal .uint32), (.terminal .uint32)] (.terminal .bool)
  /-- `a < b` (UInt32.decLt) -/
  | uint32__lean_uint32_dec_lt : JsOpInlined [(.terminal .uint32), (.terminal .uint32)] (.terminal .bool)
  /-- `a` (UInt8.toBitVec) -/
  | uint8__lean_uint8_to_nat__UInt8_toBitVec : JsOpInlined [(.terminal .uint8)] (.terminal (.bitvec_small 8 (by decide) (by decide)))
  /-- `a < b` (Nat.decLt) -/
  | bigint_nat__lean_nat_dec_lt : JsOpInlined [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bool)
  /-- `a < b` (Nat.decLt) -/
  | uint53__lean_nat_dec_lt : JsOpInlined [(.terminal .uint53), (.terminal .uint53)] (.terminal .bool)
  /-- `a < b` (UInt8.decLt) -/
  | uint8__lean_uint8_dec_lt : JsOpInlined [(.terminal .uint8), (.terminal .uint8)] (.terminal .bool)
  /-- `a <= b` (UInt32.decLe) -/
  | uint32__lean_uint32_dec_le : JsOpInlined [(.terminal .uint32), (.terminal .uint32)] (.terminal .bool)
  /-- `a === b` (Nat.decEq) -/
  | bigint_nat__lean_nat_dec_eq__Nat_decEq : JsOpInlined [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bool)
  /-- `a === b` (Nat.decEq) -/
  | uint53__lean_nat_dec_eq__Nat_decEq : JsOpInlined [(.terminal .uint53), (.terminal .uint53)] (.terminal .bool)
  /-- `a === b` (Nat.beq) -/
  | bigint_nat__lean_nat_dec_eq__Nat_beq : JsOpInlined [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bool)
  /-- `a === b` (Nat.beq) -/
  | uint53__lean_nat_dec_eq__Nat_beq : JsOpInlined [(.terminal .uint53), (.terminal .uint53)] (.terminal .bool)
  /-- `a <= b` (UInt8.decLe) -/
  | uint8__lean_uint8_dec_le : JsOpInlined [(.terminal .uint8), (.terminal .uint8)] (.terminal .bool)
  /-- `a <= b` (Nat.ble) -/
  | bigint_nat__lean_nat_dec_le__Nat_ble : JsOpInlined [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bool)
  /-- `a <= b` (Nat.ble) -/
  | uint53__lean_nat_dec_le__Nat_ble : JsOpInlined [(.terminal .uint53), (.terminal .uint53)] (.terminal .bool)
  /-- `a <= b` (Nat.decLe) -/
  | bigint_nat__lean_nat_dec_le__Nat_decLe : JsOpInlined [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bool)
  /-- `a <= b` (Nat.decLe) -/
  | uint53__lean_nat_dec_le__Nat_decLe : JsOpInlined [(.terminal .uint53), (.terminal .uint53)] (.terminal .bool)
  /-- `a + b` (Nat.add) -/
  | bigint_nat__lean_nat_add : JsOpInlined [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- `a` (UInt16.toBitVec) -/
  | uint16__lean_uint16_to_nat__UInt16_toBitVec : JsOpInlined [(.terminal .uint16)] (.terminal (.bitvec_small 16 (by decide) (by decide)))
  /-- `a` (UInt16.ofBitVec) -/
  | bitvec16__lean_uint16_of_nat_mk : JsOpInlined [(.terminal (.bitvec_small 16 (by decide) (by decide)))] (.terminal .uint16)
  /-- `a === b` (UInt16.decEq) -/
  | uint16__lean_uint16_dec_eq : JsOpInlined [(.terminal .uint16), (.terminal .uint16)] (.terminal .bool)
  /-- `a === b` (String.decEq) -/
  | string__lean_string_dec_eq : JsOpInlined [(.terminal .string), (.terminal .string)] (.terminal .bool)
  /-- `a` (UInt64.toBitVec) -/
  | bigint_nat__bigint_bitvec64__lean_uint64_to_nat__UInt64_toBitVec : JsOpInlined [(.terminal .bigint_nat)] (.terminal (.bigint_bitvec_big 64 (by decide)))
  /-- `BigInt(a)` (UInt64.toBitVec) -/
  | uint53__bigint_bitvec64__lean_uint64_to_nat__UInt64_toBitVec : JsOpInlined [(.terminal .uint53)] (.terminal (.bigint_bitvec_big 64 (by decide)))
  /-- `a` (UInt64.toBitVec) -/
  | uint53__int53_bitvec64__lean_uint64_to_nat__UInt64_toBitVec : JsOpInlined [(.terminal .uint53)] (.terminal (.int53_bitvec_big 64 (by decide)))
  /-- `a` (UInt64.ofBitVec) -/
  | bigint_bitvec64__bigint_nat__lean_uint64_of_nat_mk : JsOpInlined [(.terminal (.bigint_bitvec_big 64 (by decide)))] (.terminal .bigint_nat)
  /-- `BigInt(a)` (UInt64.ofBitVec) -/
  | int53_bitvec64__bigint_nat__lean_uint64_of_nat_mk : JsOpInlined [(.terminal (.int53_bitvec_big 64 (by decide)))] (.terminal .bigint_nat)
  /-- `a` (UInt64.ofBitVec) -/
  | int53_bitvec64__uint53__lean_uint64_of_nat_mk : JsOpInlined [(.terminal (.int53_bitvec_big 64 (by decide)))] (.terminal .uint53)
  /-- `BigInt(a)` (UInt32.toNat) -/
  | bigint_nat__lean_uint32_to_nat__UInt32_toNat : JsOpInlined [(.terminal .uint32)] (.terminal .bigint_nat)
  /-- `a` (UInt32.toNat) -/
  | uint53__lean_uint32_to_nat__UInt32_toNat : JsOpInlined [(.terminal .uint32)] (.terminal .uint53)
  /-- `a` (UInt32.toBitVec) -/
  | uint32__lean_uint32_to_nat__UInt32_toBitVec : JsOpInlined [(.terminal .uint32)] (.terminal (.bitvec_small 32 (by decide) (by decide)))
  /-- `a === b` (UInt64.decEq) -/
  | bigint_nat__lean_uint64_dec_eq : JsOpInlined [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bool)
  /-- `a === b` (UInt64.decEq) -/
  | uint53__lean_uint64_dec_eq : JsOpInlined [(.terminal .uint53), (.terminal .uint53)] (.terminal .bool)
  /-- `a` (UInt8.ofBitVec) -/
  | bitvec8__lean_uint8_of_nat_mk : JsOpInlined [(.terminal (.bitvec_small 8 (by decide) (by decide)))] (.terminal .uint8)
  /-- `a === b` (UInt8.decEq) -/
  | uint8__lean_uint8_dec_eq : JsOpInlined [(.terminal .uint8), (.terminal .uint8)] (.terminal .bool)
  /-- `a * b` (Nat.mul) -/
  | bigint_nat__lean_nat_mul : JsOpInlined [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- `a || b` (strictOr) -/
  | bool__lean_strict_or : JsOpInlined [(.terminal .bool), (.terminal .bool)] (.terminal .bool)
  /-- `a && b` (strictAnd) -/
  | bool__lean_strict_and : JsOpInlined [(.terminal .bool), (.terminal .bool)] (.terminal .bool)
  /-- `a` (Int.ofNat) -/
  | bigint_nat__bigint_int__lean_nat_to_int : JsOpInlined [(.terminal .bigint_nat)] (.terminal .bigint_int)
  /-- `BigInt(a)` (Int.ofNat) -/
  | uint53__bigint_int__lean_nat_to_int : JsOpInlined [(.terminal .uint53)] (.terminal .bigint_int)
  /-- `a` (Int.ofNat) -/
  | uint53__int53__lean_nat_to_int : JsOpInlined [(.terminal .uint53)] (.terminal .int53)
  /-- `a <= b` (Int.decLe) -/
  | bigint_int__lean_int_dec_le : JsOpInlined [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bool)
  /-- `a <= b` (Int.decLe) -/
  | int53__lean_int_dec_le : JsOpInlined [(.terminal .int53), (.terminal .int53)] (.terminal .bool)
  /-- `a < b` (Int.decLt) -/
  | bigint_int__lean_int_dec_lt : JsOpInlined [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bool)
  /-- `a < b` (Int.decLt) -/
  | int53__lean_int_dec_lt : JsOpInlined [(.terminal .int53), (.terminal .int53)] (.terminal .bool)
  /-- `a === b` (Int.decEq) -/
  | bigint_int__lean_int_dec_eq : JsOpInlined [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bool)
  /-- `a === b` (Int.decEq) -/
  | int53__lean_int_dec_eq : JsOpInlined [(.terminal .int53), (.terminal .int53)] (.terminal .bool)
  /-- `a * b` (Int.mul) -/
  | bigint_int__lean_int_mul : JsOpInlined [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- `a >= 0n` (Int.decNonneg) -/
  | bigint_int__lean_int_dec_nonneg : JsOpInlined [(.terminal .bigint_int)] (.terminal .bool)
  /-- `a >= 0` (Int.decNonneg) -/
  | int53__lean_int_dec_nonneg : JsOpInlined [(.terminal .int53)] (.terminal .bool)
  /-- `a + b` (Int.add) -/
  | bigint_int__lean_int_add : JsOpInlined [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- `-a` (Int.neg) -/
  | bigint_int__lean_int_neg : JsOpInlined [(.terminal .bigint_int)] (.terminal .bigint_int)
  /-- `a - b` (Int.sub) -/
  | bigint_int__lean_int_sub : JsOpInlined [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- `a ^ b` (Nat.xor) -/
  | bigint_nat__lean_nat_lxor : JsOpInlined [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- `a << b` (Nat.shiftLeft) -/
  | bigint_nat__lean_nat_shiftl : JsOpInlined [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- `a >> b` (Nat.shiftRight) -/
  | bigint_nat__lean_nat_shiftr : JsOpInlined [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- `a & b` (Nat.land) -/
  | bigint_nat__lean_nat_land : JsOpInlined [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- `a | b` (Nat.lor) -/
  | bigint_nat__lean_nat_lor : JsOpInlined [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- `a` (UInt64.toNat) -/
  | bigint_nat__lean_uint64_to_nat__UInt64_toNat : JsOpInlined [(.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- `BigInt(a)` (UInt64.toNat) -/
  | uint53__bigint_nat__lean_uint64_to_nat__UInt64_toNat : JsOpInlined [(.terminal .uint53)] (.terminal .bigint_nat)
  /-- `a` (UInt64.toNat) -/
  | uint53__lean_uint64_to_nat__UInt64_toNat : JsOpInlined [(.terminal .uint53)] (.terminal .uint53)
  /-- `a` (UInt16.toUInt32) -/
  | uint16__lean_uint16_to_uint32 : JsOpInlined [(.terminal .uint16)] (.terminal .uint32)
  /-- `BigInt(a)` (UInt32.toUInt64) -/
  | bigint_nat__lean_uint32_to_uint64 : JsOpInlined [(.terminal .uint32)] (.terminal .bigint_nat)
  /-- `a` (UInt32.toUInt64) -/
  | uint53__lean_uint32_to_uint64 : JsOpInlined [(.terminal .uint32)] (.terminal .uint53)
  /-- `BigInt(a)` (UInt16.toNat) -/
  | bigint_nat__lean_uint16_to_nat__UInt16_toNat : JsOpInlined [(.terminal .uint16)] (.terminal .bigint_nat)
  /-- `a` (UInt16.toNat) -/
  | uint53__lean_uint16_to_nat__UInt16_toNat : JsOpInlined [(.terminal .uint16)] (.terminal .uint53)
  /-- `BigInt(a)` (UInt8.toUInt64) -/
  | bigint_nat__lean_uint8_to_uint64 : JsOpInlined [(.terminal .uint8)] (.terminal .bigint_nat)
  /-- `a` (UInt8.toUInt64) -/
  | uint53__lean_uint8_to_uint64 : JsOpInlined [(.terminal .uint8)] (.terminal .uint53)
  /-- `BigInt(a)` (UInt8.toNat) -/
  | bigint_nat__lean_uint8_to_nat__UInt8_toNat : JsOpInlined [(.terminal .uint8)] (.terminal .bigint_nat)
  /-- `a` (UInt8.toNat) -/
  | uint53__lean_uint8_to_nat__UInt8_toNat : JsOpInlined [(.terminal .uint8)] (.terminal .uint53)
  /-- `a` (UInt8.toUInt32) -/
  | uint8__lean_uint8_to_uint32 : JsOpInlined [(.terminal .uint8)] (.terminal .uint32)
  /-- `BigInt(a)` (UInt16.toUInt64) -/
  | bigint_nat__lean_uint16_to_uint64 : JsOpInlined [(.terminal .uint16)] (.terminal .bigint_nat)
  /-- `a` (UInt16.toUInt64) -/
  | uint53__lean_uint16_to_uint64 : JsOpInlined [(.terminal .uint16)] (.terminal .uint53)
  /-- `a` (UInt8.toUInt16) -/
  | uint8__lean_uint8_to_uint16 : JsOpInlined [(.terminal .uint8)] (.terminal .uint16)
  /-- `a < b` (UInt16.decLt) -/
  | uint16__lean_uint16_dec_lt : JsOpInlined [(.terminal .uint16), (.terminal .uint16)] (.terminal .bool)
  /-- `a <= b` (UInt16.decLe) -/
  | uint16__lean_uint16_dec_le : JsOpInlined [(.terminal .uint16), (.terminal .uint16)] (.terminal .bool)
  /-- `a <= b` (UInt64.decLe) -/
  | bigint_nat__lean_uint64_dec_le : JsOpInlined [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bool)
  /-- `a <= b` (UInt64.decLe) -/
  | uint53__lean_uint64_dec_le : JsOpInlined [(.terminal .uint53), (.terminal .uint53)] (.terminal .bool)
  /-- `a < b` (UInt64.decLt) -/
  | bigint_nat__lean_uint64_dec_lt : JsOpInlined [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bool)
  /-- `a < b` (UInt64.decLt) -/
  | uint53__lean_uint64_dec_lt : JsOpInlined [(.terminal .uint53), (.terminal .uint53)] (.terminal .bool)
  /-- `a` (Int8.toInt16) -/
  | int8__lean_int8_to_int16 : JsOpInlined [(.terminal .int8)] (.terminal .int16)
  /-- `a === b` (Int8.decEq) -/
  | int8__lean_int8_dec_eq : JsOpInlined [(.terminal .int8), (.terminal .int8)] (.terminal .bool)
  /-- `a < b` (Int8.decLt) -/
  | int8__lean_int8_dec_lt : JsOpInlined [(.terminal .int8), (.terminal .int8)] (.terminal .bool)
  /-- `a` (Int8.toInt32) -/
  | int8__lean_int8_to_int32 : JsOpInlined [(.terminal .int8)] (.terminal .int32)
  /-- `BigInt(a)` (Int8.toInt64) -/
  | bigint_int__lean_int8_to_int64 : JsOpInlined [(.terminal .int8)] (.terminal .bigint_int)
  /-- `a` (Int8.toInt64) -/
  | int53__lean_int8_to_int64 : JsOpInlined [(.terminal .int8)] (.terminal .int53)
  /-- `a <= b` (Int8.decLe) -/
  | int8__lean_int8_dec_le : JsOpInlined [(.terminal .int8), (.terminal .int8)] (.terminal .bool)
  /-- `BigInt(a)` (Int8.toInt) -/
  | bigint_int__lean_int8_to_int : JsOpInlined [(.terminal .int8)] (.terminal .bigint_int)
  /-- `a` (Int8.toInt) -/
  | int53__lean_int8_to_int : JsOpInlined [(.terminal .int8)] (.terminal .int53)
  /-- `a <= b` (Int16.decLe) -/
  | int16__lean_int16_dec_le : JsOpInlined [(.terminal .int16), (.terminal .int16)] (.terminal .bool)
  /-- `a < b` (Int16.decLt) -/
  | int16__lean_int16_dec_lt : JsOpInlined [(.terminal .int16), (.terminal .int16)] (.terminal .bool)
  /-- `BigInt(a)` (Int16.toInt) -/
  | bigint_int__lean_int16_to_int : JsOpInlined [(.terminal .int16)] (.terminal .bigint_int)
  /-- `a` (Int16.toInt) -/
  | int53__lean_int16_to_int : JsOpInlined [(.terminal .int16)] (.terminal .int53)
  /-- `a === b` (Int16.decEq) -/
  | int16__lean_int16_dec_eq : JsOpInlined [(.terminal .int16), (.terminal .int16)] (.terminal .bool)
  /-- `a` (Int16.toInt32) -/
  | int16__lean_int16_to_int32 : JsOpInlined [(.terminal .int16)] (.terminal .int32)
  /-- `BigInt(a)` (Int16.toInt64) -/
  | bigint_int__lean_int16_to_int64 : JsOpInlined [(.terminal .int16)] (.terminal .bigint_int)
  /-- `a` (Int16.toInt64) -/
  | int53__lean_int16_to_int64 : JsOpInlined [(.terminal .int16)] (.terminal .int53)
  /-- `a <= b` (Int32.decLe) -/
  | int32__lean_int32_dec_le : JsOpInlined [(.terminal .int32), (.terminal .int32)] (.terminal .bool)
  /-- `BigInt(a)` (Int32.toInt64) -/
  | bigint_int__lean_int32_to_int64 : JsOpInlined [(.terminal .int32)] (.terminal .bigint_int)
  /-- `a` (Int32.toInt64) -/
  | int53__lean_int32_to_int64 : JsOpInlined [(.terminal .int32)] (.terminal .int53)
  /-- `a === b` (Int32.decEq) -/
  | int32__lean_int32_dec_eq : JsOpInlined [(.terminal .int32), (.terminal .int32)] (.terminal .bool)
  /-- `a < b` (Int32.decLt) -/
  | int32__lean_int32_dec_lt : JsOpInlined [(.terminal .int32), (.terminal .int32)] (.terminal .bool)
  /-- `BigInt(a)` (Int32.toInt) -/
  | bigint_int__lean_int32_to_int : JsOpInlined [(.terminal .int32)] (.terminal .bigint_int)
  /-- `a` (Int32.toInt) -/
  | int53__lean_int32_to_int : JsOpInlined [(.terminal .int32)] (.terminal .int53)
  /-- `a < b` (Int64.decLt) -/
  | bigint_int__lean_int64_dec_lt : JsOpInlined [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bool)
  /-- `a < b` (Int64.decLt) -/
  | int53__lean_int64_dec_lt : JsOpInlined [(.terminal .int53), (.terminal .int53)] (.terminal .bool)
  /-- `a === b` (Int64.decEq) -/
  | bigint_int__lean_int64_dec_eq : JsOpInlined [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bool)
  /-- `a === b` (Int64.decEq) -/
  | int53__lean_int64_dec_eq : JsOpInlined [(.terminal .int53), (.terminal .int53)] (.terminal .bool)
  /-- `a <= b` (Int64.decLe) -/
  | bigint_int__lean_int64_dec_le : JsOpInlined [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bool)
  /-- `a <= b` (Int64.decLe) -/
  | int53__lean_int64_dec_le : JsOpInlined [(.terminal .int53), (.terminal .int53)] (.terminal .bool)
  /-- `a` (Int64.toInt) -/
  | bigint_int__lean_int64_to_int_sint : JsOpInlined [(.terminal .bigint_int)] (.terminal .bigint_int)
  /-- `BigInt(a)` (Int64.toInt) -/
  | int53__bigint_int__lean_int64_to_int_sint : JsOpInlined [(.terminal .int53)] (.terminal .bigint_int)
  /-- `a` (Int64.toInt) -/
  | int53__lean_int64_to_int_sint : JsOpInlined [(.terminal .int53)] (.terminal .int53)
  /-- `a + b` (String.Internal.append) -/
  | string__lean_string_append__String_Internal_append : JsOpInlined [(.terminal .string), (.terminal .string)] (.terminal .string)
  /-- `a + b` (String.push) -/
  | string__lean_string_push : JsOpInlined [(.terminal .string), (.terminal .string)] (.terminal .string)
  /-- `a + b` (String.append) -/
  | string__lean_string_append__String_append : JsOpInlined [(.terminal .string), (.terminal .string)] (.terminal .string)
  /-- `a < b` (String.decidableLT) -/
  | string__lean_string_dec_lt : JsOpInlined [(.terminal .string), (.terminal .string)] (.terminal .bool)
  /-- `a` (UInt8.toFloat) -/
  | uint8__lean_uint8_to_float : JsOpInlined [(.terminal .uint8)] (.terminal .float)
  /-- `a` (Float.toModel) -/
  | float__lean_float_to_bits__Float_toModel : JsOpInlined [(.terminal .float)] (.terminal .float)
  /-- `a` (Float.ofModel) -/
  | float__lean_float_of_bits__Float_ofModel : JsOpInlined [(.terminal .float)] (.terminal .float)
  /-- `a / b` (Float.div) -/
  | float__lean_float_div : JsOpInlined [(.terminal .float), (.terminal .float)] (.terminal .float)
  /-- `a === b` (Float.beq) -/
  | float__lean_float_beq : JsOpInlined [(.terminal .float), (.terminal .float)] (.terminal .bool)
  /-- `a` (UInt32.toFloat) -/
  | uint32__lean_uint32_to_float : JsOpInlined [(.terminal .uint32)] (.terminal .float)
  /-- `a <= b` (Float.decLe) -/
  | float__lean_float_decLe__Float_decLe : JsOpInlined [(.terminal .float), (.terminal .float)] (.terminal .bool)
  /-- `a <= b` (Float.le) -/
  | float__lean_float_decLe__Float_le : JsOpInlined [(.terminal .float), (.terminal .float)] (.terminal .bool)
  /-- `Number(a)` (UInt64.toFloat) -/
  | bigint_nat__lean_uint64_to_float : JsOpInlined [(.terminal .bigint_nat)] (.terminal .float)
  /-- `a` (UInt64.toFloat) -/
  | uint53__lean_uint64_to_float : JsOpInlined [(.terminal .uint53)] (.terminal .float)
  /-- `a < b` (Float.decLt) -/
  | float__lean_float_decLt__Float_decLt : JsOpInlined [(.terminal .float), (.terminal .float)] (.terminal .bool)
  /-- `a < b` (Float.lt) -/
  | float__lean_float_decLt__Float_lt : JsOpInlined [(.terminal .float), (.terminal .float)] (.terminal .bool)
  /-- `a * b` (Float.mul) -/
  | float__lean_float_mul : JsOpInlined [(.terminal .float), (.terminal .float)] (.terminal .float)
  /-- `a` (UInt16.toFloat) -/
  | uint16__lean_uint16_to_float : JsOpInlined [(.terminal .uint16)] (.terminal .float)
  /-- `a + b` (Float.add) -/
  | float__lean_float_add : JsOpInlined [(.terminal .float), (.terminal .float)] (.terminal .float)
  /-- `a - b` (Float.sub) -/
  | float__lean_float_sub : JsOpInlined [(.terminal .float), (.terminal .float)] (.terminal .float)
  /-- `-a` (Float.neg) -/
  | float__lean_float_negate : JsOpInlined [(.terminal .float)] (.terminal .float)
  /-- `a` (Int32.toFloat) -/
  | int32__lean_int32_to_float : JsOpInlined [(.terminal .int32)] (.terminal .float)
  /-- `a` (Int16.toFloat) -/
  | int16__lean_int16_to_float : JsOpInlined [(.terminal .int16)] (.terminal .float)
  /-- `a` (Int8.toFloat) -/
  | int8__lean_int8_to_float : JsOpInlined [(.terminal .int8)] (.terminal .float)
  /-- `Number(a)` (Int64.toFloat) -/
  | bigint_int__lean_int64_to_float : JsOpInlined [(.terminal .bigint_int)] (.terminal .float)
  /-- `a` (Int64.toFloat) -/
  | int53__lean_int64_to_float : JsOpInlined [(.terminal .int53)] (.terminal .float)
  /-- `a <= b` (Float32.le) -/
  | float32__lean_float32_decLe__Float32_le : JsOpInlined [(.terminal .float32), (.terminal .float32)] (.terminal .bool)
  /-- `a <= b` (Float32.decLe) -/
  | float32__lean_float32_decLe__Float32_decLe : JsOpInlined [(.terminal .float32), (.terminal .float32)] (.terminal .bool)
  /-- `a` (Float32.toModel) -/
  | float32__lean_float32_to_bits__Float32_toModel : JsOpInlined [(.terminal .float32)] (.terminal .float32)
  /-- `a` (Float32.ofModel) -/
  | float32__lean_float32_of_bits__Float32_ofModel : JsOpInlined [(.terminal .float32)] (.terminal .float32)
  /-- `a === b` (Float32.beq) -/
  | float32__lean_float32_beq : JsOpInlined [(.terminal .float32), (.terminal .float32)] (.terminal .bool)
  /-- `a` (UInt8.toFloat32) -/
  | uint8__lean_uint8_to_float32 : JsOpInlined [(.terminal .uint8)] (.terminal .float32)
  /-- `a` (Float32.toFloat) -/
  | float32__lean_float32_to_float : JsOpInlined [(.terminal .float32)] (.terminal .float)
  /-- `a` (UInt32.toFloat32) -/
  | uint32__lean_uint32_to_float32 : JsOpInlined [(.terminal .uint32)] (.terminal .float32)
  /-- `-a` (Float32.neg) -/
  | float32__lean_float32_negate : JsOpInlined [(.terminal .float32)] (.terminal .float32)
  /-- `Number(a)` (UInt64.toFloat32) -/
  | bigint_nat__lean_uint64_to_float32 : JsOpInlined [(.terminal .bigint_nat)] (.terminal .float32)
  /-- `Number(a)` (UInt64.toFloat32) -/
  | uint53__lean_uint64_to_float32 : JsOpInlined [(.terminal .uint53)] (.terminal .float32)
  /-- `a < b` (Float32.lt) -/
  | float32__lean_float32_decLt__Float32_lt : JsOpInlined [(.terminal .float32), (.terminal .float32)] (.terminal .bool)
  /-- `a < b` (Float32.decLt) -/
  | float32__lean_float32_decLt__Float32_decLt : JsOpInlined [(.terminal .float32), (.terminal .float32)] (.terminal .bool)
  /-- `a` (UInt16.toFloat32) -/
  | uint16__lean_uint16_to_float32 : JsOpInlined [(.terminal .uint16)] (.terminal .float32)
  /-- `a` (Int32.toFloat32) -/
  | int32__lean_int32_to_float32 : JsOpInlined [(.terminal .int32)] (.terminal .float32)
  /-- `a` (Int8.toFloat32) -/
  | int8__lean_int8_to_float32 : JsOpInlined [(.terminal .int8)] (.terminal .float32)
  /-- `a` (Int16.toFloat32) -/
  | int16__lean_int16_to_float32 : JsOpInlined [(.terminal .int16)] (.terminal .float32)
  /-- `Number(a)` (Int64.toFloat32) -/
  | bigint_int__lean_int64_to_float32 : JsOpInlined [(.terminal .bigint_int)] (.terminal .float32)
  /-- `Number(a)` (Int64.toFloat32) -/
  | int53__lean_int64_to_float32 : JsOpInlined [(.terminal .int53)] (.terminal .float32)

namespace JsOpInlined

/-- The name of the operation. -/
def name {σs : List JsTy} {τ : JsTy} : JsOpInlined σs τ → String
  | .bigint_nat__lean_array_get_size _ => "bigint_nat__lean_array_get_size"
  | .uint53__lean_array_get_size _ => "uint53__lean_array_get_size"
  | .array__lean_array_to_list _ => "array__lean_array_to_list"
  | .bigint_nat__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity _ => "bigint_nat__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity"
  | .typedArray__bigint_nat__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity _ _ => "typedArray__bigint_nat__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity"
  | .uint53__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity _ => "uint53__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity"
  | .typedArray__uint53__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity _ _ => "typedArray__uint53__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity"
  | .bigint_nat__lean_mk_empty_array_with_capacity__Array_mkEmpty _ => "bigint_nat__lean_mk_empty_array_with_capacity__Array_mkEmpty"
  | .typedArray__bigint_nat__lean_mk_empty_array_with_capacity__Array_mkEmpty _ _ => "typedArray__bigint_nat__lean_mk_empty_array_with_capacity__Array_mkEmpty"
  | .uint53__lean_mk_empty_array_with_capacity__Array_mkEmpty _ => "uint53__lean_mk_empty_array_with_capacity__Array_mkEmpty"
  | .typedArray__uint53__lean_mk_empty_array_with_capacity__Array_mkEmpty _ _ => "typedArray__uint53__lean_mk_empty_array_with_capacity__Array_mkEmpty"
  | .array__lean_array_mk _ => "array__lean_array_mk"
  | .typedArray__lean_array_mk _ _ => "typedArray__lean_array_mk"
  | .bitvec32__lean_uint32_of_nat_mk => "bitvec32__lean_uint32_of_nat_mk"
  | .uint32__lean_uint32_dec_eq => "uint32__lean_uint32_dec_eq"
  | .uint32__lean_uint32_dec_lt => "uint32__lean_uint32_dec_lt"
  | .uint8__lean_uint8_to_nat__UInt8_toBitVec => "uint8__lean_uint8_to_nat__UInt8_toBitVec"
  | .bigint_nat__lean_nat_dec_lt => "bigint_nat__lean_nat_dec_lt"
  | .uint53__lean_nat_dec_lt => "uint53__lean_nat_dec_lt"
  | .uint8__lean_uint8_dec_lt => "uint8__lean_uint8_dec_lt"
  | .uint32__lean_uint32_dec_le => "uint32__lean_uint32_dec_le"
  | .bigint_nat__lean_nat_dec_eq__Nat_decEq => "bigint_nat__lean_nat_dec_eq__Nat_decEq"
  | .uint53__lean_nat_dec_eq__Nat_decEq => "uint53__lean_nat_dec_eq__Nat_decEq"
  | .bigint_nat__lean_nat_dec_eq__Nat_beq => "bigint_nat__lean_nat_dec_eq__Nat_beq"
  | .uint53__lean_nat_dec_eq__Nat_beq => "uint53__lean_nat_dec_eq__Nat_beq"
  | .uint8__lean_uint8_dec_le => "uint8__lean_uint8_dec_le"
  | .bigint_nat__lean_nat_dec_le__Nat_ble => "bigint_nat__lean_nat_dec_le__Nat_ble"
  | .uint53__lean_nat_dec_le__Nat_ble => "uint53__lean_nat_dec_le__Nat_ble"
  | .bigint_nat__lean_nat_dec_le__Nat_decLe => "bigint_nat__lean_nat_dec_le__Nat_decLe"
  | .uint53__lean_nat_dec_le__Nat_decLe => "uint53__lean_nat_dec_le__Nat_decLe"
  | .bigint_nat__lean_nat_add => "bigint_nat__lean_nat_add"
  | .uint16__lean_uint16_to_nat__UInt16_toBitVec => "uint16__lean_uint16_to_nat__UInt16_toBitVec"
  | .bitvec16__lean_uint16_of_nat_mk => "bitvec16__lean_uint16_of_nat_mk"
  | .uint16__lean_uint16_dec_eq => "uint16__lean_uint16_dec_eq"
  | .string__lean_string_dec_eq => "string__lean_string_dec_eq"
  | .bigint_nat__bigint_bitvec64__lean_uint64_to_nat__UInt64_toBitVec => "bigint_nat__bigint_bitvec64__lean_uint64_to_nat__UInt64_toBitVec"
  | .uint53__bigint_bitvec64__lean_uint64_to_nat__UInt64_toBitVec => "uint53__bigint_bitvec64__lean_uint64_to_nat__UInt64_toBitVec"
  | .uint53__int53_bitvec64__lean_uint64_to_nat__UInt64_toBitVec => "uint53__int53_bitvec64__lean_uint64_to_nat__UInt64_toBitVec"
  | .bigint_bitvec64__bigint_nat__lean_uint64_of_nat_mk => "bigint_bitvec64__bigint_nat__lean_uint64_of_nat_mk"
  | .int53_bitvec64__bigint_nat__lean_uint64_of_nat_mk => "int53_bitvec64__bigint_nat__lean_uint64_of_nat_mk"
  | .int53_bitvec64__uint53__lean_uint64_of_nat_mk => "int53_bitvec64__uint53__lean_uint64_of_nat_mk"
  | .bigint_nat__lean_uint32_to_nat__UInt32_toNat => "bigint_nat__lean_uint32_to_nat__UInt32_toNat"
  | .uint53__lean_uint32_to_nat__UInt32_toNat => "uint53__lean_uint32_to_nat__UInt32_toNat"
  | .uint32__lean_uint32_to_nat__UInt32_toBitVec => "uint32__lean_uint32_to_nat__UInt32_toBitVec"
  | .bigint_nat__lean_uint64_dec_eq => "bigint_nat__lean_uint64_dec_eq"
  | .uint53__lean_uint64_dec_eq => "uint53__lean_uint64_dec_eq"
  | .bitvec8__lean_uint8_of_nat_mk => "bitvec8__lean_uint8_of_nat_mk"
  | .uint8__lean_uint8_dec_eq => "uint8__lean_uint8_dec_eq"
  | .bigint_nat__lean_nat_mul => "bigint_nat__lean_nat_mul"
  | .bool__lean_strict_or => "bool__lean_strict_or"
  | .bool__lean_strict_and => "bool__lean_strict_and"
  | .bigint_nat__bigint_int__lean_nat_to_int => "bigint_nat__bigint_int__lean_nat_to_int"
  | .uint53__bigint_int__lean_nat_to_int => "uint53__bigint_int__lean_nat_to_int"
  | .uint53__int53__lean_nat_to_int => "uint53__int53__lean_nat_to_int"
  | .bigint_int__lean_int_dec_le => "bigint_int__lean_int_dec_le"
  | .int53__lean_int_dec_le => "int53__lean_int_dec_le"
  | .bigint_int__lean_int_dec_lt => "bigint_int__lean_int_dec_lt"
  | .int53__lean_int_dec_lt => "int53__lean_int_dec_lt"
  | .bigint_int__lean_int_dec_eq => "bigint_int__lean_int_dec_eq"
  | .int53__lean_int_dec_eq => "int53__lean_int_dec_eq"
  | .bigint_int__lean_int_mul => "bigint_int__lean_int_mul"
  | .bigint_int__lean_int_dec_nonneg => "bigint_int__lean_int_dec_nonneg"
  | .int53__lean_int_dec_nonneg => "int53__lean_int_dec_nonneg"
  | .bigint_int__lean_int_add => "bigint_int__lean_int_add"
  | .bigint_int__lean_int_neg => "bigint_int__lean_int_neg"
  | .bigint_int__lean_int_sub => "bigint_int__lean_int_sub"
  | .bigint_nat__lean_nat_lxor => "bigint_nat__lean_nat_lxor"
  | .bigint_nat__lean_nat_shiftl => "bigint_nat__lean_nat_shiftl"
  | .bigint_nat__lean_nat_shiftr => "bigint_nat__lean_nat_shiftr"
  | .bigint_nat__lean_nat_land => "bigint_nat__lean_nat_land"
  | .bigint_nat__lean_nat_lor => "bigint_nat__lean_nat_lor"
  | .bigint_nat__lean_uint64_to_nat__UInt64_toNat => "bigint_nat__lean_uint64_to_nat__UInt64_toNat"
  | .uint53__bigint_nat__lean_uint64_to_nat__UInt64_toNat => "uint53__bigint_nat__lean_uint64_to_nat__UInt64_toNat"
  | .uint53__lean_uint64_to_nat__UInt64_toNat => "uint53__lean_uint64_to_nat__UInt64_toNat"
  | .uint16__lean_uint16_to_uint32 => "uint16__lean_uint16_to_uint32"
  | .bigint_nat__lean_uint32_to_uint64 => "bigint_nat__lean_uint32_to_uint64"
  | .uint53__lean_uint32_to_uint64 => "uint53__lean_uint32_to_uint64"
  | .bigint_nat__lean_uint16_to_nat__UInt16_toNat => "bigint_nat__lean_uint16_to_nat__UInt16_toNat"
  | .uint53__lean_uint16_to_nat__UInt16_toNat => "uint53__lean_uint16_to_nat__UInt16_toNat"
  | .bigint_nat__lean_uint8_to_uint64 => "bigint_nat__lean_uint8_to_uint64"
  | .uint53__lean_uint8_to_uint64 => "uint53__lean_uint8_to_uint64"
  | .bigint_nat__lean_uint8_to_nat__UInt8_toNat => "bigint_nat__lean_uint8_to_nat__UInt8_toNat"
  | .uint53__lean_uint8_to_nat__UInt8_toNat => "uint53__lean_uint8_to_nat__UInt8_toNat"
  | .uint8__lean_uint8_to_uint32 => "uint8__lean_uint8_to_uint32"
  | .bigint_nat__lean_uint16_to_uint64 => "bigint_nat__lean_uint16_to_uint64"
  | .uint53__lean_uint16_to_uint64 => "uint53__lean_uint16_to_uint64"
  | .uint8__lean_uint8_to_uint16 => "uint8__lean_uint8_to_uint16"
  | .uint16__lean_uint16_dec_lt => "uint16__lean_uint16_dec_lt"
  | .uint16__lean_uint16_dec_le => "uint16__lean_uint16_dec_le"
  | .bigint_nat__lean_uint64_dec_le => "bigint_nat__lean_uint64_dec_le"
  | .uint53__lean_uint64_dec_le => "uint53__lean_uint64_dec_le"
  | .bigint_nat__lean_uint64_dec_lt => "bigint_nat__lean_uint64_dec_lt"
  | .uint53__lean_uint64_dec_lt => "uint53__lean_uint64_dec_lt"
  | .int8__lean_int8_to_int16 => "int8__lean_int8_to_int16"
  | .int8__lean_int8_dec_eq => "int8__lean_int8_dec_eq"
  | .int8__lean_int8_dec_lt => "int8__lean_int8_dec_lt"
  | .int8__lean_int8_to_int32 => "int8__lean_int8_to_int32"
  | .bigint_int__lean_int8_to_int64 => "bigint_int__lean_int8_to_int64"
  | .int53__lean_int8_to_int64 => "int53__lean_int8_to_int64"
  | .int8__lean_int8_dec_le => "int8__lean_int8_dec_le"
  | .bigint_int__lean_int8_to_int => "bigint_int__lean_int8_to_int"
  | .int53__lean_int8_to_int => "int53__lean_int8_to_int"
  | .int16__lean_int16_dec_le => "int16__lean_int16_dec_le"
  | .int16__lean_int16_dec_lt => "int16__lean_int16_dec_lt"
  | .bigint_int__lean_int16_to_int => "bigint_int__lean_int16_to_int"
  | .int53__lean_int16_to_int => "int53__lean_int16_to_int"
  | .int16__lean_int16_dec_eq => "int16__lean_int16_dec_eq"
  | .int16__lean_int16_to_int32 => "int16__lean_int16_to_int32"
  | .bigint_int__lean_int16_to_int64 => "bigint_int__lean_int16_to_int64"
  | .int53__lean_int16_to_int64 => "int53__lean_int16_to_int64"
  | .int32__lean_int32_dec_le => "int32__lean_int32_dec_le"
  | .bigint_int__lean_int32_to_int64 => "bigint_int__lean_int32_to_int64"
  | .int53__lean_int32_to_int64 => "int53__lean_int32_to_int64"
  | .int32__lean_int32_dec_eq => "int32__lean_int32_dec_eq"
  | .int32__lean_int32_dec_lt => "int32__lean_int32_dec_lt"
  | .bigint_int__lean_int32_to_int => "bigint_int__lean_int32_to_int"
  | .int53__lean_int32_to_int => "int53__lean_int32_to_int"
  | .bigint_int__lean_int64_dec_lt => "bigint_int__lean_int64_dec_lt"
  | .int53__lean_int64_dec_lt => "int53__lean_int64_dec_lt"
  | .bigint_int__lean_int64_dec_eq => "bigint_int__lean_int64_dec_eq"
  | .int53__lean_int64_dec_eq => "int53__lean_int64_dec_eq"
  | .bigint_int__lean_int64_dec_le => "bigint_int__lean_int64_dec_le"
  | .int53__lean_int64_dec_le => "int53__lean_int64_dec_le"
  | .bigint_int__lean_int64_to_int_sint => "bigint_int__lean_int64_to_int_sint"
  | .int53__bigint_int__lean_int64_to_int_sint => "int53__bigint_int__lean_int64_to_int_sint"
  | .int53__lean_int64_to_int_sint => "int53__lean_int64_to_int_sint"
  | .string__lean_string_append__String_Internal_append => "string__lean_string_append__String_Internal_append"
  | .string__lean_string_push => "string__lean_string_push"
  | .string__lean_string_append__String_append => "string__lean_string_append__String_append"
  | .string__lean_string_dec_lt => "string__lean_string_dec_lt"
  | .uint8__lean_uint8_to_float => "uint8__lean_uint8_to_float"
  | .float__lean_float_to_bits__Float_toModel => "float__lean_float_to_bits__Float_toModel"
  | .float__lean_float_of_bits__Float_ofModel => "float__lean_float_of_bits__Float_ofModel"
  | .float__lean_float_div => "float__lean_float_div"
  | .float__lean_float_beq => "float__lean_float_beq"
  | .uint32__lean_uint32_to_float => "uint32__lean_uint32_to_float"
  | .float__lean_float_decLe__Float_decLe => "float__lean_float_decLe__Float_decLe"
  | .float__lean_float_decLe__Float_le => "float__lean_float_decLe__Float_le"
  | .bigint_nat__lean_uint64_to_float => "bigint_nat__lean_uint64_to_float"
  | .uint53__lean_uint64_to_float => "uint53__lean_uint64_to_float"
  | .float__lean_float_decLt__Float_decLt => "float__lean_float_decLt__Float_decLt"
  | .float__lean_float_decLt__Float_lt => "float__lean_float_decLt__Float_lt"
  | .float__lean_float_mul => "float__lean_float_mul"
  | .uint16__lean_uint16_to_float => "uint16__lean_uint16_to_float"
  | .float__lean_float_add => "float__lean_float_add"
  | .float__lean_float_sub => "float__lean_float_sub"
  | .float__lean_float_negate => "float__lean_float_negate"
  | .int32__lean_int32_to_float => "int32__lean_int32_to_float"
  | .int16__lean_int16_to_float => "int16__lean_int16_to_float"
  | .int8__lean_int8_to_float => "int8__lean_int8_to_float"
  | .bigint_int__lean_int64_to_float => "bigint_int__lean_int64_to_float"
  | .int53__lean_int64_to_float => "int53__lean_int64_to_float"
  | .float32__lean_float32_decLe__Float32_le => "float32__lean_float32_decLe__Float32_le"
  | .float32__lean_float32_decLe__Float32_decLe => "float32__lean_float32_decLe__Float32_decLe"
  | .float32__lean_float32_to_bits__Float32_toModel => "float32__lean_float32_to_bits__Float32_toModel"
  | .float32__lean_float32_of_bits__Float32_ofModel => "float32__lean_float32_of_bits__Float32_ofModel"
  | .float32__lean_float32_beq => "float32__lean_float32_beq"
  | .uint8__lean_uint8_to_float32 => "uint8__lean_uint8_to_float32"
  | .float32__lean_float32_to_float => "float32__lean_float32_to_float"
  | .uint32__lean_uint32_to_float32 => "uint32__lean_uint32_to_float32"
  | .float32__lean_float32_negate => "float32__lean_float32_negate"
  | .bigint_nat__lean_uint64_to_float32 => "bigint_nat__lean_uint64_to_float32"
  | .uint53__lean_uint64_to_float32 => "uint53__lean_uint64_to_float32"
  | .float32__lean_float32_decLt__Float32_lt => "float32__lean_float32_decLt__Float32_lt"
  | .float32__lean_float32_decLt__Float32_decLt => "float32__lean_float32_decLt__Float32_decLt"
  | .uint16__lean_uint16_to_float32 => "uint16__lean_uint16_to_float32"
  | .int32__lean_int32_to_float32 => "int32__lean_int32_to_float32"
  | .int8__lean_int8_to_float32 => "int8__lean_int8_to_float32"
  | .int16__lean_int16_to_float32 => "int16__lean_int16_to_float32"
  | .bigint_int__lean_int64_to_float32 => "bigint_int__lean_int64_to_float32"
  | .int53__lean_int64_to_float32 => "int53__lean_int64_to_float32"

/-- The JavaScript of the operation, over its arguments. -/
def template {σs : List JsTy} {τ : JsTy} : JsOpInlined σs τ → JsInline
  | .bigint_nat__lean_array_get_size _ => .call "BigInt" [.member (.arg 0) "length"]
  | .uint53__lean_array_get_size _ => .member (.arg 0) "length"
  | .array__lean_array_to_list _ => .arg 0
  | .bigint_nat__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity _ => .emptyArray
  | .typedArray__bigint_nat__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity k _ => .new k.ctorName [.num 0]
  | .uint53__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity _ => .emptyArray
  | .typedArray__uint53__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity k _ => .new k.ctorName [.num 0]
  | .bigint_nat__lean_mk_empty_array_with_capacity__Array_mkEmpty _ => .emptyArray
  | .typedArray__bigint_nat__lean_mk_empty_array_with_capacity__Array_mkEmpty k _ => .new k.ctorName [.num 0]
  | .uint53__lean_mk_empty_array_with_capacity__Array_mkEmpty _ => .emptyArray
  | .typedArray__uint53__lean_mk_empty_array_with_capacity__Array_mkEmpty k _ => .new k.ctorName [.num 0]
  | .array__lean_array_mk _ => .arg 0
  | .typedArray__lean_array_mk k _ => .call (k.ctorName ++ ".from") [.arg 0]
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
  | .float__lean_float_div => .bin "/" (.arg 0) (.arg 1)
  | .float__lean_float_beq => .bin "===" (.arg 0) (.arg 1)
  | .uint32__lean_uint32_to_float => .arg 0
  | .float__lean_float_decLe__Float_decLe => .bin "<=" (.arg 0) (.arg 1)
  | .float__lean_float_decLe__Float_le => .bin "<=" (.arg 0) (.arg 1)
  | .bigint_nat__lean_uint64_to_float => .call "Number" [.arg 0]
  | .uint53__lean_uint64_to_float => .arg 0
  | .float__lean_float_decLt__Float_decLt => .bin "<" (.arg 0) (.arg 1)
  | .float__lean_float_decLt__Float_lt => .bin "<" (.arg 0) (.arg 1)
  | .float__lean_float_mul => .bin "*" (.arg 0) (.arg 1)
  | .uint16__lean_uint16_to_float => .arg 0
  | .float__lean_float_add => .bin "+" (.arg 0) (.arg 1)
  | .float__lean_float_sub => .bin "-" (.arg 0) (.arg 1)
  | .float__lean_float_negate => .un "-" (.arg 0)
  | .int32__lean_int32_to_float => .arg 0
  | .int16__lean_int16_to_float => .arg 0
  | .int8__lean_int8_to_float => .arg 0
  | .bigint_int__lean_int64_to_float => .call "Number" [.arg 0]
  | .int53__lean_int64_to_float => .arg 0
  | .float32__lean_float32_decLe__Float32_le => .bin "<=" (.arg 0) (.arg 1)
  | .float32__lean_float32_decLe__Float32_decLe => .bin "<=" (.arg 0) (.arg 1)
  | .float32__lean_float32_to_bits__Float32_toModel => .arg 0
  | .float32__lean_float32_of_bits__Float32_ofModel => .arg 0
  | .float32__lean_float32_beq => .bin "===" (.arg 0) (.arg 1)
  | .uint8__lean_uint8_to_float32 => .arg 0
  | .float32__lean_float32_to_float => .arg 0
  | .uint32__lean_uint32_to_float32 => .arg 0
  | .float32__lean_float32_negate => .un "-" (.arg 0)
  | .bigint_nat__lean_uint64_to_float32 => .call "Number" [.arg 0]
  | .uint53__lean_uint64_to_float32 => .call "Number" [.arg 0]
  | .float32__lean_float32_decLt__Float32_lt => .bin "<" (.arg 0) (.arg 1)
  | .float32__lean_float32_decLt__Float32_decLt => .bin "<" (.arg 0) (.arg 1)
  | .uint16__lean_uint16_to_float32 => .arg 0
  | .int32__lean_int32_to_float32 => .arg 0
  | .int8__lean_int8_to_float32 => .arg 0
  | .int16__lean_int16_to_float32 => .arg 0
  | .bigint_int__lean_int64_to_float32 => .call "Number" [.arg 0]
  | .int53__lean_int64_to_float32 => .call "Number" [.arg 0]

end JsOpInlined

end MoreJs

end
