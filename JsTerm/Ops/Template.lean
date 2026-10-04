module

public import JsTerm.Ops.Inlinable

@[expose] public section

set_option autoImplicit false

/-!
# The JavaScript of the operations of `JsTerm` written inline

**Generated** by `scripts/gen_js_ops.py`; do not edit.

`JsOpInlinable.template`: the JavaScript operator, conversion or literal (a `JsInline`, in
`JsTerm.Ops.Basic`) written in place of a call of each operation of `JsOpInlinable`
(`JsTerm.Ops.Inlinable`), over its arguments.
-/

namespace MoreJs

namespace JsOpInlinable

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
  | .bigint_nat__lean_nat_pow => .bin "**" (.arg 0) (.arg 1)
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
  | .bigint_int__bigint_nat__lean_int_pow => .bin "**" (.arg 0) (.arg 1)
  | .bigint_int__uint53__lean_int_pow => .bin "**" (.arg 0) (.call "BigInt" [.arg 1])
  | .bigint_nat__lean_nat_repr => .call "String" [.arg 0]
  | .uint53__lean_nat_repr => .call "String" [.arg 0]
  | .bigint_int__lean_int_repr => .call "String" [.arg 0]
  | .int53__lean_int_repr => .call "String" [.arg 0]
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
  | .uint32__lean_uint32_sub => .bin ">>>" (.bin "-" (.arg 0) (.arg 1)) (.num 0)
  | .bigint_nat__lean_uint16_to_nat__UInt16_toNat => .call "BigInt" [.arg 0]
  | .uint53__lean_uint16_to_nat__UInt16_toNat => .arg 0
  | .uint32__lean_uint32_add => .bin ">>>" (.bin "+" (.arg 0) (.arg 1)) (.num 0)
  | .bigint_nat__lean_uint8_to_uint64 => .call "BigInt" [.arg 0]
  | .uint53__lean_uint8_to_uint64 => .arg 0
  | .bigint_nat__lean_uint8_to_nat__UInt8_toNat => .call "BigInt" [.arg 0]
  | .uint53__lean_uint8_to_nat__UInt8_toNat => .arg 0
  | .uint8__lean_uint8_to_uint32 => .arg 0
  | .bigint_nat__lean_uint16_to_uint64 => .call "BigInt" [.arg 0]
  | .uint53__lean_uint16_to_uint64 => .arg 0
  | .uint8__lean_uint8_to_uint16 => .arg 0
  | .uint8__lean_uint8_sub => .bin "&" (.bin "-" (.arg 0) (.arg 1)) (.num 255)
  | .uint8__lean_uint8_neg => .bin "&" (.un "-" (.arg 0)) (.num 255)
  | .uint8__lean_uint8_lor => .bin "|" (.arg 0) (.arg 1)
  | .uint8__lean_uint8_land => .bin "&" (.arg 0) (.arg 1)
  | .uint8__lean_uint8_mul => .bin "&" (.bin "*" (.arg 0) (.arg 1)) (.num 255)
  | .uint8__lean_uint8_add => .bin "&" (.bin "+" (.arg 0) (.arg 1)) (.num 255)
  | .uint8__lean_uint8_complement => .bin "&" (.un "~" (.arg 0)) (.num 255)
  | .uint8__lean_uint8_xor => .bin "^" (.arg 0) (.arg 1)
  | .uint16__lean_uint16_neg => .bin "&" (.un "-" (.arg 0)) (.num 65535)
  | .uint16__lean_uint16_add => .bin "&" (.bin "+" (.arg 0) (.arg 1)) (.num 65535)
  | .uint16__lean_uint16_lor => .bin "|" (.arg 0) (.arg 1)
  | .uint16__lean_uint16_mul => .bin "&" (.bin "*" (.arg 0) (.arg 1)) (.num 65535)
  | .uint16__lean_uint16_land => .bin "&" (.arg 0) (.arg 1)
  | .uint16__lean_uint16_complement => .bin "&" (.un "~" (.arg 0)) (.num 65535)
  | .uint16__lean_uint16_xor => .bin "^" (.arg 0) (.arg 1)
  | .uint16__lean_uint16_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .uint16__lean_uint16_dec_le => .bin "<=" (.arg 0) (.arg 1)
  | .uint16__lean_uint16_sub => .bin "&" (.bin "-" (.arg 0) (.arg 1)) (.num 65535)
  | .uint32__lean_uint32_shift_right => .bin ">>>" (.arg 0) (.arg 1)
  | .uint32__lean_uint32_neg => .bin ">>>" (.un "-" (.arg 0)) (.num 0)
  | .uint32__lean_uint32_lor => .bin ">>>" (.bin "|" (.arg 0) (.arg 1)) (.num 0)
  | .uint32__lean_uint32_xor => .bin ">>>" (.bin "^" (.arg 0) (.arg 1)) (.num 0)
  | .uint32__lean_uint32_mul => .bin ">>>" (.call "Math.imul" [.arg 0, .arg 1]) (.num 0)
  | .uint32__lean_uint32_land => .bin ">>>" (.bin "&" (.arg 0) (.arg 1)) (.num 0)
  | .uint32__lean_uint32_complement => .bin ">>>" (.un "~" (.arg 0)) (.num 0)
  | .bigint_nat__lean_uint64_complement => .call "BigInt.asUintN" [.num 64, .un "~" (.arg 0)]
  | .bigint_nat__lean_uint64_add => .call "BigInt.asUintN" [.num 64, .bin "+" (.arg 0) (.arg 1)]
  | .bigint_nat__lean_uint64_lor => .bin "|" (.arg 0) (.arg 1)
  | .bigint_nat__lean_uint64_mul => .call "BigInt.asUintN" [.num 64, .bin "*" (.arg 0) (.arg 1)]
  | .bigint_nat__lean_uint64_land => .bin "&" (.arg 0) (.arg 1)
  | .bigint_nat__lean_uint64_dec_le => .bin "<=" (.arg 0) (.arg 1)
  | .uint53__lean_uint64_dec_le => .bin "<=" (.arg 0) (.arg 1)
  | .bigint_nat__lean_uint64_sub => .call "BigInt.asUintN" [.num 64, .bin "-" (.arg 0) (.arg 1)]
  | .bigint_nat__lean_uint64_neg => .call "BigInt.asUintN" [.num 64, .un "-" (.arg 0)]
  | .bigint_nat__lean_uint64_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .uint53__lean_uint64_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .bigint_nat__lean_uint64_xor => .bin "^" (.arg 0) (.arg 1)
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
  | .int32__lean_int32_shift_left => .bin "<<" (.arg 0) (.arg 1)
  | .int32__lean_int32_shift_right => .bin ">>" (.arg 0) (.arg 1)
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
  | .uint32__lean_uint32_to_float32 => .call "Math.fround" [.arg 0]
  | .float32__lean_float32_negate => .un "-" (.arg 0)
  | .float32__ceilf => .call "Math.ceil" [.arg 0]
  | .float32__sinf => .call "Math.fround" [.call "Math.sin" [.arg 0]]
  | .float32__asinhf => .call "Math.fround" [.call "Math.asinh" [.arg 0]]
  | .float32__log2f => .call "Math.fround" [.call "Math.log2" [.arg 0]]
  | .uint53__lean_uint64_to_float32 => .call "Math.fround" [.arg 0]
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
  | .int32__lean_int32_to_float32 => .call "Math.fround" [.arg 0]
  | .int8__lean_int8_to_float32 => .arg 0
  | .int16__lean_int16_to_float32 => .arg 0
  | .int53__lean_int64_to_float32 => .call "Math.fround" [.arg 0]

end JsOpInlinable

end MoreJs

end
