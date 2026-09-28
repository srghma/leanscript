module

public import JsTerm.Ty

@[expose] public section

set_option autoImplicit false

/-!
# The operations of `JsTerm` that call the runtime

**Generated** by `scripts/gen_js_ops.py` from the catalogue of externs
(`LeanScript/LeanInitPureExterns/*.lean`) and the exports of `runtime.js`; do not edit.

Every extern of the catalogue is split by the JavaScript representation of its arguments and
its result (`lean_nat_div : [nat, nat] → nat` is `bigint_nat__lean_nat_div : [bigint_nat,
bigint_nat] → bigint_nat` and `uint53__lean_nat_div : [uint53, uint53] → uint53`).  The
operations here are the ones implemented by a function of `runtime.js` of the **same name**,
which the generated module imports; the ones written as a JavaScript operator or conversion
are in `JsTerm.OpsInlined`.

The name of an operation is its *type prefix* and the name of the extern, joined by `__`: the
representations of the configurable Lean types of the signature (`Nat`, `Int`, `UInt64`,
`Int64`, `BitVec n` for `n > 53`) in order of first appearance and without repetitions, or,
when there is none, the first leaf of the signature (`uint32__lean_uint32_add`), or the family
of a polymorphic operation (`array__lean_array_push`, `thunk__lean_mk_thunk`).  A polymorphic
array operation works on every layout of an array (`JsArrayLayout`: a generic array or a typed
array).
-/

namespace MoreJs

/-- The operations implemented by a function of `runtime.js` of the same name, indexed by
    the types of their arguments and of their result. -/
inductive JsOpImported : List JsTy → JsTy → Type where
  /-- Array.get!InternalBorrowed -/
  | bigint_nat__lean_array_get_borrowed : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported [E, A, (.terminal .bigint_nat)] E
  /-- Array.get!InternalBorrowed -/
  | uint53__lean_array_get_borrowed : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported [E, A, (.terminal .uint53)] E
  /-- Array.push -/
  | array__lean_array_push : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported [A, E] A
  /-- Array.toList -/
  | typedArray__lean_array_to_list : (k : JsTypedArray) → (e : JsTerminalTy) → JsOpImported [(.typedArray k e)] (.list (.terminal e))
  /-- Array.get!Internal -/
  | bigint_nat__lean_array_get : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported [E, A, (.terminal .bigint_nat)] E
  /-- Array.get!Internal -/
  | uint53__lean_array_get : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported [E, A, (.terminal .uint53)] E
  /-- Thunk.pure -/
  | thunk__lean_thunk_pure : (α : JsTy) → JsOpImported [α] (.thunk α)
  /-- Thunk.mk -/
  | thunk__lean_mk_thunk : (α : JsTy) → JsOpImported [(.lazy α)] (.thunk α)
  /-- Thunk.get -/
  | thunk__lean_thunk_get_own : (α : JsTy) → JsOpImported [(.thunk α)] α
  /-- Array.set! -/
  | bigint_nat__lean_array_set : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported [A, (.terminal .bigint_nat), E] A
  /-- Array.set! -/
  | uint53__lean_array_set : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported [A, (.terminal .uint53), E] A
  /-- Array.set (decides `i < xs.size`) -/
  | bigint_nat__lean_array_fset : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported [A, (.terminal .bigint_nat), E] A
  /-- Array.set (decides `i < xs.size`) -/
  | uint53__lean_array_fset : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported [A, (.terminal .uint53), E] A
  /-- Array.swap (decides `i < xs.size`, `j < xs.size`) -/
  | bigint_nat__lean_array_fswap : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported [A, (.terminal .bigint_nat), (.terminal .bigint_nat)] A
  /-- Array.swap (decides `i < xs.size`, `j < xs.size`) -/
  | uint53__lean_array_fswap : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported [A, (.terminal .uint53), (.terminal .uint53)] A
  /-- Array.replicate -/
  | bigint_nat__lean_mk_array : (α : JsTy) → JsOpImported [(.terminal .bigint_nat), α] (.array α)
  /-- Array.replicate -/
  | typedArray__bigint_nat__lean_mk_array : (k : JsTypedArray) → (e : JsTerminalTy) → JsOpImported [(.terminal .bigint_nat), (.terminal e)] (.typedArray k e)
  /-- Array.replicate -/
  | uint53__lean_mk_array : (α : JsTy) → JsOpImported [(.terminal .uint53), α] (.array α)
  /-- Array.replicate -/
  | typedArray__uint53__lean_mk_array : (k : JsTypedArray) → (e : JsTerminalTy) → JsOpImported [(.terminal .uint53), (.terminal e)] (.typedArray k e)
  /-- Array.swapIfInBounds -/
  | bigint_nat__lean_array_swap : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported [A, (.terminal .bigint_nat), (.terminal .bigint_nat)] A
  /-- Array.swapIfInBounds -/
  | uint53__lean_array_swap : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported [A, (.terminal .uint53), (.terminal .uint53)] A
  /-- Array.pop -/
  | array__lean_array_pop : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported [A] A
  /-- (in place: `lean_array_push` on an array nothing else refers to) -/
  | array__lean_array_push_inplace : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported [A, E] A
  /-- (in place: `lean_array_set` on an array nothing else refers to) -/
  | bigint_nat__lean_array_set_inplace : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported [A, (.terminal .bigint_nat), E] A
  /-- (in place: `lean_array_set` on an array nothing else refers to) -/
  | uint53__lean_array_set_inplace : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported [A, (.terminal .uint53), E] A
  /-- (in place: `lean_array_swap` on an array nothing else refers to) -/
  | bigint_nat__lean_array_swap_inplace : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported [A, (.terminal .bigint_nat), (.terminal .bigint_nat)] A
  /-- (in place: `lean_array_swap` on an array nothing else refers to) -/
  | uint53__lean_array_swap_inplace : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported [A, (.terminal .uint53), (.terminal .uint53)] A
  /-- (in place: `lean_array_pop` on an array nothing else refers to) -/
  | array__lean_array_pop_inplace : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported [A] A
  /-- Nat.div -/
  | bigint_nat__lean_nat_div : JsOpImported [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- Nat.div -/
  | uint53__lean_nat_div : JsOpImported [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- UInt32.ofNatLT (decides `n < UInt32.size`) -/
  | bigint_nat__lean_uint32_of_nat__UInt32_ofNatLT : JsOpImported [(.terminal .bigint_nat)] (.terminal .uint32)
  /-- UInt32.ofNatLT (decides `n < UInt32.size`) -/
  | uint53__lean_uint32_of_nat__UInt32_ofNatLT : JsOpImported [(.terminal .uint53)] (.terminal .uint32)
  /-- Char.ofNatAux (decides `n.isValidChar`) -/
  | bigint_nat__lean_uint32_of_nat__Char_ofNatAux : JsOpImported [(.terminal .bigint_nat)] (.terminal .string)
  /-- Char.ofNatAux (decides `n.isValidChar`) -/
  | uint53__lean_uint32_of_nat__Char_ofNatAux : JsOpImported [(.terminal .uint53)] (.terminal .string)
  /-- Nat.modCore -/
  | bigint_nat__lean_nat_mod__Nat_modCore : JsOpImported [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- Nat.modCore -/
  | uint53__lean_nat_mod__Nat_modCore : JsOpImported [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- Nat.mod -/
  | bigint_nat__lean_nat_mod__Nat_mod : JsOpImported [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- Nat.mod -/
  | uint53__lean_nat_mod__Nat_mod : JsOpImported [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- Nat.sub -/
  | bigint_nat__lean_nat_sub : JsOpImported [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- Nat.sub -/
  | uint53__lean_nat_sub : JsOpImported [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- UInt8.ofNat -/
  | bigint_nat__lean_uint8_of_nat__UInt8_ofNat : JsOpImported [(.terminal .bigint_nat)] (.terminal .uint8)
  /-- UInt8.ofNat -/
  | uint53__lean_uint8_of_nat__UInt8_ofNat : JsOpImported [(.terminal .uint53)] (.terminal .uint8)
  /-- UInt8.ofNatLT (decides `n < UInt8.size`) -/
  | bigint_nat__lean_uint8_of_nat__UInt8_ofNatLT : JsOpImported [(.terminal .bigint_nat)] (.terminal .uint8)
  /-- UInt8.ofNatLT (decides `n < UInt8.size`) -/
  | uint53__lean_uint8_of_nat__UInt8_ofNatLT : JsOpImported [(.terminal .uint53)] (.terminal .uint8)
  /-- Nat.add -/
  | uint53__lean_nat_add : JsOpImported [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- Nat.pred -/
  | bigint_nat__lean_nat_pred : JsOpImported [(.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- Nat.pred -/
  | uint53__lean_nat_pred : JsOpImported [(.terminal .uint53)] (.terminal .uint53)
  /-- String.ofList -/
  | string__lean_string_mk__String_ofList : JsOpImported [(.list (.terminal .string))] (.terminal .string)
  /-- String.hash -/
  | bigint_nat__lean_string_hash : JsOpImported [(.terminal .string)] (.terminal .bigint_nat)
  /-- String.hash -/
  | uint53__lean_string_hash : JsOpImported [(.terminal .string)] (.terminal .uint53)
  /-- UInt64.toBitVec -/
  | bigint_nat__int53_bitvec64__lean_uint64_to_nat__UInt64_toBitVec : JsOpImported [(.terminal .bigint_nat)] (.terminal (.int53_bitvec_big 64 (by decide)))
  /-- UInt64.ofBitVec -/
  | bigint_bitvec64__uint53__lean_uint64_of_nat_mk : JsOpImported [(.terminal (.bigint_bitvec_big 64 (by decide)))] (.terminal .uint53)
  /-- UInt16.ofNatLT (decides `n < UInt16.size`) -/
  | bigint_nat__lean_uint16_of_nat__UInt16_ofNatLT : JsOpImported [(.terminal .bigint_nat)] (.terminal .uint16)
  /-- UInt16.ofNatLT (decides `n < UInt16.size`) -/
  | uint53__lean_uint16_of_nat__UInt16_ofNatLT : JsOpImported [(.terminal .uint53)] (.terminal .uint16)
  /-- Nat.pow -/
  | bigint_nat__lean_nat_pow : JsOpImported [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- Nat.pow -/
  | uint53__lean_nat_pow : JsOpImported [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- Nat.mul -/
  | uint53__lean_nat_mul : JsOpImported [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- String.utf8ByteSize -/
  | bigint_nat__lean_string_utf8_byte_size : JsOpImported [(.terminal .string)] (.terminal .bigint_nat)
  /-- String.utf8ByteSize -/
  | uint53__lean_string_utf8_byte_size : JsOpImported [(.terminal .string)] (.terminal .uint53)
  /-- UInt64.ofNatLT (decides `n < UInt64.size`) -/
  | bigint_nat__lean_uint64_of_nat__UInt64_ofNatLT : JsOpImported [(.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- UInt64.ofNatLT (decides `n < UInt64.size`) -/
  | bigint_nat__uint53__lean_uint64_of_nat__UInt64_ofNatLT : JsOpImported [(.terminal .bigint_nat)] (.terminal .uint53)
  /-- UInt64.ofNatLT (decides `n < UInt64.size`) -/
  | uint53__bigint_nat__lean_uint64_of_nat__UInt64_ofNatLT : JsOpImported [(.terminal .uint53)] (.terminal .bigint_nat)
  /-- UInt64.ofNatLT (decides `n < UInt64.size`) -/
  | uint53__lean_uint64_of_nat__UInt64_ofNatLT : JsOpImported [(.terminal .uint53)] (.terminal .uint53)
  /-- Int.ofNat -/
  | bigint_nat__int53__lean_nat_to_int : JsOpImported [(.terminal .bigint_nat)] (.terminal .int53)
  /-- Int.mul -/
  | int53__lean_int_mul : JsOpImported [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int.negSucc -/
  | bigint_nat__bigint_int__lean_int_neg_succ_of_nat : JsOpImported [(.terminal .bigint_nat)] (.terminal .bigint_int)
  /-- Int.negSucc -/
  | bigint_nat__int53__lean_int_neg_succ_of_nat : JsOpImported [(.terminal .bigint_nat)] (.terminal .int53)
  /-- Int.negSucc -/
  | uint53__bigint_int__lean_int_neg_succ_of_nat : JsOpImported [(.terminal .uint53)] (.terminal .bigint_int)
  /-- Int.negSucc -/
  | uint53__int53__lean_int_neg_succ_of_nat : JsOpImported [(.terminal .uint53)] (.terminal .int53)
  /-- Int.add -/
  | int53__lean_int_add : JsOpImported [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int.neg -/
  | int53__lean_int_neg : JsOpImported [(.terminal .int53)] (.terminal .int53)
  /-- Int.sub -/
  | int53__lean_int_sub : JsOpImported [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int.natAbs -/
  | bigint_int__bigint_nat__lean_nat_abs : JsOpImported [(.terminal .bigint_int)] (.terminal .bigint_nat)
  /-- Int.natAbs -/
  | bigint_int__uint53__lean_nat_abs : JsOpImported [(.terminal .bigint_int)] (.terminal .uint53)
  /-- Int.natAbs -/
  | int53__bigint_nat__lean_nat_abs : JsOpImported [(.terminal .int53)] (.terminal .bigint_nat)
  /-- Int.natAbs -/
  | int53__uint53__lean_nat_abs : JsOpImported [(.terminal .int53)] (.terminal .uint53)
  /-- Nat.divExact (decides `y ∣ x`) -/
  | bigint_nat__lean_nat_div_exact : JsOpImported [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- Nat.divExact (decides `y ∣ x`) -/
  | uint53__lean_nat_div_exact : JsOpImported [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- Nat.xor -/
  | uint53__lean_nat_lxor : JsOpImported [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- Nat.shiftLeft -/
  | uint53__lean_nat_shiftl : JsOpImported [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- Nat.shiftRight -/
  | uint53__lean_nat_shiftr : JsOpImported [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- Nat.land -/
  | uint53__lean_nat_land : JsOpImported [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- Nat.lor -/
  | uint53__lean_nat_lor : JsOpImported [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- Nat.log2 -/
  | bigint_nat__lean_nat_log2 : JsOpImported [(.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- Nat.log2 -/
  | uint53__lean_nat_log2 : JsOpImported [(.terminal .uint53)] (.terminal .uint53)
  /-- Int.emod -/
  | bigint_int__lean_int_emod : JsOpImported [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int.emod -/
  | int53__lean_int_emod : JsOpImported [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int.divExact (decides `y ∣ x`) -/
  | bigint_int__lean_int_div_exact : JsOpImported [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int.divExact (decides `y ∣ x`) -/
  | int53__lean_int_div_exact : JsOpImported [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int.tmod -/
  | bigint_int__lean_int_mod : JsOpImported [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int.tmod -/
  | int53__lean_int_mod : JsOpImported [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int.ediv -/
  | bigint_int__lean_int_ediv : JsOpImported [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int.ediv -/
  | int53__lean_int_ediv : JsOpImported [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int.tdiv -/
  | bigint_int__lean_int_div : JsOpImported [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int.tdiv -/
  | int53__lean_int_div : JsOpImported [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- UInt64.toNat -/
  | bigint_nat__uint53__lean_uint64_to_nat__UInt64_toNat : JsOpImported [(.terminal .bigint_nat)] (.terminal .uint53)
  /-- UInt32.toUInt8 -/
  | uint32__lean_uint32_to_uint8 : JsOpImported [(.terminal .uint32)] (.terminal .uint8)
  /-- UInt64.toUInt32 -/
  | bigint_nat__lean_uint64_to_uint32 : JsOpImported [(.terminal .bigint_nat)] (.terminal .uint32)
  /-- UInt64.toUInt32 -/
  | uint53__lean_uint64_to_uint32 : JsOpImported [(.terminal .uint53)] (.terminal .uint32)
  /-- UInt32.toUInt16 -/
  | uint32__lean_uint32_to_uint16 : JsOpImported [(.terminal .uint32)] (.terminal .uint16)
  /-- UInt32.ofNat -/
  | bigint_nat__lean_uint32_of_nat__UInt32_ofNat : JsOpImported [(.terminal .bigint_nat)] (.terminal .uint32)
  /-- UInt32.ofNat -/
  | uint53__lean_uint32_of_nat__UInt32_ofNat : JsOpImported [(.terminal .uint53)] (.terminal .uint32)
  /-- UInt32.sub -/
  | uint32__lean_uint32_sub : JsOpImported [(.terminal .uint32), (.terminal .uint32)] (.terminal .uint32)
  /-- UInt16.toUInt8 -/
  | uint16__lean_uint16_to_uint8 : JsOpImported [(.terminal .uint16)] (.terminal .uint8)
  /-- UInt32.add -/
  | uint32__lean_uint32_add : JsOpImported [(.terminal .uint32), (.terminal .uint32)] (.terminal .uint32)
  /-- UInt64.ofNat -/
  | bigint_nat__lean_uint64_of_nat__UInt64_ofNat : JsOpImported [(.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- UInt64.ofNat -/
  | bigint_nat__uint53__lean_uint64_of_nat__UInt64_ofNat : JsOpImported [(.terminal .bigint_nat)] (.terminal .uint53)
  /-- UInt64.ofNat -/
  | uint53__bigint_nat__lean_uint64_of_nat__UInt64_ofNat : JsOpImported [(.terminal .uint53)] (.terminal .bigint_nat)
  /-- UInt64.ofNat -/
  | uint53__lean_uint64_of_nat__UInt64_ofNat : JsOpImported [(.terminal .uint53)] (.terminal .uint53)
  /-- UInt16.ofNat -/
  | bigint_nat__lean_uint16_of_nat__UInt16_ofNat : JsOpImported [(.terminal .bigint_nat)] (.terminal .uint16)
  /-- UInt16.ofNat -/
  | uint53__lean_uint16_of_nat__UInt16_ofNat : JsOpImported [(.terminal .uint53)] (.terminal .uint16)
  /-- UInt64.toUInt8 -/
  | bigint_nat__lean_uint64_to_uint8 : JsOpImported [(.terminal .bigint_nat)] (.terminal .uint8)
  /-- UInt64.toUInt8 -/
  | uint53__lean_uint64_to_uint8 : JsOpImported [(.terminal .uint53)] (.terminal .uint8)
  /-- UInt64.toUInt16 -/
  | bigint_nat__lean_uint64_to_uint16 : JsOpImported [(.terminal .bigint_nat)] (.terminal .uint16)
  /-- UInt64.toUInt16 -/
  | uint53__lean_uint64_to_uint16 : JsOpImported [(.terminal .uint53)] (.terminal .uint16)
  /-- UInt8.sub -/
  | uint8__lean_uint8_sub : JsOpImported [(.terminal .uint8), (.terminal .uint8)] (.terminal .uint8)
  /-- UInt8.neg -/
  | uint8__lean_uint8_neg : JsOpImported [(.terminal .uint8)] (.terminal .uint8)
  /-- UInt8.lor -/
  | uint8__lean_uint8_lor : JsOpImported [(.terminal .uint8), (.terminal .uint8)] (.terminal .uint8)
  /-- UInt8.div -/
  | uint8__lean_uint8_div : JsOpImported [(.terminal .uint8), (.terminal .uint8)] (.terminal .uint8)
  /-- UInt8.shiftRight -/
  | uint8__lean_uint8_shift_right : JsOpImported [(.terminal .uint8), (.terminal .uint8)] (.terminal .uint8)
  /-- UInt8.shiftLeft -/
  | uint8__lean_uint8_shift_left : JsOpImported [(.terminal .uint8), (.terminal .uint8)] (.terminal .uint8)
  /-- UInt8.land -/
  | uint8__lean_uint8_land : JsOpImported [(.terminal .uint8), (.terminal .uint8)] (.terminal .uint8)
  /-- UInt8.mul -/
  | uint8__lean_uint8_mul : JsOpImported [(.terminal .uint8), (.terminal .uint8)] (.terminal .uint8)
  /-- UInt8.add -/
  | uint8__lean_uint8_add : JsOpImported [(.terminal .uint8), (.terminal .uint8)] (.terminal .uint8)
  /-- UInt8.complement -/
  | uint8__lean_uint8_complement : JsOpImported [(.terminal .uint8)] (.terminal .uint8)
  /-- UInt8.mod -/
  | uint8__lean_uint8_mod : JsOpImported [(.terminal .uint8), (.terminal .uint8)] (.terminal .uint8)
  /-- Bool.toUInt8 -/
  | bool__lean_bool_to_uint8 : JsOpImported [(.terminal .bool)] (.terminal .uint8)
  /-- UInt8.xor -/
  | uint8__lean_uint8_xor : JsOpImported [(.terminal .uint8), (.terminal .uint8)] (.terminal .uint8)
  /-- UInt16.neg -/
  | uint16__lean_uint16_neg : JsOpImported [(.terminal .uint16)] (.terminal .uint16)
  /-- UInt16.add -/
  | uint16__lean_uint16_add : JsOpImported [(.terminal .uint16), (.terminal .uint16)] (.terminal .uint16)
  /-- UInt16.lor -/
  | uint16__lean_uint16_lor : JsOpImported [(.terminal .uint16), (.terminal .uint16)] (.terminal .uint16)
  /-- UInt16.mul -/
  | uint16__lean_uint16_mul : JsOpImported [(.terminal .uint16), (.terminal .uint16)] (.terminal .uint16)
  /-- UInt16.land -/
  | uint16__lean_uint16_land : JsOpImported [(.terminal .uint16), (.terminal .uint16)] (.terminal .uint16)
  /-- UInt16.complement -/
  | uint16__lean_uint16_complement : JsOpImported [(.terminal .uint16)] (.terminal .uint16)
  /-- UInt16.xor -/
  | uint16__lean_uint16_xor : JsOpImported [(.terminal .uint16), (.terminal .uint16)] (.terminal .uint16)
  /-- UInt16.shiftLeft -/
  | uint16__lean_uint16_shift_left : JsOpImported [(.terminal .uint16), (.terminal .uint16)] (.terminal .uint16)
  /-- UInt16.mod -/
  | uint16__lean_uint16_mod : JsOpImported [(.terminal .uint16), (.terminal .uint16)] (.terminal .uint16)
  /-- UInt16.div -/
  | uint16__lean_uint16_div : JsOpImported [(.terminal .uint16), (.terminal .uint16)] (.terminal .uint16)
  /-- UInt16.sub -/
  | uint16__lean_uint16_sub : JsOpImported [(.terminal .uint16), (.terminal .uint16)] (.terminal .uint16)
  /-- Bool.toUInt16 -/
  | bool__lean_bool_to_uint16 : JsOpImported [(.terminal .bool)] (.terminal .uint16)
  /-- UInt16.shiftRight -/
  | uint16__lean_uint16_shift_right : JsOpImported [(.terminal .uint16), (.terminal .uint16)] (.terminal .uint16)
  /-- UInt32.mod -/
  | uint32__lean_uint32_mod : JsOpImported [(.terminal .uint32), (.terminal .uint32)] (.terminal .uint32)
  /-- Bool.toUInt32 -/
  | bool__lean_bool_to_uint32 : JsOpImported [(.terminal .bool)] (.terminal .uint32)
  /-- UInt32.div -/
  | uint32__lean_uint32_div : JsOpImported [(.terminal .uint32), (.terminal .uint32)] (.terminal .uint32)
  /-- UInt32.shiftRight -/
  | uint32__lean_uint32_shift_right : JsOpImported [(.terminal .uint32), (.terminal .uint32)] (.terminal .uint32)
  /-- UInt32.neg -/
  | uint32__lean_uint32_neg : JsOpImported [(.terminal .uint32)] (.terminal .uint32)
  /-- UInt32.lor -/
  | uint32__lean_uint32_lor : JsOpImported [(.terminal .uint32), (.terminal .uint32)] (.terminal .uint32)
  /-- UInt32.xor -/
  | uint32__lean_uint32_xor : JsOpImported [(.terminal .uint32), (.terminal .uint32)] (.terminal .uint32)
  /-- UInt32.shiftLeft -/
  | uint32__lean_uint32_shift_left : JsOpImported [(.terminal .uint32), (.terminal .uint32)] (.terminal .uint32)
  /-- UInt32.mul -/
  | uint32__lean_uint32_mul : JsOpImported [(.terminal .uint32), (.terminal .uint32)] (.terminal .uint32)
  /-- UInt32.land -/
  | uint32__lean_uint32_land : JsOpImported [(.terminal .uint32), (.terminal .uint32)] (.terminal .uint32)
  /-- UInt32.complement -/
  | uint32__lean_uint32_complement : JsOpImported [(.terminal .uint32)] (.terminal .uint32)
  /-- UInt64.shiftLeft -/
  | bigint_nat__lean_uint64_shift_left : JsOpImported [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- UInt64.shiftLeft -/
  | uint53__lean_uint64_shift_left : JsOpImported [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- UInt64.shiftRight -/
  | bigint_nat__lean_uint64_shift_right : JsOpImported [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- UInt64.shiftRight -/
  | uint53__lean_uint64_shift_right : JsOpImported [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- UInt64.complement -/
  | bigint_nat__lean_uint64_complement : JsOpImported [(.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- UInt64.complement -/
  | uint53__lean_uint64_complement : JsOpImported [(.terminal .uint53)] (.terminal .uint53)
  /-- UInt64.add -/
  | bigint_nat__lean_uint64_add : JsOpImported [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- UInt64.add -/
  | uint53__lean_uint64_add : JsOpImported [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- UInt64.lor -/
  | bigint_nat__lean_uint64_lor : JsOpImported [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- UInt64.lor -/
  | uint53__lean_uint64_lor : JsOpImported [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- UInt64.mod -/
  | bigint_nat__lean_uint64_mod : JsOpImported [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- UInt64.mod -/
  | uint53__lean_uint64_mod : JsOpImported [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- UInt64.div -/
  | bigint_nat__lean_uint64_div : JsOpImported [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- UInt64.div -/
  | uint53__lean_uint64_div : JsOpImported [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- UInt64.mul -/
  | bigint_nat__lean_uint64_mul : JsOpImported [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- UInt64.mul -/
  | uint53__lean_uint64_mul : JsOpImported [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- UInt64.land -/
  | bigint_nat__lean_uint64_land : JsOpImported [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- UInt64.land -/
  | uint53__lean_uint64_land : JsOpImported [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- Bool.toUInt64 -/
  | bigint_nat__lean_bool_to_uint64 : JsOpImported [(.terminal .bool)] (.terminal .bigint_nat)
  /-- Bool.toUInt64 -/
  | uint53__lean_bool_to_uint64 : JsOpImported [(.terminal .bool)] (.terminal .uint53)
  /-- UInt64.sub -/
  | bigint_nat__lean_uint64_sub : JsOpImported [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- UInt64.sub -/
  | uint53__lean_uint64_sub : JsOpImported [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- UInt64.neg -/
  | bigint_nat__lean_uint64_neg : JsOpImported [(.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- UInt64.neg -/
  | uint53__lean_uint64_neg : JsOpImported [(.terminal .uint53)] (.terminal .uint53)
  /-- UInt64.xor -/
  | bigint_nat__lean_uint64_xor : JsOpImported [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- UInt64.xor -/
  | uint53__lean_uint64_xor : JsOpImported [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- Int8.add -/
  | int8__lean_int8_add : JsOpImported [(.terminal .int8), (.terminal .int8)] (.terminal .int8)
  /-- Int8.div -/
  | int8__lean_int8_div : JsOpImported [(.terminal .int8), (.terminal .int8)] (.terminal .int8)
  /-- Int8.shiftRight -/
  | int8__lean_int8_shift_right : JsOpImported [(.terminal .int8), (.terminal .int8)] (.terminal .int8)
  /-- Int8.mod -/
  | int8__lean_int8_mod : JsOpImported [(.terminal .int8), (.terminal .int8)] (.terminal .int8)
  /-- Bool.toInt8 -/
  | bool__lean_bool_to_int8 : JsOpImported [(.terminal .bool)] (.terminal .int8)
  /-- Int8.shiftLeft -/
  | int8__lean_int8_shift_left : JsOpImported [(.terminal .int8), (.terminal .int8)] (.terminal .int8)
  /-- Int8.xor -/
  | int8__lean_int8_xor : JsOpImported [(.terminal .int8), (.terminal .int8)] (.terminal .int8)
  /-- Int8.complement -/
  | int8__lean_int8_complement : JsOpImported [(.terminal .int8)] (.terminal .int8)
  /-- Int8.neg -/
  | int8__lean_int8_neg : JsOpImported [(.terminal .int8)] (.terminal .int8)
  /-- Int8.abs -/
  | int8__lean_int8_abs : JsOpImported [(.terminal .int8)] (.terminal .int8)
  /-- Int8.sub -/
  | int8__lean_int8_sub : JsOpImported [(.terminal .int8), (.terminal .int8)] (.terminal .int8)
  /-- Int8.ofNat -/
  | bigint_nat__lean_int8_of_nat : JsOpImported [(.terminal .bigint_nat)] (.terminal .int8)
  /-- Int8.ofNat -/
  | uint53__lean_int8_of_nat : JsOpImported [(.terminal .uint53)] (.terminal .int8)
  /-- Int8.mul -/
  | int8__lean_int8_mul : JsOpImported [(.terminal .int8), (.terminal .int8)] (.terminal .int8)
  /-- Int8.land -/
  | int8__lean_int8_land : JsOpImported [(.terminal .int8), (.terminal .int8)] (.terminal .int8)
  /-- Int8.ofInt -/
  | bigint_int__lean_int8_of_int : JsOpImported [(.terminal .bigint_int)] (.terminal .int8)
  /-- Int8.ofInt -/
  | int53__lean_int8_of_int : JsOpImported [(.terminal .int53)] (.terminal .int8)
  /-- Int8.lor -/
  | int8__lean_int8_lor : JsOpImported [(.terminal .int8), (.terminal .int8)] (.terminal .int8)
  /-- Int16.ofNat -/
  | bigint_nat__lean_int16_of_nat : JsOpImported [(.terminal .bigint_nat)] (.terminal .int16)
  /-- Int16.ofNat -/
  | uint53__lean_int16_of_nat : JsOpImported [(.terminal .uint53)] (.terminal .int16)
  /-- Int16.shiftRight -/
  | int16__lean_int16_shift_right : JsOpImported [(.terminal .int16), (.terminal .int16)] (.terminal .int16)
  /-- Int16.div -/
  | int16__lean_int16_div : JsOpImported [(.terminal .int16), (.terminal .int16)] (.terminal .int16)
  /-- Int16.mod -/
  | int16__lean_int16_mod : JsOpImported [(.terminal .int16), (.terminal .int16)] (.terminal .int16)
  /-- Bool.toInt16 -/
  | bool__lean_bool_to_int16 : JsOpImported [(.terminal .bool)] (.terminal .int16)
  /-- Int16.abs -/
  | int16__lean_int16_abs : JsOpImported [(.terminal .int16)] (.terminal .int16)
  /-- Int16.complement -/
  | int16__lean_int16_complement : JsOpImported [(.terminal .int16)] (.terminal .int16)
  /-- Int16.land -/
  | int16__lean_int16_land : JsOpImported [(.terminal .int16), (.terminal .int16)] (.terminal .int16)
  /-- Int16.ofInt -/
  | bigint_int__lean_int16_of_int : JsOpImported [(.terminal .bigint_int)] (.terminal .int16)
  /-- Int16.ofInt -/
  | int53__lean_int16_of_int : JsOpImported [(.terminal .int53)] (.terminal .int16)
  /-- Int16.mul -/
  | int16__lean_int16_mul : JsOpImported [(.terminal .int16), (.terminal .int16)] (.terminal .int16)
  /-- Int16.shiftLeft -/
  | int16__lean_int16_shift_left : JsOpImported [(.terminal .int16), (.terminal .int16)] (.terminal .int16)
  /-- Int16.xor -/
  | int16__lean_int16_xor : JsOpImported [(.terminal .int16), (.terminal .int16)] (.terminal .int16)
  /-- Int16.lor -/
  | int16__lean_int16_lor : JsOpImported [(.terminal .int16), (.terminal .int16)] (.terminal .int16)
  /-- Int16.add -/
  | int16__lean_int16_add : JsOpImported [(.terminal .int16), (.terminal .int16)] (.terminal .int16)
  /-- Int16.toInt8 -/
  | int16__lean_int16_to_int8 : JsOpImported [(.terminal .int16)] (.terminal .int8)
  /-- Int16.neg -/
  | int16__lean_int16_neg : JsOpImported [(.terminal .int16)] (.terminal .int16)
  /-- Int16.sub -/
  | int16__lean_int16_sub : JsOpImported [(.terminal .int16), (.terminal .int16)] (.terminal .int16)
  /-- Int32.ofInt -/
  | bigint_int__lean_int32_of_int : JsOpImported [(.terminal .bigint_int)] (.terminal .int32)
  /-- Int32.ofInt -/
  | int53__lean_int32_of_int : JsOpImported [(.terminal .int53)] (.terminal .int32)
  /-- Int32.land -/
  | int32__lean_int32_land : JsOpImported [(.terminal .int32), (.terminal .int32)] (.terminal .int32)
  /-- Int32.mul -/
  | int32__lean_int32_mul : JsOpImported [(.terminal .int32), (.terminal .int32)] (.terminal .int32)
  /-- Int32.ofNat -/
  | bigint_nat__lean_int32_of_nat : JsOpImported [(.terminal .bigint_nat)] (.terminal .int32)
  /-- Int32.ofNat -/
  | uint53__lean_int32_of_nat : JsOpImported [(.terminal .uint53)] (.terminal .int32)
  /-- Int32.sub -/
  | int32__lean_int32_sub : JsOpImported [(.terminal .int32), (.terminal .int32)] (.terminal .int32)
  /-- Int32.neg -/
  | int32__lean_int32_neg : JsOpImported [(.terminal .int32)] (.terminal .int32)
  /-- Int32.abs -/
  | int32__lean_int32_abs : JsOpImported [(.terminal .int32)] (.terminal .int32)
  /-- Int32.xor -/
  | int32__lean_int32_xor : JsOpImported [(.terminal .int32), (.terminal .int32)] (.terminal .int32)
  /-- Int32.shiftLeft -/
  | int32__lean_int32_shift_left : JsOpImported [(.terminal .int32), (.terminal .int32)] (.terminal .int32)
  /-- Int32.shiftRight -/
  | int32__lean_int32_shift_right : JsOpImported [(.terminal .int32), (.terminal .int32)] (.terminal .int32)
  /-- Int32.complement -/
  | int32__lean_int32_complement : JsOpImported [(.terminal .int32)] (.terminal .int32)
  /-- Bool.toInt32 -/
  | bool__lean_bool_to_int32 : JsOpImported [(.terminal .bool)] (.terminal .int32)
  /-- Int32.toInt8 -/
  | int32__lean_int32_to_int8 : JsOpImported [(.terminal .int32)] (.terminal .int8)
  /-- Int32.add -/
  | int32__lean_int32_add : JsOpImported [(.terminal .int32), (.terminal .int32)] (.terminal .int32)
  /-- Int32.lor -/
  | int32__lean_int32_lor : JsOpImported [(.terminal .int32), (.terminal .int32)] (.terminal .int32)
  /-- Int32.mod -/
  | int32__lean_int32_mod : JsOpImported [(.terminal .int32), (.terminal .int32)] (.terminal .int32)
  /-- Int32.toInt16 -/
  | int32__lean_int32_to_int16 : JsOpImported [(.terminal .int32)] (.terminal .int16)
  /-- Int32.div -/
  | int32__lean_int32_div : JsOpImported [(.terminal .int32), (.terminal .int32)] (.terminal .int32)
  /-- Int64.sub -/
  | bigint_int__lean_int64_sub : JsOpImported [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int64.sub -/
  | int53__lean_int64_sub : JsOpImported [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int64.xor -/
  | bigint_int__lean_int64_xor : JsOpImported [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int64.xor -/
  | int53__lean_int64_xor : JsOpImported [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int64.toInt8 -/
  | bigint_int__lean_int64_to_int8 : JsOpImported [(.terminal .bigint_int)] (.terminal .int8)
  /-- Int64.toInt8 -/
  | int53__lean_int64_to_int8 : JsOpImported [(.terminal .int53)] (.terminal .int8)
  /-- Int64.mul -/
  | bigint_int__lean_int64_mul : JsOpImported [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int64.mul -/
  | int53__lean_int64_mul : JsOpImported [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int64.ofInt -/
  | bigint_int__lean_int64_of_int : JsOpImported [(.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int64.ofInt -/
  | bigint_int__int53__lean_int64_of_int : JsOpImported [(.terminal .bigint_int)] (.terminal .int53)
  /-- Int64.ofInt -/
  | int53__bigint_int__lean_int64_of_int : JsOpImported [(.terminal .int53)] (.terminal .bigint_int)
  /-- Int64.ofInt -/
  | int53__lean_int64_of_int : JsOpImported [(.terminal .int53)] (.terminal .int53)
  /-- Int64.land -/
  | bigint_int__lean_int64_land : JsOpImported [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int64.land -/
  | int53__lean_int64_land : JsOpImported [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int64.lor -/
  | bigint_int__lean_int64_lor : JsOpImported [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int64.lor -/
  | int53__lean_int64_lor : JsOpImported [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int64.mod -/
  | bigint_int__lean_int64_mod : JsOpImported [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int64.mod -/
  | int53__lean_int64_mod : JsOpImported [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int64.shiftLeft -/
  | bigint_int__lean_int64_shift_left : JsOpImported [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int64.shiftLeft -/
  | int53__lean_int64_shift_left : JsOpImported [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int64.complement -/
  | bigint_int__lean_int64_complement : JsOpImported [(.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int64.complement -/
  | int53__lean_int64_complement : JsOpImported [(.terminal .int53)] (.terminal .int53)
  /-- Int64.toInt32 -/
  | bigint_int__lean_int64_to_int32 : JsOpImported [(.terminal .bigint_int)] (.terminal .int32)
  /-- Int64.toInt32 -/
  | int53__lean_int64_to_int32 : JsOpImported [(.terminal .int53)] (.terminal .int32)
  /-- Int64.abs -/
  | bigint_int__lean_int64_abs : JsOpImported [(.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int64.abs -/
  | int53__lean_int64_abs : JsOpImported [(.terminal .int53)] (.terminal .int53)
  /-- Bool.toInt64 -/
  | bigint_int__lean_bool_to_int64 : JsOpImported [(.terminal .bool)] (.terminal .bigint_int)
  /-- Bool.toInt64 -/
  | int53__lean_bool_to_int64 : JsOpImported [(.terminal .bool)] (.terminal .int53)
  /-- Int64.ofNat -/
  | bigint_nat__bigint_int__lean_int64_of_nat : JsOpImported [(.terminal .bigint_nat)] (.terminal .bigint_int)
  /-- Int64.ofNat -/
  | bigint_nat__int53__lean_int64_of_nat : JsOpImported [(.terminal .bigint_nat)] (.terminal .int53)
  /-- Int64.ofNat -/
  | uint53__bigint_int__lean_int64_of_nat : JsOpImported [(.terminal .uint53)] (.terminal .bigint_int)
  /-- Int64.ofNat -/
  | uint53__int53__lean_int64_of_nat : JsOpImported [(.terminal .uint53)] (.terminal .int53)
  /-- Int64.toInt -/
  | bigint_int__int53__lean_int64_to_int_sint : JsOpImported [(.terminal .bigint_int)] (.terminal .int53)
  /-- Int64.neg -/
  | bigint_int__lean_int64_neg : JsOpImported [(.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int64.neg -/
  | int53__lean_int64_neg : JsOpImported [(.terminal .int53)] (.terminal .int53)
  /-- Int64.add -/
  | bigint_int__lean_int64_add : JsOpImported [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int64.add -/
  | int53__lean_int64_add : JsOpImported [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int64.div -/
  | bigint_int__lean_int64_div : JsOpImported [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int64.div -/
  | int53__lean_int64_div : JsOpImported [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int64.toInt16 -/
  | bigint_int__lean_int64_to_int16 : JsOpImported [(.terminal .bigint_int)] (.terminal .int16)
  /-- Int64.toInt16 -/
  | int53__lean_int64_to_int16 : JsOpImported [(.terminal .int53)] (.terminal .int16)
  /-- Int64.shiftRight -/
  | bigint_int__lean_int64_shift_right : JsOpImported [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int64.shiftRight -/
  | int53__lean_int64_shift_right : JsOpImported [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- UInt16.log2 -/
  | uint16__lean_uint16_log2 : JsOpImported [(.terminal .uint16)] (.terminal .uint16)
  /-- UInt64.log2 -/
  | bigint_nat__lean_uint64_log2 : JsOpImported [(.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- UInt64.log2 -/
  | uint53__lean_uint64_log2 : JsOpImported [(.terminal .uint53)] (.terminal .uint53)
  /-- UInt8.log2 -/
  | uint8__lean_uint8_log2 : JsOpImported [(.terminal .uint8)] (.terminal .uint8)
  /-- UInt32.log2 -/
  | uint32__lean_uint32_log2 : JsOpImported [(.terminal .uint32)] (.terminal .uint32)
  /-- String.Internal.get -/
  | string__lean_string_utf8_get__String_Internal_get : JsOpImported [(.terminal .string), (.terminal .uint53)] (.terminal .string)
  /-- String.Internal.isEmpty -/
  | string__lean_string_isempty : JsOpImported [(.terminal .string)] (.terminal .bool)
  /-- String.Internal.length -/
  | bigint_nat__lean_string_length__String_Internal_length : JsOpImported [(.terminal .string)] (.terminal .bigint_nat)
  /-- String.Internal.length -/
  | uint53__lean_string_length__String_Internal_length : JsOpImported [(.terminal .string)] (.terminal .uint53)
  /-- String.Internal.atEnd -/
  | string__lean_string_utf8_at_end__String_Internal_atEnd : JsOpImported [(.terminal .string), (.terminal .uint53)] (.terminal .bool)
  /-- String.Internal.next -/
  | string__lean_string_utf8_next__String_Internal_next : JsOpImported [(.terminal .string), (.terminal .uint53)] (.terminal .uint53)
  /-- String.mk -/
  | string__lean_string_mk__String_mk : JsOpImported [(.list (.terminal .string))] (.terminal .string)
  /-- String.Internal.pushn -/
  | bigint_nat__lean_string_pushn : JsOpImported [(.terminal .string), (.terminal .string), (.terminal .bigint_nat)] (.terminal .string)
  /-- String.Internal.pushn -/
  | uint53__lean_string_pushn : JsOpImported [(.terminal .string), (.terminal .string), (.terminal .uint53)] (.terminal .string)
  /-- String.Internal.extract -/
  | string__lean_string_utf8_extract__String_Internal_extract : JsOpImported [(.terminal .string), (.terminal .uint53), (.terminal .uint53)] (.terminal .string)
  /-- String.next -/
  | string__lean_string_utf8_next__String_next : JsOpImported [(.terminal .string), (.terminal .uint53)] (.terminal .uint53)
  /-- String.Pos.Raw.next -/
  | string__lean_string_utf8_next__String_Pos_Raw_next : JsOpImported [(.terminal .string), (.terminal .uint53)] (.terminal .uint53)
  /-- String.Pos.Raw.get -/
  | string__lean_string_utf8_get__String_Pos_Raw_get : JsOpImported [(.terminal .string), (.terminal .uint53)] (.terminal .string)
  /-- String.get -/
  | string__lean_string_utf8_get__String_get : JsOpImported [(.terminal .string), (.terminal .uint53)] (.terminal .string)
  /-- String.data -/
  | string__lean_string_data__String_data : JsOpImported [(.terminal .string)] (.list (.terminal .string))
  /-- String.toList -/
  | string__lean_string_data__String_toList : JsOpImported [(.terminal .string)] (.list (.terminal .string))
  /-- String.atEnd -/
  | string__lean_string_utf8_at_end__String_atEnd : JsOpImported [(.terminal .string), (.terminal .uint53)] (.terminal .bool)
  /-- String.Pos.Raw.atEnd -/
  | string__lean_string_utf8_at_end__String_Pos_Raw_atEnd : JsOpImported [(.terminal .string), (.terminal .uint53)] (.terminal .bool)
  /-- String.Pos.Raw.extract -/
  | string__lean_string_utf8_extract__String_Pos_Raw_extract : JsOpImported [(.terminal .string), (.terminal .uint53), (.terminal .uint53)] (.terminal .string)
  /-- String.length -/
  | bigint_nat__lean_string_length__String_length : JsOpImported [(.terminal .string)] (.terminal .bigint_nat)
  /-- String.length -/
  | uint53__lean_string_length__String_length : JsOpImported [(.terminal .string)] (.terminal .uint53)
  /-- String.Slice.Pattern.Internal.memcmpStr (decides `len.offsetBy lstart ≤ lhs.rawEndPos`, `len.offsetBy rstart ≤ rhs.rawEndPos`) -/
  | string__lean_string_memcmp : JsOpImported [(.terminal .string), (.terminal .string), (.terminal .uint53), (.terminal .uint53), (.terminal .uint53)] (.terminal .bool)
  /-- String.Pos.Raw.set -/
  | string__lean_string_utf8_set__String_Pos_Raw_set : JsOpImported [(.terminal .string), (.terminal .uint53), (.terminal .string)] (.terminal .string)
  /-- String.Pos.set (decides `p ≠ s.endPos`) -/
  | uint53__lean_string_utf8_set__String_Pos_set : JsOpImported [(.terminal .uint53), (.terminal .string)] (.terminal .string)
  /-- String.set -/
  | string__lean_string_utf8_set__String_set : JsOpImported [(.terminal .string), (.terminal .uint53), (.terminal .string)] (.terminal .string)
  /-- String.compare -/
  | string__lean_string_compare : JsOpImported [(.terminal .string), (.terminal .string)] (.enum 3 (-1))
  /-- Float.isNaN -/
  | float__lean_float_isnan : JsOpImported [(.terminal .float)] (.terminal .bool)
  /-- Float.isFinite -/
  | float__lean_float_isfinite : JsOpImported [(.terminal .float)] (.terminal .bool)
  /-- Float.isInf -/
  | float__lean_float_isinf : JsOpImported [(.terminal .float)] (.terminal .bool)
  /-- Float32.div -/
  | float32__lean_float32_div : JsOpImported [(.terminal .float32), (.terminal .float32)] (.terminal .float32)
  /-- Float.toFloat32 -/
  | float__lean_float_to_float32 : JsOpImported [(.terminal .float)] (.terminal .float32)
  /-- Float32.sub -/
  | float32__lean_float32_sub : JsOpImported [(.terminal .float32), (.terminal .float32)] (.terminal .float32)
  /-- Float32.isNaN -/
  | float32__lean_float32_isnan : JsOpImported [(.terminal .float32)] (.terminal .bool)
  /-- Float32.isInf -/
  | float32__lean_float32_isinf : JsOpImported [(.terminal .float32)] (.terminal .bool)
  /-- Float32.isFinite -/
  | float32__lean_float32_isfinite : JsOpImported [(.terminal .float32)] (.terminal .bool)
  /-- Float32.add -/
  | float32__lean_float32_add : JsOpImported [(.terminal .float32), (.terminal .float32)] (.terminal .float32)
  /-- Float32.mul -/
  | float32__lean_float32_mul : JsOpImported [(.terminal .float32), (.terminal .float32)] (.terminal .float32)

namespace JsOpImported

/-- The name of the operation: the name of its function in `runtime.js`. -/
def name {σs : List JsTy} {τ : JsTy} : JsOpImported σs τ → String
  | .bigint_nat__lean_array_get_borrowed _ => "bigint_nat__lean_array_get_borrowed"
  | .uint53__lean_array_get_borrowed _ => "uint53__lean_array_get_borrowed"
  | .array__lean_array_push _ => "array__lean_array_push"
  | .typedArray__lean_array_to_list _ _ => "typedArray__lean_array_to_list"
  | .bigint_nat__lean_array_get _ => "bigint_nat__lean_array_get"
  | .uint53__lean_array_get _ => "uint53__lean_array_get"
  | .thunk__lean_thunk_pure _ => "thunk__lean_thunk_pure"
  | .thunk__lean_mk_thunk _ => "thunk__lean_mk_thunk"
  | .thunk__lean_thunk_get_own _ => "thunk__lean_thunk_get_own"
  | .bigint_nat__lean_array_set _ => "bigint_nat__lean_array_set"
  | .uint53__lean_array_set _ => "uint53__lean_array_set"
  | .bigint_nat__lean_array_fset _ => "bigint_nat__lean_array_fset"
  | .uint53__lean_array_fset _ => "uint53__lean_array_fset"
  | .bigint_nat__lean_array_fswap _ => "bigint_nat__lean_array_fswap"
  | .uint53__lean_array_fswap _ => "uint53__lean_array_fswap"
  | .bigint_nat__lean_mk_array _ => "bigint_nat__lean_mk_array"
  | .typedArray__bigint_nat__lean_mk_array _ _ => "typedArray__bigint_nat__lean_mk_array"
  | .uint53__lean_mk_array _ => "uint53__lean_mk_array"
  | .typedArray__uint53__lean_mk_array _ _ => "typedArray__uint53__lean_mk_array"
  | .bigint_nat__lean_array_swap _ => "bigint_nat__lean_array_swap"
  | .uint53__lean_array_swap _ => "uint53__lean_array_swap"
  | .array__lean_array_pop _ => "array__lean_array_pop"
  | .array__lean_array_push_inplace _ => "array__lean_array_push_inplace"
  | .bigint_nat__lean_array_set_inplace _ => "bigint_nat__lean_array_set_inplace"
  | .uint53__lean_array_set_inplace _ => "uint53__lean_array_set_inplace"
  | .bigint_nat__lean_array_swap_inplace _ => "bigint_nat__lean_array_swap_inplace"
  | .uint53__lean_array_swap_inplace _ => "uint53__lean_array_swap_inplace"
  | .array__lean_array_pop_inplace _ => "array__lean_array_pop_inplace"
  | .bigint_nat__lean_nat_div => "bigint_nat__lean_nat_div"
  | .uint53__lean_nat_div => "uint53__lean_nat_div"
  | .bigint_nat__lean_uint32_of_nat__UInt32_ofNatLT => "bigint_nat__lean_uint32_of_nat__UInt32_ofNatLT"
  | .uint53__lean_uint32_of_nat__UInt32_ofNatLT => "uint53__lean_uint32_of_nat__UInt32_ofNatLT"
  | .bigint_nat__lean_uint32_of_nat__Char_ofNatAux => "bigint_nat__lean_uint32_of_nat__Char_ofNatAux"
  | .uint53__lean_uint32_of_nat__Char_ofNatAux => "uint53__lean_uint32_of_nat__Char_ofNatAux"
  | .bigint_nat__lean_nat_mod__Nat_modCore => "bigint_nat__lean_nat_mod__Nat_modCore"
  | .uint53__lean_nat_mod__Nat_modCore => "uint53__lean_nat_mod__Nat_modCore"
  | .bigint_nat__lean_nat_mod__Nat_mod => "bigint_nat__lean_nat_mod__Nat_mod"
  | .uint53__lean_nat_mod__Nat_mod => "uint53__lean_nat_mod__Nat_mod"
  | .bigint_nat__lean_nat_sub => "bigint_nat__lean_nat_sub"
  | .uint53__lean_nat_sub => "uint53__lean_nat_sub"
  | .bigint_nat__lean_uint8_of_nat__UInt8_ofNat => "bigint_nat__lean_uint8_of_nat__UInt8_ofNat"
  | .uint53__lean_uint8_of_nat__UInt8_ofNat => "uint53__lean_uint8_of_nat__UInt8_ofNat"
  | .bigint_nat__lean_uint8_of_nat__UInt8_ofNatLT => "bigint_nat__lean_uint8_of_nat__UInt8_ofNatLT"
  | .uint53__lean_uint8_of_nat__UInt8_ofNatLT => "uint53__lean_uint8_of_nat__UInt8_ofNatLT"
  | .uint53__lean_nat_add => "uint53__lean_nat_add"
  | .bigint_nat__lean_nat_pred => "bigint_nat__lean_nat_pred"
  | .uint53__lean_nat_pred => "uint53__lean_nat_pred"
  | .string__lean_string_mk__String_ofList => "string__lean_string_mk__String_ofList"
  | .bigint_nat__lean_string_hash => "bigint_nat__lean_string_hash"
  | .uint53__lean_string_hash => "uint53__lean_string_hash"
  | .bigint_nat__int53_bitvec64__lean_uint64_to_nat__UInt64_toBitVec => "bigint_nat__int53_bitvec64__lean_uint64_to_nat__UInt64_toBitVec"
  | .bigint_bitvec64__uint53__lean_uint64_of_nat_mk => "bigint_bitvec64__uint53__lean_uint64_of_nat_mk"
  | .bigint_nat__lean_uint16_of_nat__UInt16_ofNatLT => "bigint_nat__lean_uint16_of_nat__UInt16_ofNatLT"
  | .uint53__lean_uint16_of_nat__UInt16_ofNatLT => "uint53__lean_uint16_of_nat__UInt16_ofNatLT"
  | .bigint_nat__lean_nat_pow => "bigint_nat__lean_nat_pow"
  | .uint53__lean_nat_pow => "uint53__lean_nat_pow"
  | .uint53__lean_nat_mul => "uint53__lean_nat_mul"
  | .bigint_nat__lean_string_utf8_byte_size => "bigint_nat__lean_string_utf8_byte_size"
  | .uint53__lean_string_utf8_byte_size => "uint53__lean_string_utf8_byte_size"
  | .bigint_nat__lean_uint64_of_nat__UInt64_ofNatLT => "bigint_nat__lean_uint64_of_nat__UInt64_ofNatLT"
  | .bigint_nat__uint53__lean_uint64_of_nat__UInt64_ofNatLT => "bigint_nat__uint53__lean_uint64_of_nat__UInt64_ofNatLT"
  | .uint53__bigint_nat__lean_uint64_of_nat__UInt64_ofNatLT => "uint53__bigint_nat__lean_uint64_of_nat__UInt64_ofNatLT"
  | .uint53__lean_uint64_of_nat__UInt64_ofNatLT => "uint53__lean_uint64_of_nat__UInt64_ofNatLT"
  | .bigint_nat__int53__lean_nat_to_int => "bigint_nat__int53__lean_nat_to_int"
  | .int53__lean_int_mul => "int53__lean_int_mul"
  | .bigint_nat__bigint_int__lean_int_neg_succ_of_nat => "bigint_nat__bigint_int__lean_int_neg_succ_of_nat"
  | .bigint_nat__int53__lean_int_neg_succ_of_nat => "bigint_nat__int53__lean_int_neg_succ_of_nat"
  | .uint53__bigint_int__lean_int_neg_succ_of_nat => "uint53__bigint_int__lean_int_neg_succ_of_nat"
  | .uint53__int53__lean_int_neg_succ_of_nat => "uint53__int53__lean_int_neg_succ_of_nat"
  | .int53__lean_int_add => "int53__lean_int_add"
  | .int53__lean_int_neg => "int53__lean_int_neg"
  | .int53__lean_int_sub => "int53__lean_int_sub"
  | .bigint_int__bigint_nat__lean_nat_abs => "bigint_int__bigint_nat__lean_nat_abs"
  | .bigint_int__uint53__lean_nat_abs => "bigint_int__uint53__lean_nat_abs"
  | .int53__bigint_nat__lean_nat_abs => "int53__bigint_nat__lean_nat_abs"
  | .int53__uint53__lean_nat_abs => "int53__uint53__lean_nat_abs"
  | .bigint_nat__lean_nat_div_exact => "bigint_nat__lean_nat_div_exact"
  | .uint53__lean_nat_div_exact => "uint53__lean_nat_div_exact"
  | .uint53__lean_nat_lxor => "uint53__lean_nat_lxor"
  | .uint53__lean_nat_shiftl => "uint53__lean_nat_shiftl"
  | .uint53__lean_nat_shiftr => "uint53__lean_nat_shiftr"
  | .uint53__lean_nat_land => "uint53__lean_nat_land"
  | .uint53__lean_nat_lor => "uint53__lean_nat_lor"
  | .bigint_nat__lean_nat_log2 => "bigint_nat__lean_nat_log2"
  | .uint53__lean_nat_log2 => "uint53__lean_nat_log2"
  | .bigint_int__lean_int_emod => "bigint_int__lean_int_emod"
  | .int53__lean_int_emod => "int53__lean_int_emod"
  | .bigint_int__lean_int_div_exact => "bigint_int__lean_int_div_exact"
  | .int53__lean_int_div_exact => "int53__lean_int_div_exact"
  | .bigint_int__lean_int_mod => "bigint_int__lean_int_mod"
  | .int53__lean_int_mod => "int53__lean_int_mod"
  | .bigint_int__lean_int_ediv => "bigint_int__lean_int_ediv"
  | .int53__lean_int_ediv => "int53__lean_int_ediv"
  | .bigint_int__lean_int_div => "bigint_int__lean_int_div"
  | .int53__lean_int_div => "int53__lean_int_div"
  | .bigint_nat__uint53__lean_uint64_to_nat__UInt64_toNat => "bigint_nat__uint53__lean_uint64_to_nat__UInt64_toNat"
  | .uint32__lean_uint32_to_uint8 => "uint32__lean_uint32_to_uint8"
  | .bigint_nat__lean_uint64_to_uint32 => "bigint_nat__lean_uint64_to_uint32"
  | .uint53__lean_uint64_to_uint32 => "uint53__lean_uint64_to_uint32"
  | .uint32__lean_uint32_to_uint16 => "uint32__lean_uint32_to_uint16"
  | .bigint_nat__lean_uint32_of_nat__UInt32_ofNat => "bigint_nat__lean_uint32_of_nat__UInt32_ofNat"
  | .uint53__lean_uint32_of_nat__UInt32_ofNat => "uint53__lean_uint32_of_nat__UInt32_ofNat"
  | .uint32__lean_uint32_sub => "uint32__lean_uint32_sub"
  | .uint16__lean_uint16_to_uint8 => "uint16__lean_uint16_to_uint8"
  | .uint32__lean_uint32_add => "uint32__lean_uint32_add"
  | .bigint_nat__lean_uint64_of_nat__UInt64_ofNat => "bigint_nat__lean_uint64_of_nat__UInt64_ofNat"
  | .bigint_nat__uint53__lean_uint64_of_nat__UInt64_ofNat => "bigint_nat__uint53__lean_uint64_of_nat__UInt64_ofNat"
  | .uint53__bigint_nat__lean_uint64_of_nat__UInt64_ofNat => "uint53__bigint_nat__lean_uint64_of_nat__UInt64_ofNat"
  | .uint53__lean_uint64_of_nat__UInt64_ofNat => "uint53__lean_uint64_of_nat__UInt64_ofNat"
  | .bigint_nat__lean_uint16_of_nat__UInt16_ofNat => "bigint_nat__lean_uint16_of_nat__UInt16_ofNat"
  | .uint53__lean_uint16_of_nat__UInt16_ofNat => "uint53__lean_uint16_of_nat__UInt16_ofNat"
  | .bigint_nat__lean_uint64_to_uint8 => "bigint_nat__lean_uint64_to_uint8"
  | .uint53__lean_uint64_to_uint8 => "uint53__lean_uint64_to_uint8"
  | .bigint_nat__lean_uint64_to_uint16 => "bigint_nat__lean_uint64_to_uint16"
  | .uint53__lean_uint64_to_uint16 => "uint53__lean_uint64_to_uint16"
  | .uint8__lean_uint8_sub => "uint8__lean_uint8_sub"
  | .uint8__lean_uint8_neg => "uint8__lean_uint8_neg"
  | .uint8__lean_uint8_lor => "uint8__lean_uint8_lor"
  | .uint8__lean_uint8_div => "uint8__lean_uint8_div"
  | .uint8__lean_uint8_shift_right => "uint8__lean_uint8_shift_right"
  | .uint8__lean_uint8_shift_left => "uint8__lean_uint8_shift_left"
  | .uint8__lean_uint8_land => "uint8__lean_uint8_land"
  | .uint8__lean_uint8_mul => "uint8__lean_uint8_mul"
  | .uint8__lean_uint8_add => "uint8__lean_uint8_add"
  | .uint8__lean_uint8_complement => "uint8__lean_uint8_complement"
  | .uint8__lean_uint8_mod => "uint8__lean_uint8_mod"
  | .bool__lean_bool_to_uint8 => "bool__lean_bool_to_uint8"
  | .uint8__lean_uint8_xor => "uint8__lean_uint8_xor"
  | .uint16__lean_uint16_neg => "uint16__lean_uint16_neg"
  | .uint16__lean_uint16_add => "uint16__lean_uint16_add"
  | .uint16__lean_uint16_lor => "uint16__lean_uint16_lor"
  | .uint16__lean_uint16_mul => "uint16__lean_uint16_mul"
  | .uint16__lean_uint16_land => "uint16__lean_uint16_land"
  | .uint16__lean_uint16_complement => "uint16__lean_uint16_complement"
  | .uint16__lean_uint16_xor => "uint16__lean_uint16_xor"
  | .uint16__lean_uint16_shift_left => "uint16__lean_uint16_shift_left"
  | .uint16__lean_uint16_mod => "uint16__lean_uint16_mod"
  | .uint16__lean_uint16_div => "uint16__lean_uint16_div"
  | .uint16__lean_uint16_sub => "uint16__lean_uint16_sub"
  | .bool__lean_bool_to_uint16 => "bool__lean_bool_to_uint16"
  | .uint16__lean_uint16_shift_right => "uint16__lean_uint16_shift_right"
  | .uint32__lean_uint32_mod => "uint32__lean_uint32_mod"
  | .bool__lean_bool_to_uint32 => "bool__lean_bool_to_uint32"
  | .uint32__lean_uint32_div => "uint32__lean_uint32_div"
  | .uint32__lean_uint32_shift_right => "uint32__lean_uint32_shift_right"
  | .uint32__lean_uint32_neg => "uint32__lean_uint32_neg"
  | .uint32__lean_uint32_lor => "uint32__lean_uint32_lor"
  | .uint32__lean_uint32_xor => "uint32__lean_uint32_xor"
  | .uint32__lean_uint32_shift_left => "uint32__lean_uint32_shift_left"
  | .uint32__lean_uint32_mul => "uint32__lean_uint32_mul"
  | .uint32__lean_uint32_land => "uint32__lean_uint32_land"
  | .uint32__lean_uint32_complement => "uint32__lean_uint32_complement"
  | .bigint_nat__lean_uint64_shift_left => "bigint_nat__lean_uint64_shift_left"
  | .uint53__lean_uint64_shift_left => "uint53__lean_uint64_shift_left"
  | .bigint_nat__lean_uint64_shift_right => "bigint_nat__lean_uint64_shift_right"
  | .uint53__lean_uint64_shift_right => "uint53__lean_uint64_shift_right"
  | .bigint_nat__lean_uint64_complement => "bigint_nat__lean_uint64_complement"
  | .uint53__lean_uint64_complement => "uint53__lean_uint64_complement"
  | .bigint_nat__lean_uint64_add => "bigint_nat__lean_uint64_add"
  | .uint53__lean_uint64_add => "uint53__lean_uint64_add"
  | .bigint_nat__lean_uint64_lor => "bigint_nat__lean_uint64_lor"
  | .uint53__lean_uint64_lor => "uint53__lean_uint64_lor"
  | .bigint_nat__lean_uint64_mod => "bigint_nat__lean_uint64_mod"
  | .uint53__lean_uint64_mod => "uint53__lean_uint64_mod"
  | .bigint_nat__lean_uint64_div => "bigint_nat__lean_uint64_div"
  | .uint53__lean_uint64_div => "uint53__lean_uint64_div"
  | .bigint_nat__lean_uint64_mul => "bigint_nat__lean_uint64_mul"
  | .uint53__lean_uint64_mul => "uint53__lean_uint64_mul"
  | .bigint_nat__lean_uint64_land => "bigint_nat__lean_uint64_land"
  | .uint53__lean_uint64_land => "uint53__lean_uint64_land"
  | .bigint_nat__lean_bool_to_uint64 => "bigint_nat__lean_bool_to_uint64"
  | .uint53__lean_bool_to_uint64 => "uint53__lean_bool_to_uint64"
  | .bigint_nat__lean_uint64_sub => "bigint_nat__lean_uint64_sub"
  | .uint53__lean_uint64_sub => "uint53__lean_uint64_sub"
  | .bigint_nat__lean_uint64_neg => "bigint_nat__lean_uint64_neg"
  | .uint53__lean_uint64_neg => "uint53__lean_uint64_neg"
  | .bigint_nat__lean_uint64_xor => "bigint_nat__lean_uint64_xor"
  | .uint53__lean_uint64_xor => "uint53__lean_uint64_xor"
  | .int8__lean_int8_add => "int8__lean_int8_add"
  | .int8__lean_int8_div => "int8__lean_int8_div"
  | .int8__lean_int8_shift_right => "int8__lean_int8_shift_right"
  | .int8__lean_int8_mod => "int8__lean_int8_mod"
  | .bool__lean_bool_to_int8 => "bool__lean_bool_to_int8"
  | .int8__lean_int8_shift_left => "int8__lean_int8_shift_left"
  | .int8__lean_int8_xor => "int8__lean_int8_xor"
  | .int8__lean_int8_complement => "int8__lean_int8_complement"
  | .int8__lean_int8_neg => "int8__lean_int8_neg"
  | .int8__lean_int8_abs => "int8__lean_int8_abs"
  | .int8__lean_int8_sub => "int8__lean_int8_sub"
  | .bigint_nat__lean_int8_of_nat => "bigint_nat__lean_int8_of_nat"
  | .uint53__lean_int8_of_nat => "uint53__lean_int8_of_nat"
  | .int8__lean_int8_mul => "int8__lean_int8_mul"
  | .int8__lean_int8_land => "int8__lean_int8_land"
  | .bigint_int__lean_int8_of_int => "bigint_int__lean_int8_of_int"
  | .int53__lean_int8_of_int => "int53__lean_int8_of_int"
  | .int8__lean_int8_lor => "int8__lean_int8_lor"
  | .bigint_nat__lean_int16_of_nat => "bigint_nat__lean_int16_of_nat"
  | .uint53__lean_int16_of_nat => "uint53__lean_int16_of_nat"
  | .int16__lean_int16_shift_right => "int16__lean_int16_shift_right"
  | .int16__lean_int16_div => "int16__lean_int16_div"
  | .int16__lean_int16_mod => "int16__lean_int16_mod"
  | .bool__lean_bool_to_int16 => "bool__lean_bool_to_int16"
  | .int16__lean_int16_abs => "int16__lean_int16_abs"
  | .int16__lean_int16_complement => "int16__lean_int16_complement"
  | .int16__lean_int16_land => "int16__lean_int16_land"
  | .bigint_int__lean_int16_of_int => "bigint_int__lean_int16_of_int"
  | .int53__lean_int16_of_int => "int53__lean_int16_of_int"
  | .int16__lean_int16_mul => "int16__lean_int16_mul"
  | .int16__lean_int16_shift_left => "int16__lean_int16_shift_left"
  | .int16__lean_int16_xor => "int16__lean_int16_xor"
  | .int16__lean_int16_lor => "int16__lean_int16_lor"
  | .int16__lean_int16_add => "int16__lean_int16_add"
  | .int16__lean_int16_to_int8 => "int16__lean_int16_to_int8"
  | .int16__lean_int16_neg => "int16__lean_int16_neg"
  | .int16__lean_int16_sub => "int16__lean_int16_sub"
  | .bigint_int__lean_int32_of_int => "bigint_int__lean_int32_of_int"
  | .int53__lean_int32_of_int => "int53__lean_int32_of_int"
  | .int32__lean_int32_land => "int32__lean_int32_land"
  | .int32__lean_int32_mul => "int32__lean_int32_mul"
  | .bigint_nat__lean_int32_of_nat => "bigint_nat__lean_int32_of_nat"
  | .uint53__lean_int32_of_nat => "uint53__lean_int32_of_nat"
  | .int32__lean_int32_sub => "int32__lean_int32_sub"
  | .int32__lean_int32_neg => "int32__lean_int32_neg"
  | .int32__lean_int32_abs => "int32__lean_int32_abs"
  | .int32__lean_int32_xor => "int32__lean_int32_xor"
  | .int32__lean_int32_shift_left => "int32__lean_int32_shift_left"
  | .int32__lean_int32_shift_right => "int32__lean_int32_shift_right"
  | .int32__lean_int32_complement => "int32__lean_int32_complement"
  | .bool__lean_bool_to_int32 => "bool__lean_bool_to_int32"
  | .int32__lean_int32_to_int8 => "int32__lean_int32_to_int8"
  | .int32__lean_int32_add => "int32__lean_int32_add"
  | .int32__lean_int32_lor => "int32__lean_int32_lor"
  | .int32__lean_int32_mod => "int32__lean_int32_mod"
  | .int32__lean_int32_to_int16 => "int32__lean_int32_to_int16"
  | .int32__lean_int32_div => "int32__lean_int32_div"
  | .bigint_int__lean_int64_sub => "bigint_int__lean_int64_sub"
  | .int53__lean_int64_sub => "int53__lean_int64_sub"
  | .bigint_int__lean_int64_xor => "bigint_int__lean_int64_xor"
  | .int53__lean_int64_xor => "int53__lean_int64_xor"
  | .bigint_int__lean_int64_to_int8 => "bigint_int__lean_int64_to_int8"
  | .int53__lean_int64_to_int8 => "int53__lean_int64_to_int8"
  | .bigint_int__lean_int64_mul => "bigint_int__lean_int64_mul"
  | .int53__lean_int64_mul => "int53__lean_int64_mul"
  | .bigint_int__lean_int64_of_int => "bigint_int__lean_int64_of_int"
  | .bigint_int__int53__lean_int64_of_int => "bigint_int__int53__lean_int64_of_int"
  | .int53__bigint_int__lean_int64_of_int => "int53__bigint_int__lean_int64_of_int"
  | .int53__lean_int64_of_int => "int53__lean_int64_of_int"
  | .bigint_int__lean_int64_land => "bigint_int__lean_int64_land"
  | .int53__lean_int64_land => "int53__lean_int64_land"
  | .bigint_int__lean_int64_lor => "bigint_int__lean_int64_lor"
  | .int53__lean_int64_lor => "int53__lean_int64_lor"
  | .bigint_int__lean_int64_mod => "bigint_int__lean_int64_mod"
  | .int53__lean_int64_mod => "int53__lean_int64_mod"
  | .bigint_int__lean_int64_shift_left => "bigint_int__lean_int64_shift_left"
  | .int53__lean_int64_shift_left => "int53__lean_int64_shift_left"
  | .bigint_int__lean_int64_complement => "bigint_int__lean_int64_complement"
  | .int53__lean_int64_complement => "int53__lean_int64_complement"
  | .bigint_int__lean_int64_to_int32 => "bigint_int__lean_int64_to_int32"
  | .int53__lean_int64_to_int32 => "int53__lean_int64_to_int32"
  | .bigint_int__lean_int64_abs => "bigint_int__lean_int64_abs"
  | .int53__lean_int64_abs => "int53__lean_int64_abs"
  | .bigint_int__lean_bool_to_int64 => "bigint_int__lean_bool_to_int64"
  | .int53__lean_bool_to_int64 => "int53__lean_bool_to_int64"
  | .bigint_nat__bigint_int__lean_int64_of_nat => "bigint_nat__bigint_int__lean_int64_of_nat"
  | .bigint_nat__int53__lean_int64_of_nat => "bigint_nat__int53__lean_int64_of_nat"
  | .uint53__bigint_int__lean_int64_of_nat => "uint53__bigint_int__lean_int64_of_nat"
  | .uint53__int53__lean_int64_of_nat => "uint53__int53__lean_int64_of_nat"
  | .bigint_int__int53__lean_int64_to_int_sint => "bigint_int__int53__lean_int64_to_int_sint"
  | .bigint_int__lean_int64_neg => "bigint_int__lean_int64_neg"
  | .int53__lean_int64_neg => "int53__lean_int64_neg"
  | .bigint_int__lean_int64_add => "bigint_int__lean_int64_add"
  | .int53__lean_int64_add => "int53__lean_int64_add"
  | .bigint_int__lean_int64_div => "bigint_int__lean_int64_div"
  | .int53__lean_int64_div => "int53__lean_int64_div"
  | .bigint_int__lean_int64_to_int16 => "bigint_int__lean_int64_to_int16"
  | .int53__lean_int64_to_int16 => "int53__lean_int64_to_int16"
  | .bigint_int__lean_int64_shift_right => "bigint_int__lean_int64_shift_right"
  | .int53__lean_int64_shift_right => "int53__lean_int64_shift_right"
  | .uint16__lean_uint16_log2 => "uint16__lean_uint16_log2"
  | .bigint_nat__lean_uint64_log2 => "bigint_nat__lean_uint64_log2"
  | .uint53__lean_uint64_log2 => "uint53__lean_uint64_log2"
  | .uint8__lean_uint8_log2 => "uint8__lean_uint8_log2"
  | .uint32__lean_uint32_log2 => "uint32__lean_uint32_log2"
  | .string__lean_string_utf8_get__String_Internal_get => "string__lean_string_utf8_get__String_Internal_get"
  | .string__lean_string_isempty => "string__lean_string_isempty"
  | .bigint_nat__lean_string_length__String_Internal_length => "bigint_nat__lean_string_length__String_Internal_length"
  | .uint53__lean_string_length__String_Internal_length => "uint53__lean_string_length__String_Internal_length"
  | .string__lean_string_utf8_at_end__String_Internal_atEnd => "string__lean_string_utf8_at_end__String_Internal_atEnd"
  | .string__lean_string_utf8_next__String_Internal_next => "string__lean_string_utf8_next__String_Internal_next"
  | .string__lean_string_mk__String_mk => "string__lean_string_mk__String_mk"
  | .bigint_nat__lean_string_pushn => "bigint_nat__lean_string_pushn"
  | .uint53__lean_string_pushn => "uint53__lean_string_pushn"
  | .string__lean_string_utf8_extract__String_Internal_extract => "string__lean_string_utf8_extract__String_Internal_extract"
  | .string__lean_string_utf8_next__String_next => "string__lean_string_utf8_next__String_next"
  | .string__lean_string_utf8_next__String_Pos_Raw_next => "string__lean_string_utf8_next__String_Pos_Raw_next"
  | .string__lean_string_utf8_get__String_Pos_Raw_get => "string__lean_string_utf8_get__String_Pos_Raw_get"
  | .string__lean_string_utf8_get__String_get => "string__lean_string_utf8_get__String_get"
  | .string__lean_string_data__String_data => "string__lean_string_data__String_data"
  | .string__lean_string_data__String_toList => "string__lean_string_data__String_toList"
  | .string__lean_string_utf8_at_end__String_atEnd => "string__lean_string_utf8_at_end__String_atEnd"
  | .string__lean_string_utf8_at_end__String_Pos_Raw_atEnd => "string__lean_string_utf8_at_end__String_Pos_Raw_atEnd"
  | .string__lean_string_utf8_extract__String_Pos_Raw_extract => "string__lean_string_utf8_extract__String_Pos_Raw_extract"
  | .bigint_nat__lean_string_length__String_length => "bigint_nat__lean_string_length__String_length"
  | .uint53__lean_string_length__String_length => "uint53__lean_string_length__String_length"
  | .string__lean_string_memcmp => "string__lean_string_memcmp"
  | .string__lean_string_utf8_set__String_Pos_Raw_set => "string__lean_string_utf8_set__String_Pos_Raw_set"
  | .uint53__lean_string_utf8_set__String_Pos_set => "uint53__lean_string_utf8_set__String_Pos_set"
  | .string__lean_string_utf8_set__String_set => "string__lean_string_utf8_set__String_set"
  | .string__lean_string_compare => "string__lean_string_compare"
  | .float__lean_float_isnan => "float__lean_float_isnan"
  | .float__lean_float_isfinite => "float__lean_float_isfinite"
  | .float__lean_float_isinf => "float__lean_float_isinf"
  | .float32__lean_float32_div => "float32__lean_float32_div"
  | .float__lean_float_to_float32 => "float__lean_float_to_float32"
  | .float32__lean_float32_sub => "float32__lean_float32_sub"
  | .float32__lean_float32_isnan => "float32__lean_float32_isnan"
  | .float32__lean_float32_isinf => "float32__lean_float32_isinf"
  | .float32__lean_float32_isfinite => "float32__lean_float32_isfinite"
  | .float32__lean_float32_add => "float32__lean_float32_add"
  | .float32__lean_float32_mul => "float32__lean_float32_mul"

/-- The globals passed before the arguments (the constructor of a typed array). -/
def extraArgs {σs : List JsTy} {τ : JsTy} : JsOpImported σs τ → List String
  | .typedArray__bigint_nat__lean_mk_array k _ => [k.ctorName]
  | .typedArray__uint53__lean_mk_array k _ => [k.ctorName]
  | _ => []

/-- The name of every operation (for the tests: `runtime.js` exports each). -/
def allNames : List String := [
  "bigint_nat__lean_array_get_borrowed",
  "uint53__lean_array_get_borrowed",
  "array__lean_array_push",
  "typedArray__lean_array_to_list",
  "bigint_nat__lean_array_get",
  "uint53__lean_array_get",
  "thunk__lean_thunk_pure",
  "thunk__lean_mk_thunk",
  "thunk__lean_thunk_get_own",
  "bigint_nat__lean_array_set",
  "uint53__lean_array_set",
  "bigint_nat__lean_array_fset",
  "uint53__lean_array_fset",
  "bigint_nat__lean_array_fswap",
  "uint53__lean_array_fswap",
  "bigint_nat__lean_mk_array",
  "typedArray__bigint_nat__lean_mk_array",
  "uint53__lean_mk_array",
  "typedArray__uint53__lean_mk_array",
  "bigint_nat__lean_array_swap",
  "uint53__lean_array_swap",
  "array__lean_array_pop",
  "array__lean_array_push_inplace",
  "bigint_nat__lean_array_set_inplace",
  "uint53__lean_array_set_inplace",
  "bigint_nat__lean_array_swap_inplace",
  "uint53__lean_array_swap_inplace",
  "array__lean_array_pop_inplace",
  "bigint_nat__lean_nat_div",
  "uint53__lean_nat_div",
  "bigint_nat__lean_uint32_of_nat__UInt32_ofNatLT",
  "uint53__lean_uint32_of_nat__UInt32_ofNatLT",
  "bigint_nat__lean_uint32_of_nat__Char_ofNatAux",
  "uint53__lean_uint32_of_nat__Char_ofNatAux",
  "bigint_nat__lean_nat_mod__Nat_modCore",
  "uint53__lean_nat_mod__Nat_modCore",
  "bigint_nat__lean_nat_mod__Nat_mod",
  "uint53__lean_nat_mod__Nat_mod",
  "bigint_nat__lean_nat_sub",
  "uint53__lean_nat_sub",
  "bigint_nat__lean_uint8_of_nat__UInt8_ofNat",
  "uint53__lean_uint8_of_nat__UInt8_ofNat",
  "bigint_nat__lean_uint8_of_nat__UInt8_ofNatLT",
  "uint53__lean_uint8_of_nat__UInt8_ofNatLT",
  "uint53__lean_nat_add",
  "bigint_nat__lean_nat_pred",
  "uint53__lean_nat_pred",
  "string__lean_string_mk__String_ofList",
  "bigint_nat__lean_string_hash",
  "uint53__lean_string_hash",
  "bigint_nat__int53_bitvec64__lean_uint64_to_nat__UInt64_toBitVec",
  "bigint_bitvec64__uint53__lean_uint64_of_nat_mk",
  "bigint_nat__lean_uint16_of_nat__UInt16_ofNatLT",
  "uint53__lean_uint16_of_nat__UInt16_ofNatLT",
  "bigint_nat__lean_nat_pow",
  "uint53__lean_nat_pow",
  "uint53__lean_nat_mul",
  "bigint_nat__lean_string_utf8_byte_size",
  "uint53__lean_string_utf8_byte_size",
  "bigint_nat__lean_uint64_of_nat__UInt64_ofNatLT",
  "bigint_nat__uint53__lean_uint64_of_nat__UInt64_ofNatLT",
  "uint53__bigint_nat__lean_uint64_of_nat__UInt64_ofNatLT",
  "uint53__lean_uint64_of_nat__UInt64_ofNatLT",
  "bigint_nat__int53__lean_nat_to_int",
  "int53__lean_int_mul",
  "bigint_nat__bigint_int__lean_int_neg_succ_of_nat",
  "bigint_nat__int53__lean_int_neg_succ_of_nat",
  "uint53__bigint_int__lean_int_neg_succ_of_nat",
  "uint53__int53__lean_int_neg_succ_of_nat",
  "int53__lean_int_add",
  "int53__lean_int_neg",
  "int53__lean_int_sub",
  "bigint_int__bigint_nat__lean_nat_abs",
  "bigint_int__uint53__lean_nat_abs",
  "int53__bigint_nat__lean_nat_abs",
  "int53__uint53__lean_nat_abs",
  "bigint_nat__lean_nat_div_exact",
  "uint53__lean_nat_div_exact",
  "uint53__lean_nat_lxor",
  "uint53__lean_nat_shiftl",
  "uint53__lean_nat_shiftr",
  "uint53__lean_nat_land",
  "uint53__lean_nat_lor",
  "bigint_nat__lean_nat_log2",
  "uint53__lean_nat_log2",
  "bigint_int__lean_int_emod",
  "int53__lean_int_emod",
  "bigint_int__lean_int_div_exact",
  "int53__lean_int_div_exact",
  "bigint_int__lean_int_mod",
  "int53__lean_int_mod",
  "bigint_int__lean_int_ediv",
  "int53__lean_int_ediv",
  "bigint_int__lean_int_div",
  "int53__lean_int_div",
  "bigint_nat__uint53__lean_uint64_to_nat__UInt64_toNat",
  "uint32__lean_uint32_to_uint8",
  "bigint_nat__lean_uint64_to_uint32",
  "uint53__lean_uint64_to_uint32",
  "uint32__lean_uint32_to_uint16",
  "bigint_nat__lean_uint32_of_nat__UInt32_ofNat",
  "uint53__lean_uint32_of_nat__UInt32_ofNat",
  "uint32__lean_uint32_sub",
  "uint16__lean_uint16_to_uint8",
  "uint32__lean_uint32_add",
  "bigint_nat__lean_uint64_of_nat__UInt64_ofNat",
  "bigint_nat__uint53__lean_uint64_of_nat__UInt64_ofNat",
  "uint53__bigint_nat__lean_uint64_of_nat__UInt64_ofNat",
  "uint53__lean_uint64_of_nat__UInt64_ofNat",
  "bigint_nat__lean_uint16_of_nat__UInt16_ofNat",
  "uint53__lean_uint16_of_nat__UInt16_ofNat",
  "bigint_nat__lean_uint64_to_uint8",
  "uint53__lean_uint64_to_uint8",
  "bigint_nat__lean_uint64_to_uint16",
  "uint53__lean_uint64_to_uint16",
  "uint8__lean_uint8_sub",
  "uint8__lean_uint8_neg",
  "uint8__lean_uint8_lor",
  "uint8__lean_uint8_div",
  "uint8__lean_uint8_shift_right",
  "uint8__lean_uint8_shift_left",
  "uint8__lean_uint8_land",
  "uint8__lean_uint8_mul",
  "uint8__lean_uint8_add",
  "uint8__lean_uint8_complement",
  "uint8__lean_uint8_mod",
  "bool__lean_bool_to_uint8",
  "uint8__lean_uint8_xor",
  "uint16__lean_uint16_neg",
  "uint16__lean_uint16_add",
  "uint16__lean_uint16_lor",
  "uint16__lean_uint16_mul",
  "uint16__lean_uint16_land",
  "uint16__lean_uint16_complement",
  "uint16__lean_uint16_xor",
  "uint16__lean_uint16_shift_left",
  "uint16__lean_uint16_mod",
  "uint16__lean_uint16_div",
  "uint16__lean_uint16_sub",
  "bool__lean_bool_to_uint16",
  "uint16__lean_uint16_shift_right",
  "uint32__lean_uint32_mod",
  "bool__lean_bool_to_uint32",
  "uint32__lean_uint32_div",
  "uint32__lean_uint32_shift_right",
  "uint32__lean_uint32_neg",
  "uint32__lean_uint32_lor",
  "uint32__lean_uint32_xor",
  "uint32__lean_uint32_shift_left",
  "uint32__lean_uint32_mul",
  "uint32__lean_uint32_land",
  "uint32__lean_uint32_complement",
  "bigint_nat__lean_uint64_shift_left",
  "uint53__lean_uint64_shift_left",
  "bigint_nat__lean_uint64_shift_right",
  "uint53__lean_uint64_shift_right",
  "bigint_nat__lean_uint64_complement",
  "uint53__lean_uint64_complement",
  "bigint_nat__lean_uint64_add",
  "uint53__lean_uint64_add",
  "bigint_nat__lean_uint64_lor",
  "uint53__lean_uint64_lor",
  "bigint_nat__lean_uint64_mod",
  "uint53__lean_uint64_mod",
  "bigint_nat__lean_uint64_div",
  "uint53__lean_uint64_div",
  "bigint_nat__lean_uint64_mul",
  "uint53__lean_uint64_mul",
  "bigint_nat__lean_uint64_land",
  "uint53__lean_uint64_land",
  "bigint_nat__lean_bool_to_uint64",
  "uint53__lean_bool_to_uint64",
  "bigint_nat__lean_uint64_sub",
  "uint53__lean_uint64_sub",
  "bigint_nat__lean_uint64_neg",
  "uint53__lean_uint64_neg",
  "bigint_nat__lean_uint64_xor",
  "uint53__lean_uint64_xor",
  "int8__lean_int8_add",
  "int8__lean_int8_div",
  "int8__lean_int8_shift_right",
  "int8__lean_int8_mod",
  "bool__lean_bool_to_int8",
  "int8__lean_int8_shift_left",
  "int8__lean_int8_xor",
  "int8__lean_int8_complement",
  "int8__lean_int8_neg",
  "int8__lean_int8_abs",
  "int8__lean_int8_sub",
  "bigint_nat__lean_int8_of_nat",
  "uint53__lean_int8_of_nat",
  "int8__lean_int8_mul",
  "int8__lean_int8_land",
  "bigint_int__lean_int8_of_int",
  "int53__lean_int8_of_int",
  "int8__lean_int8_lor",
  "bigint_nat__lean_int16_of_nat",
  "uint53__lean_int16_of_nat",
  "int16__lean_int16_shift_right",
  "int16__lean_int16_div",
  "int16__lean_int16_mod",
  "bool__lean_bool_to_int16",
  "int16__lean_int16_abs",
  "int16__lean_int16_complement",
  "int16__lean_int16_land",
  "bigint_int__lean_int16_of_int",
  "int53__lean_int16_of_int",
  "int16__lean_int16_mul",
  "int16__lean_int16_shift_left",
  "int16__lean_int16_xor",
  "int16__lean_int16_lor",
  "int16__lean_int16_add",
  "int16__lean_int16_to_int8",
  "int16__lean_int16_neg",
  "int16__lean_int16_sub",
  "bigint_int__lean_int32_of_int",
  "int53__lean_int32_of_int",
  "int32__lean_int32_land",
  "int32__lean_int32_mul",
  "bigint_nat__lean_int32_of_nat",
  "uint53__lean_int32_of_nat",
  "int32__lean_int32_sub",
  "int32__lean_int32_neg",
  "int32__lean_int32_abs",
  "int32__lean_int32_xor",
  "int32__lean_int32_shift_left",
  "int32__lean_int32_shift_right",
  "int32__lean_int32_complement",
  "bool__lean_bool_to_int32",
  "int32__lean_int32_to_int8",
  "int32__lean_int32_add",
  "int32__lean_int32_lor",
  "int32__lean_int32_mod",
  "int32__lean_int32_to_int16",
  "int32__lean_int32_div",
  "bigint_int__lean_int64_sub",
  "int53__lean_int64_sub",
  "bigint_int__lean_int64_xor",
  "int53__lean_int64_xor",
  "bigint_int__lean_int64_to_int8",
  "int53__lean_int64_to_int8",
  "bigint_int__lean_int64_mul",
  "int53__lean_int64_mul",
  "bigint_int__lean_int64_of_int",
  "bigint_int__int53__lean_int64_of_int",
  "int53__bigint_int__lean_int64_of_int",
  "int53__lean_int64_of_int",
  "bigint_int__lean_int64_land",
  "int53__lean_int64_land",
  "bigint_int__lean_int64_lor",
  "int53__lean_int64_lor",
  "bigint_int__lean_int64_mod",
  "int53__lean_int64_mod",
  "bigint_int__lean_int64_shift_left",
  "int53__lean_int64_shift_left",
  "bigint_int__lean_int64_complement",
  "int53__lean_int64_complement",
  "bigint_int__lean_int64_to_int32",
  "int53__lean_int64_to_int32",
  "bigint_int__lean_int64_abs",
  "int53__lean_int64_abs",
  "bigint_int__lean_bool_to_int64",
  "int53__lean_bool_to_int64",
  "bigint_nat__bigint_int__lean_int64_of_nat",
  "bigint_nat__int53__lean_int64_of_nat",
  "uint53__bigint_int__lean_int64_of_nat",
  "uint53__int53__lean_int64_of_nat",
  "bigint_int__int53__lean_int64_to_int_sint",
  "bigint_int__lean_int64_neg",
  "int53__lean_int64_neg",
  "bigint_int__lean_int64_add",
  "int53__lean_int64_add",
  "bigint_int__lean_int64_div",
  "int53__lean_int64_div",
  "bigint_int__lean_int64_to_int16",
  "int53__lean_int64_to_int16",
  "bigint_int__lean_int64_shift_right",
  "int53__lean_int64_shift_right",
  "uint16__lean_uint16_log2",
  "bigint_nat__lean_uint64_log2",
  "uint53__lean_uint64_log2",
  "uint8__lean_uint8_log2",
  "uint32__lean_uint32_log2",
  "string__lean_string_utf8_get__String_Internal_get",
  "string__lean_string_isempty",
  "bigint_nat__lean_string_length__String_Internal_length",
  "uint53__lean_string_length__String_Internal_length",
  "string__lean_string_utf8_at_end__String_Internal_atEnd",
  "string__lean_string_utf8_next__String_Internal_next",
  "string__lean_string_mk__String_mk",
  "bigint_nat__lean_string_pushn",
  "uint53__lean_string_pushn",
  "string__lean_string_utf8_extract__String_Internal_extract",
  "string__lean_string_utf8_next__String_next",
  "string__lean_string_utf8_next__String_Pos_Raw_next",
  "string__lean_string_utf8_get__String_Pos_Raw_get",
  "string__lean_string_utf8_get__String_get",
  "string__lean_string_data__String_data",
  "string__lean_string_data__String_toList",
  "string__lean_string_utf8_at_end__String_atEnd",
  "string__lean_string_utf8_at_end__String_Pos_Raw_atEnd",
  "string__lean_string_utf8_extract__String_Pos_Raw_extract",
  "bigint_nat__lean_string_length__String_length",
  "uint53__lean_string_length__String_length",
  "string__lean_string_memcmp",
  "string__lean_string_utf8_set__String_Pos_Raw_set",
  "uint53__lean_string_utf8_set__String_Pos_set",
  "string__lean_string_utf8_set__String_set",
  "string__lean_string_compare",
  "float__lean_float_isnan",
  "float__lean_float_isfinite",
  "float__lean_float_isinf",
  "float32__lean_float32_div",
  "float__lean_float_to_float32",
  "float32__lean_float32_sub",
  "float32__lean_float32_isnan",
  "float32__lean_float32_isinf",
  "float32__lean_float32_isfinite",
  "float32__lean_float32_add",
  "float32__lean_float32_mul"]

end JsOpImported

end MoreJs

end
