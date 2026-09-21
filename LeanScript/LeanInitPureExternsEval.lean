module

public import Init
public import LeanScript.LeanInitPureExterns
public import LeanScript.ExternEval

@[expose] public section

set_option autoImplicit false

namespace LeanScript

def LeanInitPureExtern_T_T.eval : ∀ {a b : LeanPrimTy}, LeanInitPureExtern_T_T a b → a.denote → b.denote
  --------------------
  -- Init/Prelude.lean
  --------------------
  | _, _, .lean_uint32_of_nat_mk, v => (UInt32.ofBitVec v)
  | _, _, _, .lean_uint32_dec_eq, v, w => (v == w)
  | _, _, .lean_byte_array_size => ...nothing
  | _, _, .lean_string_to_utf8__String_toByteArray => ...nothing
  | _, _, _, .lean_uint32_dec_lt, v, w => (decide (v < w))
  | _, _, _, .lean_nat_div, v, w => (v / w)
  | _, _, .lean_sorry => ...nothing
  | _, _, .lean_uint32_of_nat__UInt32_ofNatLT => ...nothing
  | _, _, .lean_uint32_of_nat__Char_ofNatAux => ...nothing
  | _, _, .lean_array_get_borrowed => ...nothing
  | _, _, .lean_uint8_to_nat__UInt8_toBitVec => ...nothing
  | _, _, _, .lean_nat_dec_lt, v, w => (decide (v < w))
  | _, _, .lean_string_from_utf8_unchecked => ...nothing
  | _, _, .lean_nat_mod__Nat_modCore => ...nothing
  | _, _, .lean_nat_mod__Nat_mod => ...nothing
  | _, _, .lean_array_push => ...nothing
  | _, _, .lean_byte_array_mk => ...nothing
  | _, _, _, .lean_nat_sub, v, w => (v - w)
  | _, _, _, .lean_uint8_dec_lt, v, w => (decide (v < w))
  | _, _, .lean_byte_array_data => ...nothing
  | _, _, .lean_system_platform_nbits => ...nothing
  | _, _, _, .lean_uint32_dec_le, v, w => (decide (v ≤ w))
  | _, _, .lean_array_get_size => ...nothing
  | _, _, .lean_array_to_list => ...nothing
  | _, _, .lean_nat_dec_eq__Nat_decEq => ...nothing
  | _, _, .lean_nat_dec_eq__Nat_beq => ...nothing
  | _, _, .lean_array_fget_borrowed => ...nothing
  | _, _, .lean_mk_empty_array_with_capacity__Array_emptyWithCapacity => ...nothing
  | _, _, .lean_mk_empty_array_with_capacity__Array_mkEmpty => ...nothing
  | _, _, .lean_uint8_of_nat__UInt8_ofNat => ...nothing
  | _, _, .lean_uint8_of_nat__UInt8_ofNatLT => ...nothing
  | _, _, .lean_is_scalar => ...nothing
  | _, _, _, .lean_uint8_dec_le, v, w => (decide (v ≤ w))
  | _, _, .lean_nat_dec_le__Nat_ble => ...nothing
  | _, _, .lean_nat_dec_le__Nat_decLe => ...nothing
  | _, _, .lean_array_get => ...nothing
  | _, _, _, .lean_nat_add, v, w => (v + w)
  | _, _, .lean_panic_fn_borrowed => ...nothing
  | _, _, .lean_uint16_to_nat__UInt16_toBitVec => ...nothing
  | _, _, .lean_uint16_of_nat_mk, v => (UInt16.ofBitVec v)
  | _, _, _, .lean_uint16_dec_eq, v, w => (v == w)
  | _, _, _, .lean_string_dec_eq, v, w => (v == w)
  | _, _, .lean_nat_pred, v => (Nat.pred v)
  | _, _, .lean_usize_of_nat__USize_ofNatLT => ...nothing
  | _, _, .lean_string_mk__String_ofList => ...nothing
  | _, _, .lean_string_hash, v => (String.hash v)
  | _, _, .lean_uint64_to_nat__UInt64_toBitVec => ...nothing
  | _, _, .lean_uint64_of_nat_mk, v => (UInt64.ofBitVec v)
  | _, _, .lean_uint32_to_nat__UInt32_toNat => ...nothing
  | _, _, .lean_uint32_to_nat__UInt32_toBitVec => ...nothing
  | _, _, _, .lean_uint64_dec_eq, v, w => (v == w)
  | _, _, .lean_uint16_of_nat__UInt16_ofNatLT => ...nothing
  | _, _, .lean_name_eq => ...nothing
  | _, _, .lean_uint8_of_nat_mk, v => (UInt8.ofBitVec v)
  | _, _, .lean_mk_empty_byte_array => ...nothing
  | _, _, _, .lean_uint8_dec_eq, v, w => (v == w)
  | _, _, _, .lean_nat_pow, v, w => (v ^ w)
  | _, _, _, .lean_usize_dec_eq, v, w => (v == w)
  | _, _, .lean_usize_of_nat_mk, v => (UInt64.ofBitVec v)
  | _, _, .lean_array_fget => ...nothing
  | _, _, _, .lean_nat_mul, v, w => (v * w)
  | _, _, .lean_usize_to_nat__USize_toBitVec => ...nothing
  | _, _, .lean_string_utf8_byte_size, v => (String.utf8ByteSize v)
  | _, _, .lean_byte_array_push => ...nothing
  | _, _, .lean_array_mk => ...nothing
  | _, _, _, .lean_uint64_mix_hash, v, w => (mixHash v w)
  | _, _, .lean_uint64_of_nat__UInt64_ofNatLT => ...nothing
  -----------------
  -- Init/Core.lean
  -----------------
  | _, _, .lean_task_map => ...nothing
  | _, _, .lean_task_spawn => ...nothing
  | _, _, _, .lean_strict_or, v, w => (v || w)
  | _, _, .lean_thunk_pure => ...nothing
  | _, _, .lean_mk_thunk => ...nothing
  | _, _, .lean_task_get_own => ...nothing
  | _, _, .lean_task_pure => ...nothing
  | _, _, .lean_thunk_get_own => ...nothing
  | _, _, _, .lean_strict_and, v, w => (v && w)
  | _, _, .lean_task_bind => ...nothing
  ---------------------------
  -- Init/Data/Int/Basic.lean
  ---------------------------
  | _, _, .lean_nat_to_int, v => (Int.ofNat v)
  | _, _, _, .lean_int_dec_le, v, w => (decide (v ≤ w))
  | _, _, _, .lean_int_dec_lt, v, w => (decide (v < w))
  | _, _, _, .lean_int_dec_eq, v, w => (decide (v = w))
  | _, _, _, .lean_int_mul, v, w => (v * w)
  | _, _, .lean_int_dec_nonneg, v => (@decide _ (Int.decNonneg v))
  | _, _, .lean_int_neg_succ_of_nat, v => (Int.negSucc v)
  | _, _, _, .lean_int_add, v, w => (v + w)
  | _, _, .lean_int_neg, v => (Int.neg v)
  | _, _, _, .lean_int_sub, v, w => (v - w)
  | _, _, .lean_nat_abs, v => (Int.natAbs v)
  -------------------------------
  -- Init/Data/Nat/Div/Basic.lean
  -------------------------------
  | _, _, _, .lean_nat_div_exact, v, w => (v / w)
  -----------------------------------
  -- Init/Data/Nat/Bitwise/Basic.lean
  -----------------------------------
  | _, _, _, .lean_nat_lxor, v, w => (Nat.xor v w)
  | _, _, _, .lean_nat_shiftl, v, w => (Nat.shiftLeft v w)
  | _, _, _, .lean_nat_shiftr, v, w => (Nat.shiftRight v w)
  | _, _, _, .lean_nat_land, v, w => (Nat.land v w)
  | _, _, _, .lean_nat_lor, v, w => (Nat.lor v w)
  -------------------------------
  -- Init/Data/UInt/BasicAux.lean
  -------------------------------
  | _, _, .lean_uint64_to_nat__UInt64_toNat => ...nothing
  | _, _, .lean_uint32_to_uint8, v => (UInt32.toUInt8 v)
  | _, _, .lean_usize_to_nat__USize_toNat => ...nothing
  | _, _, .lean_uint64_to_uint32, v => (UInt64.toUInt32 v)
  | _, _, .lean_uint32_to_uint16, v => (UInt32.toUInt16 v)
  | _, _, .lean_uint16_to_uint32, v => (UInt16.toUInt32 v)
  | _, _, .lean_uint32_to_uint64, v => (UInt32.toUInt64 v)
  | _, _, .lean_uint32_of_nat__UInt32_ofNat => ...nothing
  | _, _, _, .lean_usize_add, v, w => (v + w)
  | _, _, _, .lean_uint32_sub, v, w => (v - w)
  | _, _, .lean_uint16_to_nat__UInt16_toNat => ...nothing
  | _, _, .lean_uint16_to_uint8, v => (UInt16.toUInt8 v)
  | _, _, _, .lean_usize_sub, v, w => (v - w)
  | _, _, _, .lean_uint32_add, v, w => (v + w)
  | _, _, .lean_usize_of_nat__USize_ofNat => ...nothing
  | _, _, _, .lean_usize_dec_le, v, w => (decide (v ≤ w))
  | _, _, .lean_uint8_to_uint64, v => (UInt8.toUInt64 v)
  | _, _, .lean_uint8_to_nat__UInt8_toNat => ...nothing
  | _, _, .lean_uint64_of_nat__UInt64_ofNat => ...nothing
  | _, _, .lean_uint8_to_uint32, v => (UInt8.toUInt32 v)
  | _, _, .lean_uint16_of_nat__UInt16_ofNat => ...nothing
  | _, _, .lean_uint16_to_uint64, v => (UInt16.toUInt64 v)
  | _, _, _, .lean_usize_dec_lt, v, w => (decide (v < w))
  | _, _, .lean_uint64_to_uint8, v => (UInt64.toUInt8 v)
  | _, _, .lean_uint64_to_uint16, v => (UInt64.toUInt16 v)
  | _, _, .lean_uint8_to_uint16, v => (UInt8.toUInt16 v)
  ----------------------------------
  -- Init/Data/String/Bootstrap.lean
  ----------------------------------
  | _, _, .lean_string_utf8_get__String_Internal_get => ...nothing
  | _, _, .lean_string_trim, v => (String.Internal.trim v)
  | _, _, _, .lean_substring_drop, v, w => (Substring.Raw.drop v w)
  | _, _, _, .lean_substring_prev, v, w => (Substring.Raw.prev v w)
  | _, _, _, _, .lean_substring_extract, s, i, j => (Substring.Raw.extract s ⟨i⟩ ⟨j⟩)
  | _, _, .lean_string_foldl => ...nothing
  | _, _, .lean_substring_tostring, v => (Substring.Raw.Internal.toString v)
  | _, _, .lean_string_append__String_Internal_append => ...nothing
  | _, _, .lean_string_get_byte_fast__String_Internal_getUTF8Byte => ...nothing
  | _, _, .lean_string_isempty, v => (String.Internal.isEmpty v)
  | _, _, _, .lean_string_push, v, w => (String.push v w)
  | _, _, _, .lean_string_isprefixof, v, w => (String.isPrefixOf v w)
  | _, _, _, .lean_string_dropright, v, w => ((String.dropEnd v w).toString)
  | _, _, .lean_substring_takewhile => ...nothing
  | _, _, _, .lean_substring_get, v, w => (Substring.Raw.get v w)
  | _, _, _, .lean_string_uget_byte_fast, v, w => ((String.toUTF8 v)[w.toNat]!) -- TODO: use ugetUTF8Byte, but its dependent
  | _, _, _, .lean_string_contains, v, w => (String.contains v w)
  | _, _, .lean_string_front, v => (String.Internal.front v)
  | _, _, _, .lean_string_posof, v, w => (String.Internal.posOf v w)
  | _, _, .lean_substring_all => ...nothing
  | _, _, .lean_string_intercalate => ...nothing
  | _, _, _, .lean_string_drop, v, w => ((String.drop v w).toString)
  | _, _, .lean_string_length__String_Internal_length => ...nothing
  | _, _, .lean_string_utf8_at_end__String_Internal_atEnd => ...nothing
  | _, _, _, .lean_substring_beq, v, w => (Substring.Raw.beq v w)
  | _, _, .lean_string_nextwhile => ...nothing
  | _, _, .lean_string_utf8_next__String_Internal_next => ...nothing
  | _, _, .lean_string_mk__String_mk => ...nothing
  | _, _, .lean_string_any => ...nothing
  | _, _, _, _, .lean_string_pushn, s, c, n => (String.pushn s c n)
  | _, _, .lean_string_capitalize, v => (String.Internal.capitalize v)
  | _, _, .lean_string_utf8_extract__String_Internal_extract => ...nothing
  | _, _, _, .lean_string_pos_min, v, w => (min v w)
  | _, _, .lean_substring_front, v => (Substring.Raw.Internal.front v)
  | _, _, _, .lean_string_pos_sub, v, w => (String.Pos.Raw.Internal.sub v w)
  | _, _, .lean_substring_isempty, v => (Substring.Raw.Internal.isEmpty v)
  | _, _, _, .lean_string_offsetofpos, v, w => (String.Pos.Raw.offsetOfPos v w)
  ----------------------
  -- Init/Data/Repr.lean
  ----------------------
  | _, _, .lean_string_of_usize, v => (USize.repr (UInt64.toUSize v))
  -----------------
  -- Init/Util.lean
  -----------------
  | _, _, .lean_dbg_sleep => ...nothing
  | _, _, .lean_ptr_addr => ...nothing
  | _, _, .lean_dbg_trace => ...nothing
  | _, _, .lean_dbg_trace_if_shared => ...nothing
  | _, _, .lean_dbg_stack_trace => ...nothing
  | _, _, .lean_is_exclusive_obj => ...nothing
  ---------------------------
  -- Init/Data/Array/Set.lean
  ---------------------------
  | _, _, .lean_array_set => ...nothing
  | _, _, .lean_array_fset => ...nothing
  -----------------------------
  -- Init/Data/Array/Basic.lean
  -----------------------------
  | _, _, .lean_array_fswap => ...nothing
  | _, _, .lean_array_uget => ...nothing
  | _, _, .lean_mk_array => ...nothing
  | _, _, .lean_array_swap => ...nothing
  | _, _, .lean_array_uget_borrowed => ...nothing
  | _, _, .lean_array_pop => ...nothing
  | _, _, .lean_array_uset => ...nothing
  | _, _, .lean_array_size => ...nothing
  ----------------------
  -- Init/Meta/Defs.lean
  ----------------------
  | _, lean_version_get_special_desc          : LeanInitPureExtern_U_T .string -- always "leanscript"
  | _, lean_version_get_is_release            : LeanInitPureExtern_U_T .bool -- always false
  | _, lean_version_get_major                 : LeanInitPureExtern_U_T .nat -- always 0
  | _, lean_version_get_patch                 : LeanInitPureExtern_U_T .nat -- always 0
  | _, lean_internal_is_stage0                : LeanInitPureExtern_U_T .bool -- always false
  | _, lean_version_get_minor                 : LeanInitPureExtern_U_T .nat -- always 0
  | _, lean_get_githash                       : LeanInitPureExtern_U_T .string -- always "leanscript"
  | _, lean_internal_has_llvm_backend         : LeanInitPureExtern_U_T .bool -- always false
  --------------------------
  -- Init/Data/Nat/Log2.lean
  --------------------------
  | _, _, .lean_nat_log2 => ...nothing
  ----------------------------------
  -- Init/Data/Int/DivMod/Basic.lean
  ----------------------------------
  | _, _, _, .lean_int_emod, v, w => (Int.emod v w)
  | _, _, _, .lean_int_div_exact, v, w => (Int.tdiv v w)
  | _, _, _, .lean_int_mod, v, w => (Int.tmod v w)
  | _, _, _, .lean_int_ediv, v, w => (Int.ediv v w)
  | _, _, _, .lean_int_div, v, w => (Int.tdiv v w)
  -------------------------
  -- Init/Data/Nat/Gcd.lean
  -------------------------
  | _, _, .lean_nat_gcd__Nat_gcd__unary => ...nothing
  | _, _, .lean_nat_gcd__Nat_gcd => ...nothing
  ----------------------------
  -- Init/Data/UInt/Basic.lean
  ----------------------------
  | _, _, _, .lean_uint64_shift_left, v, w => (v <<< w)
  | _, _, _, .lean_uint32_mod, v, w => (v % w)
  | _, _, .lean_uint16_neg, v => (UInt16.neg v)
  | _, _, _, .lean_usize_land, v, w => (v &&& w)
  | _, _, _, .lean_usize_mul, v, w => (v * w)
  | _, _, .lean_uint16_to_usize, v => (UInt16.toUInt64 v)
  | _, _, _, .lean_uint64_shift_right, v, w => (v >>> w)
  | _, _, _, .lean_usize_shift_left, v, w => (v <<< w)
  | _, _, _, .lean_uint16_add, v, w => (v + w)
  | _, _, _, .lean_usize_xor, v, w => (v ^^^ w)
  | _, _, .lean_uint64_complement, v => (UInt64.complement v)
  | _, _, .lean_bool_to_uint32, v => (Bool.toUInt32 v)
  | _, _, _, .lean_uint16_lor, v, w => (v ||| w)
  | _, _, _, .lean_uint16_mul, v, w => (v * w)
  | _, _, _, .lean_uint16_land, v, w => (v &&& w)
  | _, _, _, .lean_uint8_sub, v, w => (v - w)
  | _, _, _, .lean_uint32_div, v, w => (v / w)
  | _, _, _, .lean_uint64_add, v, w => (v + w)
  | _, _, .lean_uint8_neg, v => (UInt8.neg v)
  | _, _, .lean_uint16_complement, v => (UInt16.complement v)
  | _, _, _, .lean_uint64_lor, v, w => (v ||| w)
  | _, _, _, .lean_uint64_mod, v, w => (v % w)
  | _, _, _, .lean_uint8_lor, v, w => (v ||| w)
  | _, _, _, .lean_uint32_shift_right, v, w => (v >>> w)
  | _, _, _, .lean_uint16_xor, v, w => (v ^^^ w)
  | _, _, _, .lean_usize_lor, v, w => (v ||| w)
  | _, _, _, .lean_uint8_div, v, w => (v / w)
  | _, _, _, .lean_uint16_shift_left, v, w => (v <<< w)
  | _, _, .lean_uint32_neg, v => (UInt32.neg v)
  | _, _, _, .lean_uint16_mod, v, w => (v % w)
  | _, _, .lean_usize_neg, v => (UInt64.neg v)
  | _, _, _, .lean_uint64_div, v, w => (v / w)
  | _, _, _, .lean_uint16_dec_lt, v, w => (decide (v < w))
  | _, _, _, .lean_uint8_shift_right, v, w => (v >>> w)
  | _, _, .lean_usize_to_uint64, v => v
  | _, _, _, .lean_uint32_lor, v, w => (v ||| w)
  | _, _, _, .lean_uint64_mul, v, w => (v * w)
  | _, _, _, .lean_usize_shift_right, v, w => (v >>> w)
  | _, _, _, .lean_uint64_land, v, w => (v &&& w)
  | _, _, _, .lean_uint8_shift_left, v, w => (v <<< w)
  | _, _, _, .lean_uint16_div, v, w => (v / w)
  | _, _, .lean_bool_to_uint64, v => (Bool.toUInt64 v)
  | _, _, _, .lean_uint8_land, v, w => (v &&& w)
  | _, _, _, .lean_uint64_dec_le, v, w => (decide (v ≤ w))
  | _, _, _, .lean_uint8_mul, v, w => (v * w)
  | _, _, .lean_usize_of_nat__USize_ofNat32 => ...nothing
  | _, _, _, .lean_uint64_sub, v, w => (v - w)
  | _, _, .lean_uint64_neg, v => (UInt64.neg v)
  | _, _, _, .lean_uint8_add, v, w => (v + w)
  | _, _, _, .lean_usize_div, v, w => (v / w)
  | _, _, .lean_uint32_to_usize, v => (UInt32.toUInt64 v)
  | _, _, .lean_uint8_complement, v => (UInt8.complement v)
  | _, _, .lean_usize_to_uint16, v => (UInt64.toUInt16 v)
  | _, _, _, .lean_uint32_xor, v, w => (v ^^^ w)
  | _, _, _, .lean_uint16_dec_le, v, w => (decide (v ≤ w))
  | _, _, .lean_usize_to_uint8, v => (UInt64.toUInt8 v)
  | _, _, _, .lean_uint32_shift_left, v, w => (v <<< w)
  | _, _, _, .lean_uint16_sub, v, w => (v - w)
  | _, _, _, .lean_uint32_mul, v, w => (v * w)
  | _, _, _, .lean_uint32_land, v, w => (v &&& w)
  | _, _, _, .lean_usize_mod, v, w => (v % w)
  | _, _, _, .lean_uint8_mod, v, w => (v % w)
  | _, _, _, .lean_uint64_dec_lt, v, w => (decide (v < w))
  | _, _, .lean_bool_to_uint8, v => (Bool.toUInt8 v)
  | _, _, .lean_uint32_complement, v => (UInt32.complement v)
  | _, _, .lean_uint8_to_usize, v => (UInt8.toUInt64 v)
  | _, _, .lean_bool_to_uint16, v => (Bool.toUInt16 v)
  | _, _, _, .lean_uint8_xor, v, w => (v ^^^ w)
  | _, _, .lean_bool_to_usize, v => (Bool.toUInt64 v)
  | _, _, .lean_uint64_to_usize, v => v
  | _, _, _, .lean_uint16_shift_right, v, w => (v >>> w)
  | _, _, .lean_usize_to_uint32, v => (UInt64.toUInt32 v)
  | _, _, .lean_usize_complement, v => (UInt64.complement v)
  | _, _, _, .lean_uint64_xor, v, w => (v ^^^ w)
  ---------------------------------
  -- Init/Data/ByteArray/Basic.lean
  ---------------------------------
  | _, _, .lean_byte_array_copy_slice => ...nothing
  | _, _, .lean_byte_array_hash => ...nothing
  | _, _, .lean_sarray_size__ByteArray_usize => ...nothing
  | _, _, .lean_sarray_dec_eq__ByteArray_beq => ...nothing
  | _, _, .lean_sarray_dec_eq__ByteArray_decEq => ...nothing
  | _, _, .lean_byte_array_set => ...nothing
  | _, _, .lean_byte_array_fget => ...nothing
  | _, _, .lean_byte_array_uset => ...nothing
  | _, _, .lean_byte_array_fset => ...nothing
  | _, _, .lean_byte_array_uget => ...nothing
  | _, _, .lean_byte_array_get => ...nothing
  -------------------------------
  -- Init/Data/String/PosRaw.lean
  -------------------------------
  | _, _, .lean_string_get_byte_fast__String_getUtf8Byte => ...nothing
  | _, _, .lean_string_get_byte_fast__String_getUTF8Byte => ...nothing
  -----------------------------
  -- Init/Data/String/Defs.lean
  -----------------------------
  | _, _, .lean_string_to_utf8__String_toUTF8 => ...nothing
  | _, _, .lean_string_append__String_append => ...nothing
  ----------------------------
  -- Init/System/Platform.lean
  ----------------------------
  | _, _, .lean_internal_get_hardware_concurrency => ...nothing
  | _, _, .lean_system_platform_linux => ...nothing
  | _, lean_system_platform_emscripten        : LeanInitPureExtern_U_T .bool -- always false
  | _, lean_system_platform_target            : LeanInitPureExtern_U_T .string -- always "nodeorbrowser"
  | _, _, .lean_system_platform_windows => ...nothing
  | _, _, .lean_system_platform_osx => ...nothing
  ------------------------------
  -- Init/Data/String/Basic.lean
  ------------------------------
  | _, _, .lean_string_utf8_next__String_next => ...nothing
  | _, _, .lean_string_utf8_next__String_Pos_Raw_next => ...nothing
  | _, _, .lean_string_utf8_get__String_Pos_Raw_get => ...nothing
  | _, _, .lean_string_utf8_get__String_get => ...nothing
  | _, _, .lean_string_utf8_prev__String_Pos_Raw_prev => ...nothing
  | _, _, .lean_string_utf8_prev__String_prev => ...nothing
  | _, _, .lean_string_utf8_next_fast__String_Pos_next => ...nothing
  | _, _, .lean_string_data__String_data => ...nothing
  | _, _, .lean_string_data__String_toList => ...nothing
  | _, _, _, _, .lean_string_utf8_extract_fast, s, i, j => (String.Pos.Raw.extract s ⟨i⟩ ⟨j⟩)
  | _, _, .lean_string_utf8_at_end__String_atEnd => ...nothing
  | _, _, .lean_string_utf8_at_end__String_Pos_Raw_atEnd => ...nothing
  | _, _, .lean_string_utf8_get_fast__String_decodeChar => ...nothing
  | _, _, _, .lean_string_is_valid_pos, v, w => (String.Pos.Raw.isValid v w)
  | _, _, _, .lean_string_dec_lt, v, w => (decide (v < w))
  | _, _, .lean_string_validate_utf8 => ...nothing
  | _, _, .lean_string_utf8_extract__String_Pos_Raw_extract => ...nothing
  -------------------------------
  -- Init/Data/String/Length.lean
  -------------------------------
  | _, _, .lean_string_length__String_length => ...nothing
  ----------------------------
  -- Init/Data/SInt/Basic.lean
  ----------------------------
  | _, _, .lean_isize_complement, v => (Int64.complement v)
  | _, _, _, .lean_int8_add, v, w => (v + w)
  | _, _, .lean_int16_of_nat, v => (Int16.ofNat v)
  | _, _, _, .lean_int16_dec_le, v, w => (decide (v ≤ w))
  | _, _, .lean_int32_of_int, v => (Int32.ofInt v)
  | _, _, .lean_int64_to_isize, v => v
  | _, _, _, .lean_int32_land, v, w => (v &&& w)
  | _, _, _, .lean_int8_div, v, w => (v / w)
  | _, _, _, .lean_int32_mul, v, w => (v * w)
  | _, _, _, .lean_int64_sub, v, w => (v - w)
  | _, _, _, .lean_int16_shift_right, v, w => (v >>> w)
  | _, _, .lean_isize_to_int8, v => (Int64.toInt8 v)
  | _, _, _, .lean_int64_xor, v, w => (v ^^^ w)
  | _, _, _, .lean_int32_dec_le, v, w => (decide (v ≤ w))
  | _, _, .lean_int32_of_nat, v => (Int32.ofNat v)
  | _, _, _, .lean_isize_xor, v, w => (v ^^^ w)
  | _, _, .lean_int64_to_int8, v => (Int64.toInt8 v)
  | _, _, _, .lean_isize_shift_left, v, w => (v <<< w)
  | _, _, _, .lean_int64_mul, v, w => (v * w)
  | _, _, .lean_int32_to_int64, v => (Int32.toInt64 v)
  | _, _, .lean_int8_to_int16, v => (Int8.toInt16 v)
  | _, _, _, .lean_int32_sub, v, w => (v - w)
  | _, _, .lean_int64_of_int, v => (Int64.ofInt v)
  | _, _, .lean_int32_to_isize, v => (Int32.toInt64 v)
  | _, _, _, .lean_int64_land, v, w => (v &&& w)
  | _, _, _, .lean_int8_shift_right, v, w => (v >>> w)
  | _, _, _, .lean_int64_lor, v, w => (v ||| w)
  | _, _, _, .lean_int16_div, v, w => (v / w)
  | _, _, _, .lean_isize_mod, v, w => (v % w)
  | _, _, .lean_int32_neg, v => (Int32.neg v)
  | _, _, _, .lean_int8_mod, v, w => (v % w)
  | _, _, .lean_int32_abs, v => (Int32.abs v)
  | _, _, .lean_bool_to_int8, v => (Bool.toInt8 v)
  | _, _, _, .lean_isize_shift_right, v, w => (v >>> w)
  | _, _, .lean_isize_to_int16, v => (Int64.toInt16 v)
  | _, _, _, .lean_int8_shift_left, v, w => (v <<< w)
  | _, _, _, .lean_int16_dec_lt, v, w => (decide (v < w))
  | _, _, _, .lean_int8_xor, v, w => (v ^^^ w)
  | _, _, _, .lean_int32_dec_eq, v, w => (v == w)
  | _, _, .lean_int16_to_int, v => (Int16.toInt v)
  | _, _, _, .lean_int16_mod, v, w => (v % w)
  | _, _, _, .lean_isize_div, v, w => (v / w)
  | _, _, _, .lean_int16_dec_eq, v, w => (v == w)
  | _, _, .lean_int8_complement, v => (Int8.complement v)
  | _, _, _, .lean_isize_add, v, w => (v + w)
  | _, _, .lean_bool_to_int16, v => (Bool.toInt16 v)
  | _, _, _, .lean_int32_dec_lt, v, w => (decide (v < w))
  | _, _, _, .lean_isize_lor, v, w => (v ||| w)
  | _, _, _, .lean_int64_mod, v, w => (v % w)
  | _, _, .lean_isize_of_int, v => (Int64.ofInt v)
  | _, _, _, .lean_int64_shift_left, v, w => (v <<< w)
  | _, _, .lean_int16_abs, v => (Int16.abs v)
  | _, _, _, .lean_isize_land, v, w => (v &&& w)
  | _, _, .lean_int16_to_int32, v => (Int16.toInt32 v)
  | _, _, _, .lean_isize_mul, v, w => (v * w)
  | _, _, .lean_isize_to_int, v => (Int64.toInt v)
  | _, _, _, .lean_int64_dec_lt, v, w => (decide (v < w))
  | _, _, _, .lean_isize_dec_le, v, w => (decide (v ≤ w))
  | _, _, _, .lean_int8_dec_eq, v, w => (v == w)
  | _, _, _, .lean_int32_xor, v, w => (v ^^^ w)
  | _, _, .lean_isize_of_nat, v => (Int64.ofNat v)
  | _, _, .lean_int16_complement, v => (Int16.complement v)
  | _, _, _, .lean_int32_shift_left, v, w => (v <<< w)
  | _, _, .lean_isize_to_int64, v => v
  | _, _, _, .lean_isize_sub, v, w => (v - w)
  | _, _, .lean_int64_complement, v => (Int64.complement v)
  | _, _, .lean_isize_abs, v => (Int64.abs v)
  | _, _, _, .lean_int16_land, v, w => (v &&& w)
  | _, _, .lean_int16_of_int, v => (Int16.ofInt v)
  | _, _, _, .lean_int32_shift_right, v, w => (v >>> w)
  | _, _, .lean_int8_neg, v => (Int8.neg v)
  | _, _, _, .lean_int16_mul, v, w => (v * w)
  | _, _, .lean_isize_to_int32, v => (Int64.toInt32 v)
  | _, _, .lean_int64_to_int32, v => (Int64.toInt32 v)
  | _, _, _, .lean_int16_shift_left, v, w => (v <<< w)
  | _, _, .lean_int64_abs, v => (Int64.abs v)
  | _, _, .lean_int32_complement, v => (Int32.complement v)
  | _, _, _, .lean_int16_xor, v, w => (v ^^^ w)
  | _, _, .lean_bool_to_int64, v => (Bool.toInt64 v)
  | _, _, .lean_bool_to_isize, v => (Bool.toInt64 v)
  | _, _, _, .lean_int8_dec_lt, v, w => (decide (v < w))
  | _, _, _, .lean_int64_dec_eq, v, w => (v == w)
  | _, _, _, .lean_int64_dec_le, v, w => (decide (v ≤ w))
  | _, _, .lean_bool_to_int32, v => (Bool.toInt32 v)
  | _, _, .lean_int64_of_nat, v => (Int64.ofNat v)
  | _, _, .lean_int32_to_int8, v => (Int32.toInt8 v)
  | _, _, .lean_int64_to_int_sint, v => (Int64.toInt v)
  | _, _, _, .lean_int32_add, v, w => (v + w)
  | _, _, _, .lean_isize_dec_lt, v, w => (decide (v < w))
  | _, _, .lean_int64_neg, v => (Int64.neg v)
  | _, _, _, .lean_int32_lor, v, w => (v ||| w)
  | _, _, .lean_int8_abs, v => (Int8.abs v)
  | _, _, .lean_int8_to_int32, v => (Int8.toInt32 v)
  | _, _, _, .lean_int32_mod, v, w => (v % w)
  | _, _, .lean_isize_neg, v => (Int64.neg v)
  | _, _, .lean_int32_to_int, v => (Int32.toInt v)
  | _, _, _, .lean_int64_add, v, w => (v + w)
  | _, _, _, .lean_int8_sub, v, w => (v - w)
  | _, _, .lean_int32_to_int16, v => (Int32.toInt16 v)
  | _, _, .lean_int8_to_int64, v => (Int8.toInt64 v)
  | _, _, _, .lean_int16_lor, v, w => (v ||| w)
  | _, _, _, .lean_int64_div, v, w => (v / w)
  | _, _, .lean_int8_to_isize, v => (Int8.toInt64 v)
  | _, _, _, .lean_isize_dec_eq, v, w => (v == w)
  | _, _, _, .lean_int16_add, v, w => (v + w)
  | _, _, .lean_int8_of_nat, v => (Int8.ofNat v)
  | _, _, _, .lean_int8_dec_le, v, w => (decide (v ≤ w))
  | _, _, .lean_int16_to_int8, v => (Int16.toInt8 v)
  | _, _, .lean_int8_to_int, v => (Int8.toInt v)
  | _, _, _, .lean_int8_mul, v, w => (v * w)
  | _, _, .lean_int16_neg, v => (Int16.neg v)
  | _, _, .lean_int64_to_int16, v => (Int64.toInt16 v)
  | _, _, _, .lean_int8_land, v, w => (v &&& w)
  | _, _, _, .lean_int32_div, v, w => (v / w)
  | _, _, .lean_int8_of_int, v => (Int8.ofInt v)
  | _, _, .lean_int16_to_isize, v => (Int16.toInt64 v)
  | _, _, _, .lean_int16_sub, v, w => (v - w)
  | _, _, .lean_int16_to_int64, v => (Int16.toInt64 v)
  | _, _, _, .lean_int8_lor, v, w => (v ||| w)
  | _, _, _, .lean_int64_shift_right, v, w => (v >>> w)
  --------------------------------------
  -- Init/Data/String/Pattern/Basic.lean
  --------------------------------------
  | _, _, _, _, _, _, .lean_string_memcmp, s1, s2, p1, p2, len => String.Slice.Pattern.Internal.memcmpStr --TODO should use

  ------------------------------
  -- Init/Data/String/Slice.lean
  ------------------------------
  | _, _, _, .lean_slice_dec_lt, v, w => (v < w)
  | _, _, .lean_slice_hash, v => (String.Slice.hash v)
  -------------------------------
  -- Init/Data/String/Modify.lean
  -------------------------------
  | _, _, .lean_string_utf8_set__String_Pos_Raw_set => ...nothing
  | _, _, .lean_string_utf8_set__String_Pos_set => ...nothing
  | _, _, .lean_string_utf8_set__String_set => ...nothing
  -----------------------------
  -- Init/Data/Float/Float.lean
  -----------------------------
  | _, _, .lean_float_frexp => ...nothing
  | _, _, .lean_uint8_to_float, v => (UInt8.toFloat v)
  | _, _, .lean_float_to_bits__Float_toModel => ...nothing
  | _, _, .lean_float_to_bits__Float_toBits => ...nothing
  | _, _, .lean_float_of_bits__Float_ofBits => ...nothing
  | _, _, .lean_float_of_bits__Float_ofModel => ...nothing
  | _, _, .lean_float_isnan, v => (Float.isNaN v)
  | _, _, .log10, v => (Float.log10 v)
  | _, _, .cbrt, v => (Float.cbrt v)
  | _, _, .cbrtf, v => (Float32.cbrt v)
  | _, _, .log, v => (Float.log v)
  | _, _, _, .lean_float_div, v, w => (v / w)
  | _, _, _, .lean_float_beq, v, w => (v == w)
  | _, _, .tan, v => (Float.tan v)
  | _, _, .tanh, v => (Float.tanh v)
  | _, _, .exp2, v => (Float.exp2 v)
  | _, _, .lean_float_to_uint16, v => (Float.toUInt16 v)
  | _, _, .lean_uint32_to_float, v => (UInt32.toFloat v)
  | _, _, .lean_float_decLe__Float_decLe => ...nothing
  | _, _, .lean_float_decLe__Float_le => ...nothing
  | _, _, .lean_float_to_uint64, v => (Float.toUInt64 v)
  | _, _, .sqrt, v => (Float.sqrt v)
  | _, _, .sqrtf, v => (Float32.sqrt v)
  | _, _, .acos, v => (Float.acos v)
  | _, _, .acosf, v => (Float32.acos v)
  | _, _, .atan, v => (Float.atan v)
  | _, _, .atanf, v => (Float32.atan v)
  | _, _, .acosh, v => (Float.acosh v)
  | _, _, .acoshf, v => (Float32.acosh v)
  | _, _, .floor, v => (Float.floor v)
  | _, _, .floorf, v => (Float32.floor v)
  | _, _, .fabs, v => (Float.abs v)
  | _, _, .lean_float_to_uint32, v => (Float.toUInt32 v)
  | _, _, .lean_float_to_string, v => (Float.toString v)
  | _, _, .lean_uint64_to_float, v => (UInt64.toFloat v)
  | _, _, .lean_float_decLt__Float_decLt => ...nothing
  | _, _, .lean_float_decLt__Float_lt => ...nothing
  | _, _, .lean_float_to_uint8, v => (Float.toUInt8 v)
  | _, _, .sin, v => (Float.sin v)
  | _, _, .lean_usize_to_float, v => (UInt64.toFloat v)
  | _, _, .cosh, v => (Float.cosh v)
  | _, _, .exp, v => (Float.exp v)
  | _, _, .expf, v => (Float32.exp v)
  | _, _, .ceil, v => (Float.ceil v)
  | _, _, .lean_float_to_usize, v => (Float.toUInt64 v)
  | _, _, .lean_float_isfinite, v => (Float.isFinite v)
  | _, _, .round, v => (Float.round v)
  | _, _, .cos, v => (Float.cos v)
  | _, _, .cosf, v => (Float32.cos v)
  | _, _, .lean_nat_log2, v => (Nat.log2 v)
  | _, _, .log2, v => (Float.log2 v)
  | _, _, .lean_usize_log2, v => (UInt64.log2 v)
  | _, _, .lean_uint16_log2, v => (UInt16.log2 v)
  | _, _, .lean_uint64_log2, v => (UInt64.log2 v)
  | _, _, .lean_uint8_log2, v => (UInt8.log2 v)
  | _, _, .lean_uint32_log2, v => (UInt32.log2 v)
  | _, _, .log2f, v => (Float32.log2 v)
  | _, _, .atanh, v => (Float.atanh v)
  | _, _, _, .atan2, v, w => (Float.atan2 v w)
  | _, _, .sinh, v => (Float.sinh v)
  | _, _, .sinhf, v => (Float32.sinh v)
  | _, _, .asinh, v => (Float.asinh v)
  | _, _, .asinhf, v => (Float32.asinh v)
  | _, _, _, .lean_float_mul, v, w => (v * w)
  | _, _, .lean_uint16_to_float, v => (UInt16.toFloat v)
  | _, _, .asin, v => (Float.asin v)
  | _, _, .asinf, v => (Float32.asin v)
  | _, _, _, .pow, v, w => (Float.pow v w)
  | _, _, _, .lean_float_scaleb, v, w => (Float.scaleB v (Int64.toInt w))
  | _, _, _, .lean_float_add, v, w => (v + w)
  | _, _, _, .lean_float_sub, v, w => (v - w)
  | _, _, .lean_float_negate, v => (Float.neg v)
  | _, _, .lean_float_isinf, v => (Float.isInf v)
  ----------------------------------
  -- Init/Data/FloatArray/Basic.lean
  ----------------------------------
  | _, _, .lean_mk_empty_float_array => ...nothing
  | _, _, .lean_float_array_get => ...nothing
  | _, _, .lean_float_array_uget => ...nothing
  | _, _, .lean_float_array_fset => ...nothing
  | _, _, .lean_float_array_uset => ...nothing
  | _, _, .lean_float_array_fget => ...nothing
  | _, _, .lean_float_array_set => ...nothing
  | _, _, .lean_float_array_data => ...nothing
  | _, _, .lean_sarray_size__FloatArray_usize => ...nothing
  | _, _, .lean_float_array_mk => ...nothing
  | _, _, .lean_float_array_size => ...nothing
  | _, _, .lean_float_array_push => ...nothing
  ---------------------------
  -- Init/Data/UInt/Log2.lean
  ---------------------------
  | _, _, .lean_usize_log2 => ...nothing
  | _, _, .lean_uint16_log2 => ...nothing
  | _, _, .lean_uint64_log2 => ...nothing
  | _, _, .lean_uint8_log2 => ...nothing
  | _, _, .lean_uint32_log2 => ...nothing
  ----------------------------
  -- Init/Data/SInt/Float.lean
  ----------------------------
  | _, _, .lean_int32_to_float, v => (Int32.toFloat v)
  | _, _, .lean_float_to_int16, v => (Float.toInt16 v)
  | _, _, .lean_int16_to_float, v => (Int16.toFloat v)
  | _, _, .lean_float_to_int32, v => (Float.toInt32 v)
  | _, _, .lean_isize_to_float, v => (Int64.toFloat v)
  | _, _, .lean_int8_to_float, v => (Int8.toFloat v)
  | _, _, .lean_float_to_int8, v => (Float.toInt8 v)
  | _, _, .lean_int64_to_float, v => (Int64.toFloat v)
  | _, _, .lean_float_to_int64, v => (Float.toInt64 v)
  | _, _, .lean_float_to_isize, v => (Float.toInt64 v)
  -------------------------------
  -- Init/Data/Float/Float32.lean
  -------------------------------
  | _, _, .tanhf, v => (Float32.tanh v)
  | _, _, .exp2f, v => (Float32.exp2 v)
  | _, _, _, .lean_float32_div, v, w => (v / w)
  | _, _, .logf, v => (Float32.log v)
  | _, _, .lean_float32_decLe__Float32_le => ...nothing
  | _, _, .lean_float32_decLe__Float32_decLe => ...nothing
  | _, _, .lean_float_to_float32, v => (Float.toFloat32 v)
  | _, _, .lean_float32_to_bits__Float32_toModel => ...nothing
  | _, _, .lean_float32_to_bits__Float32_toBits => ...nothing
  | _, _, .lean_float32_of_bits__Float32_ofBits => ...nothing
  | _, _, .lean_float32_of_bits__Float32_ofModel => ...nothing
  | _, _, .atanf => ...nothing
  | _, _, .acoshf => ...nothing
  | _, _, .lean_float32_frexp => ...nothing
  | _, _, .lean_float32_to_uint64, v => (Float32.toUInt64 v)
  | _, _, _, .lean_float32_sub, v, w => (v - w)
  | _, _, .lean_float32_to_uint16, v => (Float32.toUInt16 v)
  | _, _, .lean_usize_to_float32, v => (UInt64.toFloat32 v)
  | _, _, .asinf => ...nothing
  | _, _, _, .powf, v, w => (Float32.pow v w)
  | _, _, _, .lean_float32_beq, v, w => (v == w)
  | _, _, .lean_uint8_to_float32, v => (UInt8.toFloat32 v)
  | _, _, .tanf, v => (Float32.tan v)
  | _, _, .lean_float32_to_float, v => (Float32.toFloat v)
  | _, _, .lean_float32_isnan, v => (Float32.isNaN v)
  | _, _, .log10f, v => (Float32.log10 v)
  | _, _, .cbrtf => ...nothing
  | _, _, _, .atan2f, v, w => (Float32.atan2 v w)
  | _, _, .sinhf => ...nothing
  | _, _, .cosf => ...nothing
  | _, _, .lean_uint32_to_float32, v => (UInt32.toFloat32 v)
  | _, _, .lean_float32_isinf, v => (Float32.isInf v)
  | _, _, .lean_float32_negate, v => (Float32.neg v)
  | _, _, .lean_float32_to_usize, v => (Float32.toUInt64 v)
  | _, _, .ceilf, v => (Float32.ceil v)
  | _, _, .lean_float32_isfinite, v => (Float32.isFinite v)
  | _, _, _, .lean_float32_add, v, w => (v + w)
  | _, _, _, .lean_float32_scaleb, v, w => (Float32.scaleB v (Int64.toInt w))
  | _, _, .sinf, v => (Float32.sin v)
  | _, _, _, .lean_float32_mul, v, w => (v * w)
  | _, _, .lean_float32_to_string, v => (Float32.toString v)
  | _, _, .asinhf => ...nothing
  | _, _, .lean_float32_to_uint32, v => (Float32.toUInt32 v)
  | _, _, .log2f => ...nothing
  | _, _, .lean_uint64_to_float32, v => (UInt64.toFloat32 v)
  | _, _, .atanhf, v => (Float32.atanh v)
  | _, _, .floorf => ...nothing
  | _, _, .fabsf, v => (Float32.abs v)
  | _, _, .roundf, v => (Float32.round v)
  | _, _, .lean_float32_decLt__Float32_lt => ...nothing
  | _, _, .lean_float32_decLt__Float32_decLt => ...nothing
  | _, _, .acosf => ...nothing
  | _, _, .sqrtf => ...nothing
  | _, _, .lean_uint16_to_float32, v => (UInt16.toFloat32 v)
  | _, _, .coshf, v => (Float32.cosh v)
  | _, _, .expf => ...nothing
  | _, _, .lean_float32_to_uint8, v => (Float32.toUInt8 v)
  ------------------------------
  -- Init/Data/SInt/Float32.lean
  ------------------------------
  | _, _, .lean_float32_to_int64, v => (Float32.toInt64 v)
  | _, _, .lean_float32_to_isize, v => (Float32.toInt64 v)
  | _, _, .lean_int32_to_float32, v => (Int32.toFloat32 v)
  | _, _, .lean_float32_to_int8, v => (Float32.toInt8 v)
  | _, _, .lean_float32_to_int16, v => (Float32.toInt16 v)
  | _, _, .lean_isize_to_float32, v => (Int64.toFloat32 v)
  | _, _, .lean_int8_to_float32, v => (Int8.toFloat32 v)
  | _, _, .lean_float32_to_int32, v => (Float32.toInt32 v)
  | _, _, .lean_int16_to_float32, v => (Int16.toFloat32 v)
  | _, _, .lean_int64_to_float32, v => (Int64.toFloat32 v)
  ----------------------------
  -- Init/Data/Ord/String.lean
  ----------------------------
  | _, _, .lean_string_compare => ...nothing
  ----------------------
  -- Init/System/IO.lean
  ----------------------
  | _, _, .lean_io_process_child_pid => ...nothing
  ---------------------------
  -- Init/System/Promise.lean
  ---------------------------
  | _, _, .lean_io_promise_result_opt => ...nothing
  | _, _, .lean_option_get_or_block => ...nothing
  ------------------------
  -- Init/ShareCommon.lean
  ------------------------
  | _, _, .lean_sharecommon_quick => ...nothing
  | _, _, .lean_state_sharecommon => ...nothing
  | _, _, .lean_sharecommon_eq => ...nothing
  | _, _, .lean_sharecommon_hash => ...nothing
  ------------------------------------------------------------
  -- Unmatched (in LeanInitPureExternsEval but not PureExterns)
  ------------------------------------------------------------
  | _, _, .lean_uint32_of_nat_lt, v => (UInt32.ofNat v)
  | _, _, .lean_char_of_nat_aux, v => (Char.ofNat v)
  | _, _, .lean_uint8_to_bitvec, v => (UInt8.toBitVec v)
  | _, _, .lean_uint8_of_nat, v => (UInt8.ofNat v)
  | _, _, .lean_uint8_of_nat_lt, v => (UInt8.ofNat v)
  | _, _, .lean_uint16_to_bitvec, v => (UInt16.toBitVec v)
  | _, _, .lean_usize_of_nat_lt, v => (UInt64.ofNat v)
  | _, _, .lean_uint64_to_bitvec, v => (UInt64.toBitVec v)
  | _, _, .lean_uint32_to_nat, v => (UInt32.toNat v)
  | _, _, .lean_uint32_to_bitvec, v => (UInt32.toBitVec v)
  | _, _, .lean_uint16_of_nat_lt, v => (UInt16.ofNat v)
  | _, _, .lean_usize_to_bitvec, v => (UInt64.toBitVec v)
  | _, _, .lean_uint64_of_nat_lt, v => (UInt64.ofNat v)
  | _, _, .lean_int_to_nat, v => (Int.toNat v)
  | _, _, .lean_uint64_to_nat, v => (UInt64.toNat v)
  | _, _, .lean_usize_to_nat, v => (UInt64.toNat v)
  | _, _, .lean_uint32_of_nat, v => (UInt32.ofNat v)
  | _, _, .lean_uint16_to_nat, v => (UInt16.toNat v)
  | _, _, .lean_usize_of_nat, v => (UInt64.ofNat v)
  | _, _, .lean_uint8_to_nat, v => (UInt8.toNat v)
  | _, _, .lean_uint64_of_nat, v => (UInt64.ofNat v)
  | _, _, .lean_uint16_of_nat, v => (UInt16.ofNat v)
  | _, _, .lean_string_length, v => (String.Internal.length v)
  | _, _, .lean_usize_of_nat32, v => (UInt64.ofNat v)
  | _, _, .lean_string_length_def, v => (String.length v)
  | _, _, .lean_float_to_bits, v => (Float.toBits v)
  | _, _, .lean_float_of_bits, v => (Float.ofBits v)
  | _, _, .lean_float32_to_bits, v => (Float32.toBits v)
  | _, _, .lean_float32_of_bits, v => (Float32.ofBits v)
  | _, _, _, .lean_nat_mod_core, v, w => (v % w)
  | _, _, _, .lean_nat_mod, v, w => (v % w)
  | _, _, _, .lean_nat_dec_eq, v, w => (decide (v = w))
  | _, _, _, .lean_nat_beq, v, w => (v == w)
  | _, _, _, .lean_nat_ble, v, w => (decide (v ≤ w))
  | _, _, _, .lean_nat_dec_le, v, w => (decide (v ≤ w))
  | _, _, _, .lean_string_utf8_get, v, w => (String.Pos.Raw.get v w)
  | _, _, _, .lean_string_append, v, w => (v ++ w)
  | _, _, _, .lean_string_utf8_at_end, v, w => (String.Pos.Raw.atEnd v w)
  | _, _, _, .lean_string_utf8_next, v, w => (String.Pos.Raw.next v w)
  | _, _, _, .lean_string_append_defs, v, w => (v ++ w)
  | _, _, _, .lean_string_utf8_next_basic, v, w => (String.Pos.Raw.next v w)
  | _, _, _, .lean_string_pos_raw_next, v, w => (String.Pos.Raw.next v w)
  | _, _, _, .lean_string_pos_raw_get, v, w => (String.Pos.Raw.get v w)
  | _, _, _, .lean_string_get_basic, v, w => (String.Pos.Raw.get v w)
  | _, _, _, .lean_string_pos_raw_prev, v, w => (String.Pos.Raw.prev v w)
  | _, _, _, .lean_string_prev, v, w => (String.Pos.Raw.prev v w)
  | _, _, _, .lean_string_next_fast, v, w => (String.Pos.Raw.next v w)
  | _, _, _, .lean_string_pos_raw_next_fast, v, w => (String.Pos.Raw.next v w)
  | _, _, _, .lean_string_pos_next, v, w => (String.Pos.Raw.next v w)
  | _, _, _, .lean_string_at_end_basic, v, w => (String.Pos.Raw.atEnd v w)
  | _, _, _, .lean_string_pos_raw_at_end, v, w => (String.Pos.Raw.atEnd v w)
  | _, _, _, .lean_string_pos_raw_get_bang, v, w => (String.Pos.Raw.get! v w)
  | _, _, _, .lean_string_get_bang, v, w => (String.Pos.Raw.get! v w)
  | _, _, _, .lean_string_get_fast, v, w => (String.Pos.Raw.get v w)
  | _, _, _, .lean_string_pos_raw_get_fast, v, w => (String.Pos.Raw.get v w)
  | _, _, _, .lean_float_decLe, v, w => (decide (v ≤ w))
  | _, _, _, .lean_float_le, v, w => (decide (v ≤ w))
  | _, _, _, .lean_float_decLt, v, w => (decide (v < w))
  | _, _, _, .lean_float_lt, v, w => (decide (v < w))
  | _, _, _, .lean_float32_le, v, w => (decide (v ≤ w))
  | _, _, _, .lean_float32_decLe, v, w => (decide (v ≤ w))
  | _, _, _, .lean_float32_lt, v, w => (decide (v < w))
  | _, _, _, .lean_float32_decLt, v, w => (decide (v < w))
  | _, _, _, .lean_string_get_byte_fast, v, w => ((String.toUTF8 v)[w]!)
  | _, _, _, _, .lean_string_utf8_extract, s, i, j => (String.Pos.Raw.extract s ⟨i⟩ ⟨j⟩)
  | _, _, _, _, .lean_string_utf8_extract_basic, s, i, j => (String.Pos.Raw.extract s ⟨i⟩ ⟨j⟩)
  | _, _, _, _, .lean_string_pos_raw_set, s, i, c => (String.Pos.Raw.set s ⟨i⟩ c)
  | _, _, _, _, .lean_string_pos_set, s, i, c => (String.Pos.Raw.set s ⟨i⟩ c)
  | _, _, _, _, .lean_string_set, s, i, c => (String.Pos.Raw.set s ⟨i⟩ c)
end LeanScript

end
