module
prelude
public import LeanScript.LeanPrimTy
public import LeanScript.LeanPrimTyCovariant
-- public import Init.Data.FloatArray.Basic
-- public import Init.System.IO
-- public import Init.System.Promise
-- public import Init.ShareCommon
set_option autoImplicit false
@[expose] public section
namespace LeanScript

open LeanPrimTy
open LeanPrimTyCovariant

-- `usize`/`isize` are `uint64`/`int64` in this grammar, so every entry that speaks about
-- one is already covered by the `UInt64`/`Int64` entries and is commented out below.
-- protected abbrev LeanPrimTy.usize : LeanPrimTy := uint64
-- protected abbrev LeanPrimTy.isize : LeanPrimTy := int64
-- protected abbrev USize_size : Nat := UInt64.size
-- protected abbrev LeanPrimTy.byteArray : LeanPrimTyCovariant LeanPrimTy := Array UInt8 -- Though array doesnt have analogues to lean_byte_array_copy_slice, lean_byte_array_hash, lean_sarray_dec_eq, lean_string_validate_utf8, lean_string_from_utf8_unchecked, lean_string_to_utf8, lean_string_utf8_get_fast - we will support them differently
-- protected abbrev LeanPrimTy.floatArray : LeanPrimTyCovariant LeanPrimTy := Array Float

variable {MyTy : Type}
  (denote : MyTy → Type)
  [Coe LeanPrimTy MyTy]
  [Coe (LeanPrimTyCovariant LeanPrimTy) MyTy]
  [Coe (LeanPrimTyCovariant MyTy) MyTy]
  (option : MyTy → MyTy)
  (list : MyTy → MyTy)
  (fn1 : MyTy → MyTy → MyTy)
  (fn2 : MyTy → MyTy → MyTy → MyTy)
  (prod : MyTy → MyTy → MyTy)
  -- the run-time handles are not values, so nothing that speaks about one is listed
  -- (`IO.Promise`, `IO.Process.Child`, `ShareCommon.Object`, `ShareCommon.State`)
  -- (io_promise : MyTy → MyTy)
  -- (io_process_child : IO.Process.StdioConfig → MyTy)
  -- (shareCommon_object : MyTy)
  -- (shareCommon_stateFactory : Type)
  -- (shareCommon_state : shareCommon_stateFactory -> MyTy)
  -- (name : MyTy)  -- no entry of the catalogue answers with a `Lean.Name`
  (ordering : MyTy)
  -- A byte array is `Array UInt8` and a float array is `Array Float`, so neither is a
  -- type former of its own here; the entries that speak about one are commented out
  -- below, and will be supported either through the ordinary array entries or through a
  -- separate API.
  -- (byteArray : MyTy)
  -- (floatArray : MyTy)

inductive LeanInitPureExtern : MyTy → Type where
  --------------------
  -- Init/Prelude.lean
  --------------------
  | lean_uint32_of_nat_mk : BitVec 32 → LeanInitPureExtern uint32 -- UInt32.ofBitVec
  | lean_uint32_dec_eq : UInt32 → UInt32 → LeanInitPureExtern LeanPrimTy.bool -- UInt32.decEq
  -- | lean_byte_array_size : ByteArray → LeanInitPureExtern nat -- ByteArray.size -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  -- | lean_string_to_utf8__String_toByteArray : String → LeanInitPureExtern byteArray -- String.toByteArray -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  | lean_uint32_dec_lt : UInt32 → UInt32 → LeanInitPureExtern LeanPrimTy.bool -- UInt32.decLt
  | lean_nat_div : Nat → Nat → LeanInitPureExtern nat -- Nat.div
  -- | lean_sorry : (αt : MyTy) → Bool → LeanInitPureExtern αt -- sorryAx -- XXX: DONT IMPLEMENT
  | lean_uint32_of_nat__UInt32_ofNatLT : (n : Nat) → (h : n < UInt32.size) → LeanInitPureExtern uint32 -- UInt32.ofNatLT
  | lean_uint32_of_nat__Char_ofNatAux : (n : Nat) → (h : n.isValidChar) → LeanInitPureExtern char -- Char.ofNatAux
  | lean_array_get_borrowed : (αt : MyTy) → (inhabited_default : denote αt) → Array (denote αt) → Nat → LeanInitPureExtern αt -- Array.get!InternalBorrowed
  | lean_uint8_to_nat__UInt8_toBitVec : UInt8 → LeanInitPureExtern (bitvec 8) -- UInt8.toBitVec
  | lean_nat_dec_lt : Nat → Nat → LeanInitPureExtern LeanPrimTy.bool -- Nat.decLt
  -- | lean_string_from_utf8_unchecked : (toByteArray : ByteArray) → toByteArray.IsValidUTF8 → LeanInitPureExtern string -- String.ofByteArray -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  | lean_nat_mod__Nat_modCore : Nat → Nat → LeanInitPureExtern nat -- Nat.modCore
  | lean_nat_mod__Nat_mod : Nat → Nat → LeanInitPureExtern nat -- Nat.mod
  | lean_array_push : (αt : MyTy) → Array (denote αt) → denote αt → LeanInitPureExtern (array αt) -- Array.push
  -- | lean_byte_array_mk : Array UInt8 → LeanInitPureExtern byteArray -- ByteArray.mk -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  | lean_nat_sub : Nat → Nat → LeanInitPureExtern nat -- Nat.sub
  | lean_uint8_dec_lt : UInt8 → UInt8 → LeanInitPureExtern LeanPrimTy.bool -- UInt8.decLt
  -- | lean_byte_array_data : ByteArray → LeanInitPureExtern (array uint8) -- ByteArray.data -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  -- | lean_system_platform_nbits : LeanInitPureExtern (lazy nat) -- System.Platform.getNumBits
  | lean_uint32_dec_le : UInt32 → UInt32 → LeanInitPureExtern LeanPrimTy.bool -- UInt32.decLe
  | lean_array_get_size : (αt : MyTy) → Array (denote αt) → LeanInitPureExtern nat -- Array.size
  | lean_array_to_list : (αt : MyTy) → Array (denote αt) → LeanInitPureExtern (list αt) -- Array.toList
  | lean_nat_dec_eq__Nat_decEq : Nat → Nat → LeanInitPureExtern LeanPrimTy.bool -- Nat.decEq
  | lean_nat_dec_eq__Nat_beq : Nat → Nat → LeanInitPureExtern LeanPrimTy.bool -- Nat.beq
  | lean_array_fget_borrowed : (αt : MyTy) → (a : Array (denote αt)) → (i : Nat) → (h : i < a.size) → LeanInitPureExtern αt -- Array.getInternalBorrowed
  | lean_mk_empty_array_with_capacity__Array_emptyWithCapacity : (αt : MyTy) → Nat → LeanInitPureExtern (array αt) -- Array.emptyWithCapacity
  | lean_mk_empty_array_with_capacity__Array_mkEmpty : (αt : MyTy) → Nat → LeanInitPureExtern (array αt) -- Array.mkEmpty
  | lean_uint8_of_nat__UInt8_ofNat : Nat → LeanInitPureExtern uint8 -- UInt8.ofNat
  | lean_uint8_of_nat__UInt8_ofNatLT : (n : Nat) → (h : n < UInt8.size) → LeanInitPureExtern uint8 -- UInt8.ofNatLT
  -- | lean_is_scalar : (αt : MyTy) → denote αt → LeanInitPureExtern LeanPrimTy.bool -- isScalarObj
  | lean_uint8_dec_le : UInt8 → UInt8 → LeanInitPureExtern LeanPrimTy.bool -- UInt8.decLe
  | lean_nat_dec_le__Nat_ble : Nat → Nat → LeanInitPureExtern LeanPrimTy.bool -- Nat.ble
  | lean_nat_dec_le__Nat_decLe : Nat → Nat → LeanInitPureExtern LeanPrimTy.bool -- Nat.decLe
  | lean_array_get : (αt : MyTy) → (inhabited_default : denote αt) → Array (denote αt) → Nat → LeanInitPureExtern αt -- Array.get!Internal
  | lean_nat_add : Nat → Nat → LeanInitPureExtern nat -- Nat.add
  -- | lean_panic_fn_borrowed : (αt : MyTy) → String → LeanInitPureExtern αt -- panicCore
  | lean_uint16_to_nat__UInt16_toBitVec : UInt16 → LeanInitPureExtern (bitvec 16) -- UInt16.toBitVec
  | lean_uint16_of_nat_mk : BitVec 16 → LeanInitPureExtern uint16 -- UInt16.ofBitVec
  | lean_uint16_dec_eq : UInt16 → UInt16 → LeanInitPureExtern LeanPrimTy.bool -- UInt16.decEq
  | lean_string_dec_eq : String → String → LeanInitPureExtern LeanPrimTy.bool -- String.decEq
  | lean_nat_pred : Nat → LeanInitPureExtern nat -- Nat.pred
  -- | lean_usize_of_nat__USize_ofNatLT : (n : Nat) → (h : n < LeanScript.USize_size) → LeanInitPureExtern LeanPrimTy.usize -- USize.ofNatLT
  | lean_string_mk__String_ofList : List Char → LeanInitPureExtern string -- String.ofList
  | lean_string_hash : String → LeanInitPureExtern uint64 -- String.hash
  | lean_uint64_to_nat__UInt64_toBitVec : UInt64 → LeanInitPureExtern (bitvec 64) -- UInt64.toBitVec
  | lean_uint64_of_nat_mk : BitVec 64 → LeanInitPureExtern uint64 -- UInt64.ofBitVec
  | lean_uint32_to_nat__UInt32_toNat : UInt32 → LeanInitPureExtern nat -- UInt32.toNat
  | lean_uint32_to_nat__UInt32_toBitVec : UInt32 → LeanInitPureExtern (bitvec 32) -- UInt32.toBitVec
  | lean_uint64_dec_eq : UInt64 → UInt64 → LeanInitPureExtern LeanPrimTy.bool -- UInt64.decEq
  | lean_uint16_of_nat__UInt16_ofNatLT : (n : Nat) → (h : n < UInt16.size) → LeanInitPureExtern uint16 -- UInt16.ofNatLT
  | lean_name_eq : Lean.Name → Lean.Name → LeanInitPureExtern LeanPrimTy.bool -- Lean.Name.beq
  | lean_uint8_of_nat_mk : BitVec 8 → LeanInitPureExtern uint8 -- UInt8.ofBitVec
  -- | lean_mk_empty_byte_array : Nat → LeanInitPureExtern byteArray -- ByteArray.emptyWithCapacity -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  | lean_uint8_dec_eq : UInt8 → UInt8 → LeanInitPureExtern LeanPrimTy.bool -- UInt8.decEq
  | lean_nat_pow : Nat → Nat → LeanInitPureExtern nat -- Nat.pow
  -- | lean_usize_dec_eq : denote LeanPrimTy.usize → denote LeanPrimTy.usize → LeanInitPureExtern LeanPrimTy.bool -- USize.decEq
  -- | lean_usize_of_nat_mk : BitVec 64 → LeanInitPureExtern LeanPrimTy.usize -- USize.ofBitVec
  | lean_array_fget : (αt : MyTy) → (a : Array (denote αt)) → (i : Nat) → (h : i < a.size) → LeanInitPureExtern αt -- Array.getInternal
  | lean_nat_mul : Nat → Nat → LeanInitPureExtern nat -- Nat.mul
  -- | lean_usize_to_nat__USize_toBitVec : denote LeanPrimTy.usize → LeanInitPureExtern (bitvec 64) -- USize.toBitVec
  | lean_string_utf8_byte_size : String → LeanInitPureExtern nat -- String.utf8ByteSize
  -- | lean_byte_array_push : ByteArray → UInt8 → LeanInitPureExtern byteArray -- ByteArray.push -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  | lean_array_mk : (αt : MyTy) → List (denote αt) → LeanInitPureExtern (array αt) -- Array.mk
  | lean_uint64_mix_hash : UInt64 → UInt64 → LeanInitPureExtern uint64 -- mixHash
  | lean_uint64_of_nat__UInt64_ofNatLT : (n : Nat) → (h : n < UInt64.size) → LeanInitPureExtern uint64 -- UInt64.ofNatLT
  -----------------
  -- Init/Core.lean
  -----------------
  -- | lean_task_map : (αt : MyTy) → (βt : MyTy) → (denote αt → denote βt) → denote (task αt) → (prio : Task.Priority := Task.Priority.default) → (sync : Bool := false) → LeanInitPureExtern (task βt) -- Task.map
  -- | lean_task_spawn : (αt : MyTy) → (denote (lazy αt)) → (prio : Task.Priority := Task.Priority.default) → LeanInitPureExtern (task αt) -- Task.spawn
  | lean_strict_or : Bool → Bool → LeanInitPureExtern LeanPrimTy.bool -- strictOr
  | lean_thunk_pure : (αt : MyTy) → denote αt → LeanInitPureExtern (thunk αt) -- Thunk.pure
  | lean_mk_thunk : (αt : MyTy) → (denote (lazy αt)) → LeanInitPureExtern (thunk αt) -- Thunk.mk
  -- | lean_task_get_own : (αt : MyTy) → denote (task αt) → LeanInitPureExtern αt -- Task.get
  -- | lean_task_pure : (αt : MyTy) → denote αt → LeanInitPureExtern (task αt) -- Task.pure
  | lean_thunk_get_own : (αt : MyTy) → Thunk (denote αt) → LeanInitPureExtern αt -- Thunk.get
  | lean_strict_and : Bool → Bool → LeanInitPureExtern LeanPrimTy.bool -- strictAnd
  -- | lean_task_bind : (αt : MyTy) → (βt : MyTy) → denote (task αt) → (denote αt → denote (task βt)) → (prio : Task.Priority := Task.Priority.default) → (sync : Bool := false) → LeanInitPureExtern (task βt) -- Task.bind
  ---------------------------
  -- Init/Data/Int/Basic.lean
  ---------------------------
  | lean_nat_to_int : Nat → LeanInitPureExtern int -- Int.ofNat
  | lean_int_dec_le : Int → Int → LeanInitPureExtern LeanPrimTy.bool -- Int.decLe
  | lean_int_dec_lt : Int → Int → LeanInitPureExtern LeanPrimTy.bool -- Int.decLt
  | lean_int_dec_eq : Int → Int → LeanInitPureExtern LeanPrimTy.bool -- Int.decEq
  | lean_int_mul : Int → Int → LeanInitPureExtern int -- Int.mul
  | lean_int_dec_nonneg : Int → LeanInitPureExtern LeanPrimTy.bool -- Int.decNonneg
  | lean_int_neg_succ_of_nat : Nat → LeanInitPureExtern int -- Int.negSucc
  | lean_int_add : Int → Int → LeanInitPureExtern int -- Int.add
  | lean_int_neg : Int → LeanInitPureExtern int -- Int.neg
  | lean_int_sub : Int → Int → LeanInitPureExtern int -- Int.sub
  | lean_nat_abs : Int → LeanInitPureExtern nat -- Int.natAbs
  -------------------------------
  -- Init/Data/Nat/Div/Basic.lean
  -------------------------------
  | lean_nat_div_exact : (x : Nat) → (y : Nat) → (h : y ∣ x) → LeanInitPureExtern nat -- Nat.divExact
  -----------------------------------
  -- Init/Data/Nat/Bitwise/Basic.lean
  -----------------------------------
  | lean_nat_lxor : Nat → Nat → LeanInitPureExtern nat -- Nat.xor
  | lean_nat_shiftl : Nat → Nat → LeanInitPureExtern nat -- Nat.shiftLeft
  | lean_nat_shiftr : Nat → Nat → LeanInitPureExtern nat -- Nat.shiftRight
  | lean_nat_land : Nat → Nat → LeanInitPureExtern nat -- Nat.land
  | lean_nat_lor : Nat → Nat → LeanInitPureExtern nat -- Nat.lor
  -------------------------------
  -- Init/Data/UInt/BasicAux.lean
  -------------------------------
  | lean_uint64_to_nat__UInt64_toNat : UInt64 → LeanInitPureExtern nat -- UInt64.toNat
  | lean_uint32_to_uint8 : UInt32 → LeanInitPureExtern uint8 -- UInt32.toUInt8
  -- | lean_usize_to_nat__USize_toNat : denote LeanPrimTy.usize → LeanInitPureExtern nat -- USize.toNat
  | lean_uint64_to_uint32 : UInt64 → LeanInitPureExtern uint32 -- UInt64.toUInt32
  | lean_uint32_to_uint16 : UInt32 → LeanInitPureExtern uint16 -- UInt32.toUInt16
  | lean_uint16_to_uint32 : UInt16 → LeanInitPureExtern uint32 -- UInt16.toUInt32
  | lean_uint32_to_uint64 : UInt32 → LeanInitPureExtern uint64 -- UInt32.toUInt64
  | lean_uint32_of_nat__UInt32_ofNat : Nat → LeanInitPureExtern uint32 -- UInt32.ofNat
  -- | lean_usize_add : denote LeanPrimTy.usize → denote LeanPrimTy.usize → LeanInitPureExtern LeanPrimTy.usize -- USize.add
  | lean_uint32_sub : UInt32 → UInt32 → LeanInitPureExtern uint32 -- UInt32.sub
  | lean_uint16_to_nat__UInt16_toNat : UInt16 → LeanInitPureExtern nat -- UInt16.toNat
  | lean_uint16_to_uint8 : UInt16 → LeanInitPureExtern uint8 -- UInt16.toUInt8
  -- | lean_usize_sub : denote LeanPrimTy.usize → denote LeanPrimTy.usize → LeanInitPureExtern LeanPrimTy.usize -- USize.sub
  | lean_uint32_add : UInt32 → UInt32 → LeanInitPureExtern uint32 -- UInt32.add
  -- | lean_usize_of_nat__USize_ofNat : Nat → LeanInitPureExtern LeanPrimTy.usize -- USize.ofNat
  -- | lean_usize_dec_le : denote LeanPrimTy.usize → denote LeanPrimTy.usize → LeanInitPureExtern LeanPrimTy.bool -- USize.decLe
  | lean_uint8_to_uint64 : UInt8 → LeanInitPureExtern uint64 -- UInt8.toUInt64
  | lean_uint8_to_nat__UInt8_toNat : UInt8 → LeanInitPureExtern nat -- UInt8.toNat
  | lean_uint64_of_nat__UInt64_ofNat : Nat → LeanInitPureExtern uint64 -- UInt64.ofNat
  | lean_uint8_to_uint32 : UInt8 → LeanInitPureExtern uint32 -- UInt8.toUInt32
  | lean_uint16_of_nat__UInt16_ofNat : Nat → LeanInitPureExtern uint16 -- UInt16.ofNat
  | lean_uint16_to_uint64 : UInt16 → LeanInitPureExtern uint64 -- UInt16.toUInt64
  -- | lean_usize_dec_lt : denote LeanPrimTy.usize → denote LeanPrimTy.usize → LeanInitPureExtern LeanPrimTy.bool -- USize.decLt
  | lean_uint64_to_uint8 : UInt64 → LeanInitPureExtern uint8 -- UInt64.toUInt8
  | lean_uint64_to_uint16 : UInt64 → LeanInitPureExtern uint16 -- UInt64.toUInt16
  | lean_uint8_to_uint16 : UInt8 → LeanInitPureExtern uint16 -- UInt8.toUInt16
  ----------------------------------
  -- Init/Data/String/Bootstrap.lean
  ----------------------------------
  | lean_string_utf8_get__String_Internal_get : String → String.Pos.Raw → LeanInitPureExtern char -- String.Internal.get
  | lean_string_trim : String → LeanInitPureExtern string -- String.Internal.trim
  | lean_substring_drop : Substring.Raw → Nat → LeanInitPureExtern substringRaw -- Substring.Raw.Internal.drop
  | lean_substring_prev : Substring.Raw → String.Pos.Raw → LeanInitPureExtern stringPosRaw -- Substring.Raw.Internal.prev
  | lean_substring_extract : Substring.Raw → String.Pos.Raw → String.Pos.Raw → LeanInitPureExtern substringRaw -- Substring.Raw.Internal.extract
  | lean_string_foldl : (String → Char → String) → String → String → LeanInitPureExtern string -- String.Internal.foldl
  | lean_substring_tostring : Substring.Raw → LeanInitPureExtern string -- Substring.Raw.Internal.toString
  | lean_string_append__String_Internal_append : String → String → LeanInitPureExtern string -- String.Internal.append
  | lean_string_get_byte_fast__String_Internal_getUTF8Byte : (s : String) → (n : Nat) → (h : n < s.utf8ByteSize) → LeanInitPureExtern uint8 -- String.Internal.getUTF8Byte
  | lean_string_isempty : String → LeanInitPureExtern LeanPrimTy.bool -- String.Internal.isEmpty
  | lean_string_push : String → Char → LeanInitPureExtern string -- String.push
  | lean_string_isprefixof : String → String → LeanInitPureExtern LeanPrimTy.bool -- String.Internal.isPrefixOf
  | lean_string_dropright : String → Nat → LeanInitPureExtern string -- String.Internal.dropRight
  | lean_substring_takewhile : Substring.Raw → (Char → Bool) → LeanInitPureExtern substringRaw -- Substring.Raw.Internal.takeWhile
  | lean_substring_get : Substring.Raw → String.Pos.Raw → LeanInitPureExtern char -- Substring.Raw.Internal.get
  | lean_string_uget_byte_fast : (s : String) → (n : USize) → (h : n.toNat < s.utf8ByteSize) → LeanInitPureExtern uint8 -- String.Internal.ugetUTF8Byte
  | lean_string_contains : String → Char → LeanInitPureExtern LeanPrimTy.bool -- String.Internal.contains
  | lean_string_front : String → LeanInitPureExtern char -- String.Internal.front
  | lean_string_posof : String → Char → LeanInitPureExtern stringPosRaw -- String.Internal.posOf
  | lean_substring_all : Substring.Raw → (Char → Bool) → LeanInitPureExtern LeanPrimTy.bool -- Substring.Raw.Internal.all
  | lean_string_intercalate : String → List String → LeanInitPureExtern string -- String.Internal.intercalate
  | lean_string_drop : String → Nat → LeanInitPureExtern string -- String.Internal.drop
  | lean_string_length__String_Internal_length : String → LeanInitPureExtern nat -- String.Internal.length
  | lean_string_utf8_at_end__String_Internal_atEnd : String → String.Pos.Raw → LeanInitPureExtern LeanPrimTy.bool -- String.Internal.atEnd
  | lean_substring_beq : Substring.Raw → Substring.Raw → LeanInitPureExtern LeanPrimTy.bool -- Substring.Raw.Internal.beq
  | lean_string_nextwhile : String → (Char → Bool) → String.Pos.Raw → LeanInitPureExtern stringPosRaw -- String.Internal.nextWhile
  | lean_string_utf8_next__String_Internal_next : String → String.Pos.Raw → LeanInitPureExtern stringPosRaw -- String.Internal.next
  | lean_string_mk__String_mk : List Char → LeanInitPureExtern string -- String.mk
  | lean_string_any : String → (Char → Bool) → LeanInitPureExtern LeanPrimTy.bool -- String.Internal.any
  | lean_string_pushn : String → Char → Nat → LeanInitPureExtern string -- String.Internal.pushn
  | lean_string_capitalize : String → LeanInitPureExtern string -- String.Internal.capitalize
  | lean_string_utf8_extract__String_Internal_extract : String → String.Pos.Raw → String.Pos.Raw → LeanInitPureExtern string -- String.Internal.extract
  | lean_string_pos_min : String.Pos.Raw → String.Pos.Raw → LeanInitPureExtern stringPosRaw -- String.Pos.Raw.Internal.min
  | lean_substring_front : Substring.Raw → LeanInitPureExtern char -- Substring.Raw.Internal.front
  | lean_string_pos_sub : String.Pos.Raw → String.Pos.Raw → LeanInitPureExtern stringPosRaw -- String.Pos.Raw.Internal.sub
  | lean_substring_isempty : Substring.Raw → LeanInitPureExtern LeanPrimTy.bool -- Substring.Raw.Internal.isEmpty
  | lean_string_offsetofpos : String → String.Pos.Raw → LeanInitPureExtern nat -- String.Internal.offsetOfPos
  ----------------------
  -- Init/Data/Repr.lean
  ----------------------
  -- | lean_string_of_usize : denote LeanPrimTy.usize → LeanInitPureExtern string -- USize.repr
  -----------------
  -- Init/Util.lean
  -----------------
  -- | lean_dbg_sleep : (αt : MyTy) → UInt32 → (denote (lazy αt)) → LeanInitPureExtern αt -- dbgSleep
  -- | lean_ptr_addr : (αt : MyTy) → denote αt → LeanInitPureExtern LeanPrimTy.usize -- ptrAddrUnsafe
  -- | lean_dbg_trace : (αt : MyTy) → String → (denote (lazy αt)) → LeanInitPureExtern αt -- dbgTrace
  | lean_dbg_trace_if_shared : (αt : MyTy) → String → denote αt → LeanInitPureExtern αt -- dbgTraceIfShared
  -- | lean_dbg_stack_trace : (αt : MyTy) → (denote (lazy αt)) → LeanInitPureExtern αt -- dbgStackTrace
  -- | lean_is_exclusive_obj : (αt : MyTy) → denote αt → LeanInitPureExtern LeanPrimTy.bool -- isExclusiveUnsafe
  ---------------------------
  -- Init/Data/Array/Set.lean
  ---------------------------
  | lean_array_set : (αt : MyTy) → Array (denote αt) → Nat → denote αt → LeanInitPureExtern (array αt) -- Array.set!
  | lean_array_fset : (αt : MyTy) → (xs : Array (denote αt)) → (i : Nat) → denote αt → (h : i < xs.size := by get_elem_tactic) → LeanInitPureExtern (array αt) -- Array.set
  -----------------------------
  -- Init/Data/Array/Basic.lean
  -----------------------------
  | lean_array_fswap : (αt : MyTy) → (xs : Array (denote αt)) → (i : Nat) → (j : Nat) → (h : i < xs.size := by get_elem_tactic) → (h : j < xs.size := by get_elem_tactic) → LeanInitPureExtern (array αt) -- Array.swap
  | lean_array_uget : (αt : MyTy) → (xs : Array (denote αt)) → (i : USize) → (h : i.toNat < xs.size) → LeanInitPureExtern αt -- Array.uget
  | lean_mk_array : (αt : MyTy) → Nat → denote αt → LeanInitPureExtern (array αt) -- Array.replicate
  | lean_array_swap : (αt : MyTy) → Array (denote αt) → Nat → Nat → LeanInitPureExtern (array αt) -- Array.swapIfInBounds
  -- | lean_array_uget_borrowed : (αt : MyTy) → (xs : Array (denote αt)) → (i : USize) → (h : i.toNat < xs.size) → LeanInitPureExtern αt -- Array.ugetBorrowed
  | lean_array_pop : (αt : MyTy) → Array (denote αt) → LeanInitPureExtern (array αt) -- Array.pop
  | lean_array_uset : (αt : MyTy) → (xs : Array (denote αt)) → (i : USize) → denote αt → (h : i.toNat < xs.size) → LeanInitPureExtern (array αt) -- Array.uset
  -- | lean_array_size : (αt : MyTy) → Array (denote αt) → LeanInitPureExtern LeanPrimTy.usize -- Array.usize
  ----------------------
  -- Init/Meta/Defs.lean
  ----------------------
  | lean_version_get_special_desc : LeanInitPureExtern (lazy string) -- Lean.version.getSpecialDesc
  | lean_version_get_is_release : LeanInitPureExtern (lazy LeanPrimTy.bool) -- Lean.version.getIsRelease
  | lean_version_get_major : LeanInitPureExtern (lazy nat) -- _private.Init.Meta.Defs.0.Lean.version.getMajor
  | lean_version_get_patch : LeanInitPureExtern (lazy nat) -- _private.Init.Meta.Defs.0.Lean.version.getPatch
  | lean_internal_is_stage0 : LeanInitPureExtern (lazy LeanPrimTy.bool) -- Lean.Internal.isStage0
  | lean_version_get_minor : LeanInitPureExtern (lazy nat) -- _private.Init.Meta.Defs.0.Lean.version.getMinor
  | lean_get_githash : LeanInitPureExtern (lazy string) -- Lean.getGithash
  | lean_internal_has_llvm_backend : LeanInitPureExtern (lazy LeanPrimTy.bool) -- Lean.Internal.hasLLVMBackend
  --------------------------
  -- Init/Data/Nat/Log2.lean
  --------------------------
  | lean_nat_log2 : Nat → LeanInitPureExtern nat -- Nat.log2
  ----------------------------------
  -- Init/Data/Int/DivMod/Basic.lean
  ----------------------------------
  | lean_int_emod : Int → Int → LeanInitPureExtern int -- Int.emod
  | lean_int_div_exact : (x : Int) → (y : Int) → (h : y ∣ x) → LeanInitPureExtern int -- Int.divExact
  | lean_int_mod : Int → Int → LeanInitPureExtern int -- Int.tmod
  | lean_int_ediv : Int → Int → LeanInitPureExtern int -- Int.ediv
  | lean_int_div : Int → Int → LeanInitPureExtern int -- Int.tdiv
  -------------------------
  -- Init/Data/Nat/Gcd.lean
  -------------------------
  | lean_nat_gcd__Nat_gcd__unary : (_ : Nat) ×' Nat → LeanInitPureExtern nat -- Nat.gcd._unary
  | lean_nat_gcd__Nat_gcd : Nat → Nat → LeanInitPureExtern nat -- Nat.gcd
  ----------------------------
  -- Init/Data/UInt/Basic.lean
  ----------------------------
  | lean_uint64_shift_left : UInt64 → UInt64 → LeanInitPureExtern uint64 -- UInt64.shiftLeft
  | lean_uint32_mod : UInt32 → UInt32 → LeanInitPureExtern uint32 -- UInt32.mod
  | lean_uint16_neg : UInt16 → LeanInitPureExtern uint16 -- UInt16.neg
  -- | lean_usize_land : denote LeanPrimTy.usize → denote LeanPrimTy.usize → LeanInitPureExtern LeanPrimTy.usize -- USize.land
  -- | lean_usize_mul : denote LeanPrimTy.usize → denote LeanPrimTy.usize → LeanInitPureExtern LeanPrimTy.usize -- USize.mul
  -- | lean_uint16_to_usize : UInt16 → LeanInitPureExtern LeanPrimTy.usize -- UInt16.toUSize
  | lean_uint64_shift_right : UInt64 → UInt64 → LeanInitPureExtern uint64 -- UInt64.shiftRight
  -- | lean_usize_shift_left : denote LeanPrimTy.usize → denote LeanPrimTy.usize → LeanInitPureExtern LeanPrimTy.usize -- USize.shiftLeft
  | lean_uint16_add : UInt16 → UInt16 → LeanInitPureExtern uint16 -- UInt16.add
  -- | lean_usize_xor : denote LeanPrimTy.usize → denote LeanPrimTy.usize → LeanInitPureExtern LeanPrimTy.usize -- USize.xor
  | lean_uint64_complement : UInt64 → LeanInitPureExtern uint64 -- UInt64.complement
  | lean_bool_to_uint32 : Bool → LeanInitPureExtern uint32 -- Bool.toUInt32
  | lean_uint16_lor : UInt16 → UInt16 → LeanInitPureExtern uint16 -- UInt16.lor
  | lean_uint16_mul : UInt16 → UInt16 → LeanInitPureExtern uint16 -- UInt16.mul
  | lean_uint16_land : UInt16 → UInt16 → LeanInitPureExtern uint16 -- UInt16.land
  | lean_uint8_sub : UInt8 → UInt8 → LeanInitPureExtern uint8 -- UInt8.sub
  | lean_uint32_div : UInt32 → UInt32 → LeanInitPureExtern uint32 -- UInt32.div
  | lean_uint64_add : UInt64 → UInt64 → LeanInitPureExtern uint64 -- UInt64.add
  | lean_uint8_neg : UInt8 → LeanInitPureExtern uint8 -- UInt8.neg
  | lean_uint16_complement : UInt16 → LeanInitPureExtern uint16 -- UInt16.complement
  | lean_uint64_lor : UInt64 → UInt64 → LeanInitPureExtern uint64 -- UInt64.lor
  | lean_uint64_mod : UInt64 → UInt64 → LeanInitPureExtern uint64 -- UInt64.mod
  | lean_uint8_lor : UInt8 → UInt8 → LeanInitPureExtern uint8 -- UInt8.lor
  | lean_uint32_shift_right : UInt32 → UInt32 → LeanInitPureExtern uint32 -- UInt32.shiftRight
  | lean_uint16_xor : UInt16 → UInt16 → LeanInitPureExtern uint16 -- UInt16.xor
  -- | lean_usize_lor : denote LeanPrimTy.usize → denote LeanPrimTy.usize → LeanInitPureExtern LeanPrimTy.usize -- USize.lor
  | lean_uint8_div : UInt8 → UInt8 → LeanInitPureExtern uint8 -- UInt8.div
  | lean_uint16_shift_left : UInt16 → UInt16 → LeanInitPureExtern uint16 -- UInt16.shiftLeft
  | lean_uint32_neg : UInt32 → LeanInitPureExtern uint32 -- UInt32.neg
  | lean_uint16_mod : UInt16 → UInt16 → LeanInitPureExtern uint16 -- UInt16.mod
  -- | lean_usize_neg : denote LeanPrimTy.usize → LeanInitPureExtern LeanPrimTy.usize -- USize.neg
  | lean_uint64_div : UInt64 → UInt64 → LeanInitPureExtern uint64 -- UInt64.div
  | lean_uint16_dec_lt : UInt16 → UInt16 → LeanInitPureExtern LeanPrimTy.bool -- UInt16.decLt
  | lean_uint8_shift_right : UInt8 → UInt8 → LeanInitPureExtern uint8 -- UInt8.shiftRight
  -- | lean_usize_to_uint64 : denote LeanPrimTy.usize → LeanInitPureExtern uint64 -- USize.toUInt64
  | lean_uint32_lor : UInt32 → UInt32 → LeanInitPureExtern uint32 -- UInt32.lor
  | lean_uint64_mul : UInt64 → UInt64 → LeanInitPureExtern uint64 -- UInt64.mul
  -- | lean_usize_shift_right : denote LeanPrimTy.usize → denote LeanPrimTy.usize → LeanInitPureExtern LeanPrimTy.usize -- USize.shiftRight
  | lean_uint64_land : UInt64 → UInt64 → LeanInitPureExtern uint64 -- UInt64.land
  | lean_uint8_shift_left : UInt8 → UInt8 → LeanInitPureExtern uint8 -- UInt8.shiftLeft
  | lean_uint16_div : UInt16 → UInt16 → LeanInitPureExtern uint16 -- UInt16.div
  | lean_bool_to_uint64 : Bool → LeanInitPureExtern uint64 -- Bool.toUInt64
  | lean_uint8_land : UInt8 → UInt8 → LeanInitPureExtern uint8 -- UInt8.land
  | lean_uint64_dec_le : UInt64 → UInt64 → LeanInitPureExtern LeanPrimTy.bool -- UInt64.decLe
  | lean_uint8_mul : UInt8 → UInt8 → LeanInitPureExtern uint8 -- UInt8.mul
  -- | lean_usize_of_nat__USize_ofNat32 : (n : Nat) → (h : n < 4294967296) → LeanInitPureExtern LeanPrimTy.usize -- USize.ofNat32
  | lean_uint64_sub : UInt64 → UInt64 → LeanInitPureExtern uint64 -- UInt64.sub
  | lean_uint64_neg : UInt64 → LeanInitPureExtern uint64 -- UInt64.neg
  | lean_uint8_add : UInt8 → UInt8 → LeanInitPureExtern uint8 -- UInt8.add
  -- | lean_usize_div : denote LeanPrimTy.usize → denote LeanPrimTy.usize → LeanInitPureExtern LeanPrimTy.usize -- USize.div
  -- | lean_uint32_to_usize : UInt32 → LeanInitPureExtern LeanPrimTy.usize -- UInt32.toUSize
  | lean_uint8_complement : UInt8 → LeanInitPureExtern uint8 -- UInt8.complement
  -- | lean_usize_to_uint16 : denote LeanPrimTy.usize → LeanInitPureExtern uint16 -- USize.toUInt16
  | lean_uint32_xor : UInt32 → UInt32 → LeanInitPureExtern uint32 -- UInt32.xor
  | lean_uint16_dec_le : UInt16 → UInt16 → LeanInitPureExtern LeanPrimTy.bool -- UInt16.decLe
  -- | lean_usize_to_uint8 : denote LeanPrimTy.usize → LeanInitPureExtern uint8 -- USize.toUInt8
  | lean_uint32_shift_left : UInt32 → UInt32 → LeanInitPureExtern uint32 -- UInt32.shiftLeft
  | lean_uint16_sub : UInt16 → UInt16 → LeanInitPureExtern uint16 -- UInt16.sub
  | lean_uint32_mul : UInt32 → UInt32 → LeanInitPureExtern uint32 -- UInt32.mul
  | lean_uint32_land : UInt32 → UInt32 → LeanInitPureExtern uint32 -- UInt32.land
  -- | lean_usize_mod : denote LeanPrimTy.usize → denote LeanPrimTy.usize → LeanInitPureExtern LeanPrimTy.usize -- USize.mod
  | lean_uint8_mod : UInt8 → UInt8 → LeanInitPureExtern uint8 -- UInt8.mod
  | lean_uint64_dec_lt : UInt64 → UInt64 → LeanInitPureExtern LeanPrimTy.bool -- UInt64.decLt
  | lean_bool_to_uint8 : Bool → LeanInitPureExtern uint8 -- Bool.toUInt8
  | lean_uint32_complement : UInt32 → LeanInitPureExtern uint32 -- UInt32.complement
  -- | lean_uint8_to_usize : UInt8 → LeanInitPureExtern LeanPrimTy.usize -- UInt8.toUSize
  | lean_bool_to_uint16 : Bool → LeanInitPureExtern uint16 -- Bool.toUInt16
  | lean_uint8_xor : UInt8 → UInt8 → LeanInitPureExtern uint8 -- UInt8.xor
  -- | lean_bool_to_usize : Bool → LeanInitPureExtern LeanPrimTy.usize -- Bool.toUSize
  -- | lean_uint64_to_usize : UInt64 → LeanInitPureExtern LeanPrimTy.usize -- UInt64.toUSize
  | lean_uint16_shift_right : UInt16 → UInt16 → LeanInitPureExtern uint16 -- UInt16.shiftRight
  -- | lean_usize_to_uint32 : denote LeanPrimTy.usize → LeanInitPureExtern uint32 -- USize.toUInt32
  -- | lean_usize_complement : denote LeanPrimTy.usize → LeanInitPureExtern LeanPrimTy.usize -- USize.complement
  | lean_uint64_xor : UInt64 → UInt64 → LeanInitPureExtern uint64 -- UInt64.xor
  ---------------------------------
  -- Init/Data/ByteArray/Basic.lean
  ---------------------------------
  -- | lean_byte_array_copy_slice : ByteArray → Nat → ByteArray → Nat → Nat → (exact : Bool := true) → LeanInitPureExtern byteArray -- ByteArray.copySlice -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  -- | lean_byte_array_hash : ByteArray → LeanInitPureExtern uint64 -- ByteArray.hash -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  -- | lean_sarray_size__ByteArray_usize : ByteArray → LeanInitPureExtern LeanPrimTy.usize -- ByteArray.usize
  -- | lean_sarray_dec_eq__ByteArray_beq : ByteArray → ByteArray → LeanInitPureExtern LeanPrimTy.bool -- ByteArray.beq -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  -- | lean_sarray_dec_eq__ByteArray_decEq : ByteArray → ByteArray → LeanInitPureExtern LeanPrimTy.bool -- ByteArray.decEq -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  -- | lean_byte_array_set : ByteArray → Nat → UInt8 → LeanInitPureExtern byteArray -- ByteArray.set! -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  -- | lean_byte_array_fget : (a : ByteArray) → (i : Nat) → (h : i < a.size := by get_elem_tactic) → LeanInitPureExtern uint8 -- ByteArray.get -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  -- | lean_byte_array_uset : (a : ByteArray) → (i : USize) → UInt8 → (h : i.toNat < a.size := by get_elem_tactic) → LeanInitPureExtern byteArray -- ByteArray.uset -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  -- | lean_byte_array_fset : (a : ByteArray) → (i : Nat) → UInt8 → (h : i < a.size := by get_elem_tactic) → LeanInitPureExtern byteArray -- ByteArray.set -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  -- | lean_byte_array_uget : (a : ByteArray) → (i : USize) → (h : i.toNat < a.size := by get_elem_tactic) → LeanInitPureExtern uint8 -- ByteArray.uget -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  -- | lean_byte_array_get : ByteArray → Nat → LeanInitPureExtern uint8 -- ByteArray.get! -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  -------------------------------
  -- Init/Data/String/PosRaw.lean
  -------------------------------
  | lean_string_get_byte_fast__String_getUtf8Byte : (s : String) → (p : String.Pos.Raw) → (h : p < s.rawEndPos) → LeanInitPureExtern uint8 -- String.getUtf8Byte
  | lean_string_get_byte_fast__String_getUTF8Byte : (s : String) → (p : String.Pos.Raw) → (h : p < s.rawEndPos) → LeanInitPureExtern uint8 -- String.getUTF8Byte
  -----------------------------
  -- Init/Data/String/Defs.lean
  -----------------------------
  -- | lean_string_to_utf8__String_toUTF8 : String → LeanInitPureExtern byteArray -- String.toUTF8 -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  | lean_string_append__String_append : String → String → LeanInitPureExtern string -- String.append
  ----------------------------
  -- Init/System/Platform.lean
  ----------------------------
  -- | lean_internal_get_hardware_concurrency : LeanInitPureExtern (lazy uint32) -- System.Platform.Internal.getHardwareConcurrency
  -- | lean_system_platform_linux : LeanInitPureExtern (lazy LeanPrimTy.bool) -- System.Platform.getIsLinux
  | lean_system_platform_emscripten : LeanInitPureExtern (lazy LeanPrimTy.bool) -- System.Platform.getIsEmscripten
  | lean_system_platform_target : LeanInitPureExtern (lazy string) -- System.Platform.getTarget
  -- | lean_system_platform_windows : LeanInitPureExtern (lazy LeanPrimTy.bool) -- System.Platform.getIsWindows
  -- | lean_system_platform_osx : LeanInitPureExtern (lazy LeanPrimTy.bool) -- System.Platform.getIsOSX
  ------------------------------
  -- Init/Data/String/Basic.lean
  ------------------------------
  | lean_string_utf8_next__String_next : String → String.Pos.Raw → LeanInitPureExtern stringPosRaw -- String.next
  | lean_string_utf8_next__String_Pos_Raw_next : String → String.Pos.Raw → LeanInitPureExtern stringPosRaw -- String.Pos.Raw.next
  | lean_string_utf8_get__String_Pos_Raw_get : String → String.Pos.Raw → LeanInitPureExtern char -- String.Pos.Raw.get
  | lean_string_utf8_get__String_get : String → String.Pos.Raw → LeanInitPureExtern char -- String.get
  | lean_string_utf8_get_opt__String_Pos_Raw_get? : String → String.Pos.Raw → LeanInitPureExtern (option char) -- String.Pos.Raw.get?
  | lean_string_utf8_get_opt__String_get? : String → String.Pos.Raw → LeanInitPureExtern (option char) -- String.get?
  | lean_string_utf8_prev__String_Pos_Raw_prev : String → String.Pos.Raw → LeanInitPureExtern stringPosRaw -- String.Pos.Raw.prev
  | lean_string_utf8_prev__String_prev : String → String.Pos.Raw → LeanInitPureExtern stringPosRaw -- String.prev
  | lean_string_utf8_next_fast__String_next' : (s : String) → (p : String.Pos.Raw) → (h : ¬String.Pos.Raw.atEnd s p = Bool.true) → LeanInitPureExtern stringPosRaw -- String.next'
  | lean_string_utf8_next_fast__String_Pos_Raw_next' : (s : String) → (p : String.Pos.Raw) → (h : ¬String.Pos.Raw.atEnd s p = Bool.true) → LeanInitPureExtern stringPosRaw -- String.Pos.Raw.next'
  | lean_string_utf8_next_fast__String_Pos_next : {s : String} → (pos : s.Pos) → (h : pos ≠ s.endPos) → LeanInitPureExtern (LeanPrimTy.stringPos s) -- String.Pos.next
  | lean_string_data__String_data : String → LeanInitPureExtern (list char) -- String.data
  | lean_string_data__String_toList : String → LeanInitPureExtern (list char) -- String.toList
  | lean_string_utf8_extract_fast : {s : String} → s.Pos → s.Pos → LeanInitPureExtern string -- String.extract
  | lean_string_utf8_at_end__String_atEnd : String → String.Pos.Raw → LeanInitPureExtern LeanPrimTy.bool -- String.atEnd
  | lean_string_utf8_at_end__String_Pos_Raw_atEnd : String → String.Pos.Raw → LeanInitPureExtern LeanPrimTy.bool -- String.Pos.Raw.atEnd
  | lean_string_utf8_get_bang__String_Pos_Raw_get! : String → String.Pos.Raw → LeanInitPureExtern char -- String.Pos.Raw.get!
  | lean_string_utf8_get_bang__String_get! : String → String.Pos.Raw → LeanInitPureExtern char -- String.get!
  -- | lean_string_utf8_get_fast__String_decodeChar : (s : String) → (byteIdx : Nat) → (h : (s.toByteArray.utf8DecodeChar? byteIdx).isSome = Bool.true) → LeanInitPureExtern char -- String.decodeChar -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  | lean_string_utf8_get_fast__String_get' : (s : String) → (p : String.Pos.Raw) → (h : ¬String.Pos.Raw.atEnd s p = Bool.true) → LeanInitPureExtern char -- String.get'
  | lean_string_utf8_get_fast__String_Pos_Raw_get' : (s : String) → (p : String.Pos.Raw) → (h : ¬String.Pos.Raw.atEnd s p = Bool.true) → LeanInitPureExtern char -- String.Pos.Raw.get'
  | lean_string_is_valid_pos : String → String.Pos.Raw → LeanInitPureExtern LeanPrimTy.bool -- String.Pos.Raw.isValid
  | lean_string_dec_lt : String → String → LeanInitPureExtern LeanPrimTy.bool -- String.decidableLT
  -- | lean_string_validate_utf8 : ByteArray → LeanInitPureExtern LeanPrimTy.bool -- ByteArray.validateUTF8 -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  | lean_string_utf8_extract__String_Pos_Raw_extract : String → String.Pos.Raw → String.Pos.Raw → LeanInitPureExtern string -- String.Pos.Raw.extract
  -------------------------------
  -- Init/Data/String/Length.lean
  -------------------------------
  | lean_string_length__String_length : String → LeanInitPureExtern nat -- String.length
  ----------------------------
  -- Init/Data/SInt/Basic.lean
  ----------------------------
  -- | lean_isize_complement : denote LeanPrimTy.isize → LeanInitPureExtern LeanPrimTy.isize -- ISize.complement
  | lean_int8_add : Int8 → Int8 → LeanInitPureExtern int8 -- Int8.add
  | lean_int16_of_nat : Nat → LeanInitPureExtern int16 -- Int16.ofNat
  | lean_int16_dec_le : Int16 → Int16 → LeanInitPureExtern LeanPrimTy.bool -- Int16.decLe
  | lean_int32_of_int : Int → LeanInitPureExtern int32 -- Int32.ofInt
  -- | lean_int64_to_isize : Int64 → LeanInitPureExtern LeanPrimTy.isize -- Int64.toISize
  | lean_int32_land : Int32 → Int32 → LeanInitPureExtern int32 -- Int32.land
  | lean_int8_div : Int8 → Int8 → LeanInitPureExtern int8 -- Int8.div
  | lean_int32_mul : Int32 → Int32 → LeanInitPureExtern int32 -- Int32.mul
  | lean_int64_sub : Int64 → Int64 → LeanInitPureExtern int64 -- Int64.sub
  | lean_int16_shift_right : Int16 → Int16 → LeanInitPureExtern int16 -- Int16.shiftRight
  -- | lean_isize_to_int8 : denote LeanPrimTy.isize → LeanInitPureExtern int8 -- ISize.toInt8
  | lean_int64_xor : Int64 → Int64 → LeanInitPureExtern int64 -- Int64.xor
  | lean_int32_dec_le : Int32 → Int32 → LeanInitPureExtern LeanPrimTy.bool -- Int32.decLe
  | lean_int32_of_nat : Nat → LeanInitPureExtern int32 -- Int32.ofNat
  -- | lean_isize_xor : denote LeanPrimTy.isize → denote LeanPrimTy.isize → LeanInitPureExtern LeanPrimTy.isize -- ISize.xor
  | lean_int64_to_int8 : Int64 → LeanInitPureExtern int8 -- Int64.toInt8
  -- | lean_isize_shift_left : denote LeanPrimTy.isize → denote LeanPrimTy.isize → LeanInitPureExtern LeanPrimTy.isize -- ISize.shiftLeft
  | lean_int64_mul : Int64 → Int64 → LeanInitPureExtern int64 -- Int64.mul
  | lean_int32_to_int64 : Int32 → LeanInitPureExtern int64 -- Int32.toInt64
  | lean_int8_to_int16 : Int8 → LeanInitPureExtern int16 -- Int8.toInt16
  | lean_int32_sub : Int32 → Int32 → LeanInitPureExtern int32 -- Int32.sub
  | lean_int64_of_int : Int → LeanInitPureExtern int64 -- Int64.ofInt
  -- | lean_int32_to_isize : Int32 → LeanInitPureExtern LeanPrimTy.isize -- Int32.toISize
  | lean_int64_land : Int64 → Int64 → LeanInitPureExtern int64 -- Int64.land
  | lean_int8_shift_right : Int8 → Int8 → LeanInitPureExtern int8 -- Int8.shiftRight
  | lean_int64_lor : Int64 → Int64 → LeanInitPureExtern int64 -- Int64.lor
  | lean_int16_div : Int16 → Int16 → LeanInitPureExtern int16 -- Int16.div
  -- | lean_isize_mod : denote LeanPrimTy.isize → denote LeanPrimTy.isize → LeanInitPureExtern LeanPrimTy.isize -- ISize.mod
  | lean_int32_neg : Int32 → LeanInitPureExtern int32 -- Int32.neg
  | lean_int8_mod : Int8 → Int8 → LeanInitPureExtern int8 -- Int8.mod
  | lean_int32_abs : Int32 → LeanInitPureExtern int32 -- Int32.abs
  | lean_bool_to_int8 : Bool → LeanInitPureExtern int8 -- Bool.toInt8
  -- | lean_isize_shift_right : denote LeanPrimTy.isize → denote LeanPrimTy.isize → LeanInitPureExtern LeanPrimTy.isize -- ISize.shiftRight
  -- | lean_isize_to_int16 : denote LeanPrimTy.isize → LeanInitPureExtern int16 -- ISize.toInt16
  | lean_int8_shift_left : Int8 → Int8 → LeanInitPureExtern int8 -- Int8.shiftLeft
  | lean_int16_dec_lt : Int16 → Int16 → LeanInitPureExtern LeanPrimTy.bool -- Int16.decLt
  | lean_int8_xor : Int8 → Int8 → LeanInitPureExtern int8 -- Int8.xor
  | lean_int32_dec_eq : Int32 → Int32 → LeanInitPureExtern LeanPrimTy.bool -- Int32.decEq
  | lean_int16_to_int : Int16 → LeanInitPureExtern int -- Int16.toInt
  | lean_int16_mod : Int16 → Int16 → LeanInitPureExtern int16 -- Int16.mod
  -- | lean_isize_div : denote LeanPrimTy.isize → denote LeanPrimTy.isize → LeanInitPureExtern LeanPrimTy.isize -- ISize.div
  | lean_int16_dec_eq : Int16 → Int16 → LeanInitPureExtern LeanPrimTy.bool -- Int16.decEq
  | lean_int8_complement : Int8 → LeanInitPureExtern int8 -- Int8.complement
  -- | lean_isize_add : denote LeanPrimTy.isize → denote LeanPrimTy.isize → LeanInitPureExtern LeanPrimTy.isize -- ISize.add
  | lean_bool_to_int16 : Bool → LeanInitPureExtern int16 -- Bool.toInt16
  | lean_int32_dec_lt : Int32 → Int32 → LeanInitPureExtern LeanPrimTy.bool -- Int32.decLt
  -- | lean_isize_lor : denote LeanPrimTy.isize → denote LeanPrimTy.isize → LeanInitPureExtern LeanPrimTy.isize -- ISize.lor
  | lean_int64_mod : Int64 → Int64 → LeanInitPureExtern int64 -- Int64.mod
  -- | lean_isize_of_int : Int → LeanInitPureExtern LeanPrimTy.isize -- ISize.ofInt
  | lean_int64_shift_left : Int64 → Int64 → LeanInitPureExtern int64 -- Int64.shiftLeft
  | lean_int16_abs : Int16 → LeanInitPureExtern int16 -- Int16.abs
  -- | lean_isize_land : denote LeanPrimTy.isize → denote LeanPrimTy.isize → LeanInitPureExtern LeanPrimTy.isize -- ISize.land
  | lean_int16_to_int32 : Int16 → LeanInitPureExtern int32 -- Int16.toInt32
  -- | lean_isize_mul : denote LeanPrimTy.isize → denote LeanPrimTy.isize → LeanInitPureExtern LeanPrimTy.isize -- ISize.mul
  -- | lean_isize_to_int : denote LeanPrimTy.isize → LeanInitPureExtern int -- ISize.toInt
  | lean_int64_dec_lt : Int64 → Int64 → LeanInitPureExtern LeanPrimTy.bool -- Int64.decLt
  -- | lean_isize_dec_le : denote LeanPrimTy.isize → denote LeanPrimTy.isize → LeanInitPureExtern LeanPrimTy.bool -- ISize.decLe
  | lean_int8_dec_eq : Int8 → Int8 → LeanInitPureExtern LeanPrimTy.bool -- Int8.decEq
  | lean_int32_xor : Int32 → Int32 → LeanInitPureExtern int32 -- Int32.xor
  -- | lean_isize_of_nat : Nat → LeanInitPureExtern LeanPrimTy.isize -- ISize.ofNat
  | lean_int16_complement : Int16 → LeanInitPureExtern int16 -- Int16.complement
  | lean_int32_shift_left : Int32 → Int32 → LeanInitPureExtern int32 -- Int32.shiftLeft
  -- | lean_isize_to_int64 : denote LeanPrimTy.isize → LeanInitPureExtern int64 -- ISize.toInt64
  -- | lean_isize_sub : denote LeanPrimTy.isize → denote LeanPrimTy.isize → LeanInitPureExtern LeanPrimTy.isize -- ISize.sub
  | lean_int64_complement : Int64 → LeanInitPureExtern int64 -- Int64.complement
  -- | lean_isize_abs : denote LeanPrimTy.isize → LeanInitPureExtern LeanPrimTy.isize -- ISize.abs
  | lean_int16_land : Int16 → Int16 → LeanInitPureExtern int16 -- Int16.land
  | lean_int16_of_int : Int → LeanInitPureExtern int16 -- Int16.ofInt
  | lean_int32_shift_right : Int32 → Int32 → LeanInitPureExtern int32 -- Int32.shiftRight
  | lean_int8_neg : Int8 → LeanInitPureExtern int8 -- Int8.neg
  | lean_int16_mul : Int16 → Int16 → LeanInitPureExtern int16 -- Int16.mul
  -- | lean_isize_to_int32 : denote LeanPrimTy.isize → LeanInitPureExtern int32 -- ISize.toInt32
  | lean_int64_to_int32 : Int64 → LeanInitPureExtern int32 -- Int64.toInt32
  | lean_int16_shift_left : Int16 → Int16 → LeanInitPureExtern int16 -- Int16.shiftLeft
  | lean_int64_abs : Int64 → LeanInitPureExtern int64 -- Int64.abs
  | lean_int32_complement : Int32 → LeanInitPureExtern int32 -- Int32.complement
  | lean_int16_xor : Int16 → Int16 → LeanInitPureExtern int16 -- Int16.xor
  | lean_bool_to_int64 : Bool → LeanInitPureExtern int64 -- Bool.toInt64
  -- | lean_bool_to_isize : Bool → LeanInitPureExtern LeanPrimTy.isize -- Bool.toISize
  | lean_int8_dec_lt : Int8 → Int8 → LeanInitPureExtern LeanPrimTy.bool -- Int8.decLt
  | lean_int64_dec_eq : Int64 → Int64 → LeanInitPureExtern LeanPrimTy.bool -- Int64.decEq
  | lean_int64_dec_le : Int64 → Int64 → LeanInitPureExtern LeanPrimTy.bool -- Int64.decLe
  | lean_bool_to_int32 : Bool → LeanInitPureExtern int32 -- Bool.toInt32
  | lean_int64_of_nat : Nat → LeanInitPureExtern int64 -- Int64.ofNat
  | lean_int32_to_int8 : Int32 → LeanInitPureExtern int8 -- Int32.toInt8
  | lean_int64_to_int_sint : Int64 → LeanInitPureExtern int -- Int64.toInt
  | lean_int32_add : Int32 → Int32 → LeanInitPureExtern int32 -- Int32.add
  -- | lean_isize_dec_lt : denote LeanPrimTy.isize → denote LeanPrimTy.isize → LeanInitPureExtern LeanPrimTy.bool -- ISize.decLt
  | lean_int64_neg : Int64 → LeanInitPureExtern int64 -- Int64.neg
  | lean_int32_lor : Int32 → Int32 → LeanInitPureExtern int32 -- Int32.lor
  | lean_int8_abs : Int8 → LeanInitPureExtern int8 -- Int8.abs
  | lean_int8_to_int32 : Int8 → LeanInitPureExtern int32 -- Int8.toInt32
  | lean_int32_mod : Int32 → Int32 → LeanInitPureExtern int32 -- Int32.mod
  -- | lean_isize_neg : denote LeanPrimTy.isize → LeanInitPureExtern LeanPrimTy.isize -- ISize.neg
  | lean_int32_to_int : Int32 → LeanInitPureExtern int -- Int32.toInt
  | lean_int64_add : Int64 → Int64 → LeanInitPureExtern int64 -- Int64.add
  | lean_int8_sub : Int8 → Int8 → LeanInitPureExtern int8 -- Int8.sub
  | lean_int32_to_int16 : Int32 → LeanInitPureExtern int16 -- Int32.toInt16
  | lean_int8_to_int64 : Int8 → LeanInitPureExtern int64 -- Int8.toInt64
  | lean_int16_lor : Int16 → Int16 → LeanInitPureExtern int16 -- Int16.lor
  | lean_int64_div : Int64 → Int64 → LeanInitPureExtern int64 -- Int64.div
  -- | lean_int8_to_isize : Int8 → LeanInitPureExtern LeanPrimTy.isize -- Int8.toISize
  -- | lean_isize_dec_eq : denote LeanPrimTy.isize → denote LeanPrimTy.isize → LeanInitPureExtern LeanPrimTy.bool -- ISize.decEq
  | lean_int16_add : Int16 → Int16 → LeanInitPureExtern int16 -- Int16.add
  | lean_int8_of_nat : Nat → LeanInitPureExtern int8 -- Int8.ofNat
  | lean_int8_dec_le : Int8 → Int8 → LeanInitPureExtern LeanPrimTy.bool -- Int8.decLe
  | lean_int16_to_int8 : Int16 → LeanInitPureExtern int8 -- Int16.toInt8
  | lean_int8_to_int : Int8 → LeanInitPureExtern int -- Int8.toInt
  | lean_int8_mul : Int8 → Int8 → LeanInitPureExtern int8 -- Int8.mul
  | lean_int16_neg : Int16 → LeanInitPureExtern int16 -- Int16.neg
  | lean_int64_to_int16 : Int64 → LeanInitPureExtern int16 -- Int64.toInt16
  | lean_int8_land : Int8 → Int8 → LeanInitPureExtern int8 -- Int8.land
  | lean_int32_div : Int32 → Int32 → LeanInitPureExtern int32 -- Int32.div
  | lean_int8_of_int : Int → LeanInitPureExtern int8 -- Int8.ofInt
  -- | lean_int16_to_isize : Int16 → LeanInitPureExtern LeanPrimTy.isize -- Int16.toISize
  | lean_int16_sub : Int16 → Int16 → LeanInitPureExtern int16 -- Int16.sub
  | lean_int16_to_int64 : Int16 → LeanInitPureExtern int64 -- Int16.toInt64
  | lean_int8_lor : Int8 → Int8 → LeanInitPureExtern int8 -- Int8.lor
  | lean_int64_shift_right : Int64 → Int64 → LeanInitPureExtern int64 -- Int64.shiftRight
  --------------------------------------
  -- Init/Data/String/Pattern/Basic.lean
  --------------------------------------
  | lean_string_memcmp : (lhs : String) → (rhs : String) → (lstart : String.Pos.Raw) → (rstart : String.Pos.Raw) → (len : String.Pos.Raw) → len.offsetBy lstart ≤ lhs.rawEndPos → len.offsetBy rstart ≤ rhs.rawEndPos → LeanInitPureExtern LeanPrimTy.bool -- String.Slice.Pattern.Internal.memcmpStr
  ------------------------------
  -- Init/Data/String/Slice.lean
  ------------------------------
  | lean_slice_dec_lt : String.Slice → String.Slice → LeanInitPureExtern LeanPrimTy.bool -- String.Slice.instDecidableLt
  | lean_slice_hash : String.Slice → LeanInitPureExtern uint64 -- String.Slice.hash
  -------------------------------
  -- Init/Data/String/Modify.lean
  -------------------------------
  | lean_string_utf8_set__String_Pos_Raw_set : String → String.Pos.Raw → Char → LeanInitPureExtern string -- String.Pos.Raw.set
  | lean_string_utf8_set__String_Pos_set : {s : String} → (p : s.Pos) → Char → p ≠ s.endPos → LeanInitPureExtern string -- String.Pos.set
  | lean_string_utf8_set__String_set : String → String.Pos.Raw → Char → LeanInitPureExtern string -- String.set
  -----------------------------
  -- Init/Data/Float/Float.lean
  -----------------------------
  | lean_float_frexp : Float → LeanInitPureExtern (prod float int) -- Float.frExp
  | lean_uint8_to_float : UInt8 → LeanInitPureExtern float -- UInt8.toFloat
  | lean_float_to_bits__Float_toModel : Float → LeanInitPureExtern floatModel -- Float.toModel
  | lean_float_to_bits__Float_toBits : Float → LeanInitPureExtern uint64 -- Float.toBits
  | lean_float_of_bits__Float_ofBits : UInt64 → LeanInitPureExtern float -- Float.ofBits
  | lean_float_of_bits__Float_ofModel : Float.Model → LeanInitPureExtern float -- Float.ofModel
  | lean_float_isnan : Float → LeanInitPureExtern LeanPrimTy.bool -- Float.isNaN
  | log10 : Float → LeanInitPureExtern float -- Float.log10
  | cbrt : Float → LeanInitPureExtern float -- Float.cbrt
  | log : Float → LeanInitPureExtern float -- Float.log
  | lean_float_div : Float → Float → LeanInitPureExtern float -- Float.div
  | lean_float_beq : Float → Float → LeanInitPureExtern LeanPrimTy.bool -- Float.beq
  | tan : Float → LeanInitPureExtern float -- Float.tan
  | tanh : Float → LeanInitPureExtern float -- Float.tanh
  | exp2 : Float → LeanInitPureExtern float -- Float.exp2
  | lean_float_to_uint16 : Float → LeanInitPureExtern uint16 -- Float.toUInt16
  | lean_uint32_to_float : UInt32 → LeanInitPureExtern float -- UInt32.toFloat
  | lean_float_decLe__Float_decLe : Float → Float → LeanInitPureExtern LeanPrimTy.bool -- Float.decLe
  | lean_float_decLe__Float_le : Float → Float → LeanInitPureExtern LeanPrimTy.bool -- Float.le
  | lean_float_to_uint64 : Float → LeanInitPureExtern uint64 -- Float.toUInt64
  | sqrt : Float → LeanInitPureExtern float -- Float.sqrt
  | acos : Float → LeanInitPureExtern float -- Float.acos
  | atan : Float → LeanInitPureExtern float -- Float.atan
  | acosh : Float → LeanInitPureExtern float -- Float.acosh
  | floor : Float → LeanInitPureExtern float -- Float.floor
  | fabs : Float → LeanInitPureExtern float -- Float.abs
  | lean_float_to_uint32 : Float → LeanInitPureExtern uint32 -- Float.toUInt32
  | lean_float_to_string : Float → LeanInitPureExtern string -- Float.toString
  | lean_uint64_to_float : UInt64 → LeanInitPureExtern float -- UInt64.toFloat
  | lean_float_decLt__Float_decLt : Float → Float → LeanInitPureExtern LeanPrimTy.bool -- Float.decLt
  | lean_float_decLt__Float_lt : Float → Float → LeanInitPureExtern LeanPrimTy.bool -- Float.lt
  | lean_float_to_uint8 : Float → LeanInitPureExtern uint8 -- Float.toUInt8
  | sin : Float → LeanInitPureExtern float -- Float.sin
  -- | lean_usize_to_float : denote LeanPrimTy.usize → LeanInitPureExtern float -- USize.toFloat
  | cosh : Float → LeanInitPureExtern float -- Float.cosh
  | exp : Float → LeanInitPureExtern float -- Float.exp
  | ceil : Float → LeanInitPureExtern float -- Float.ceil
  -- | lean_float_to_usize : Float → LeanInitPureExtern LeanPrimTy.usize -- Float.toUSize
  | lean_float_isfinite : Float → LeanInitPureExtern LeanPrimTy.bool -- Float.isFinite
  | round : Float → LeanInitPureExtern float -- Float.round
  | cos : Float → LeanInitPureExtern float -- Float.cos
  | log2 : Float → LeanInitPureExtern float -- Float.log2
  | atanh : Float → LeanInitPureExtern float -- Float.atanh
  | atan2 : Float → Float → LeanInitPureExtern float -- Float.atan2
  | sinh : Float → LeanInitPureExtern float -- Float.sinh
  | asinh : Float → LeanInitPureExtern float -- Float.asinh
  | lean_float_mul : Float → Float → LeanInitPureExtern float -- Float.mul
  | lean_uint16_to_float : UInt16 → LeanInitPureExtern float -- UInt16.toFloat
  | asin : Float → LeanInitPureExtern float -- Float.asin
  | pow : Float → Float → LeanInitPureExtern float -- Float.pow
  | lean_float_scaleb : Float → Int → LeanInitPureExtern float -- Float.scaleB
  | lean_float_add : Float → Float → LeanInitPureExtern float -- Float.add
  | lean_float_sub : Float → Float → LeanInitPureExtern float -- Float.sub
  | lean_float_negate : Float → LeanInitPureExtern float -- Float.neg
  | lean_float_isinf : Float → LeanInitPureExtern LeanPrimTy.bool -- Float.isInf
  ----------------------------------
  -- Init/Data/FloatArray/Basic.lean
  ----------------------------------
  -- | lean_mk_empty_float_array : Nat → LeanInitPureExtern floatArray -- FloatArray.emptyWithCapacity -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  -- | lean_float_array_get : FloatArray → Nat → LeanInitPureExtern float -- FloatArray.get! -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  -- | lean_float_array_uget : (a : FloatArray) → (i : USize) → (h : i.toNat < a.size) → LeanInitPureExtern float -- FloatArray.uget -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  -- | lean_float_array_fset : (ds : FloatArray) → (i : Nat) → Float → (h : i < ds.size := by get_elem_tactic) → LeanInitPureExtern floatArray -- FloatArray.set -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  -- | lean_float_array_uset : (a : FloatArray) → (i : USize) → Float → (h : i.toNat < a.size := by get_elem_tactic) → LeanInitPureExtern floatArray -- FloatArray.uset -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  -- | lean_float_array_fget : (ds : FloatArray) → (i : Nat) → (h : i < ds.size := by get_elem_tactic) → LeanInitPureExtern float -- FloatArray.get -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  -- | lean_float_array_set : FloatArray → Nat → Float → LeanInitPureExtern floatArray -- FloatArray.set! -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  -- | lean_float_array_data : FloatArray → LeanInitPureExtern (array float) -- FloatArray.data -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  -- | lean_sarray_size__FloatArray_usize : FloatArray → LeanInitPureExtern LeanPrimTy.usize -- FloatArray.usize
  -- | lean_float_array_mk : Array Float → LeanInitPureExtern floatArray -- FloatArray.mk -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  -- | lean_float_array_size : FloatArray → LeanInitPureExtern nat -- FloatArray.size -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  -- | lean_float_array_push : FloatArray → Float → LeanInitPureExtern floatArray -- FloatArray.push -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  ---------------------------
  -- Init/Data/UInt/Log2.lean
  ---------------------------
  -- | lean_usize_log2 : denote LeanPrimTy.usize → LeanInitPureExtern LeanPrimTy.usize -- USize.log2
  | lean_uint16_log2 : UInt16 → LeanInitPureExtern uint16 -- UInt16.log2
  | lean_uint64_log2 : UInt64 → LeanInitPureExtern uint64 -- UInt64.log2
  | lean_uint8_log2 : UInt8 → LeanInitPureExtern uint8 -- UInt8.log2
  | lean_uint32_log2 : UInt32 → LeanInitPureExtern uint32 -- UInt32.log2
  ----------------------------
  -- Init/Data/SInt/Float.lean
  ----------------------------
  | lean_int32_to_float : Int32 → LeanInitPureExtern float -- Int32.toFloat
  | lean_float_to_int16 : Float → LeanInitPureExtern int16 -- Float.toInt16
  | lean_int16_to_float : Int16 → LeanInitPureExtern float -- Int16.toFloat
  | lean_float_to_int32 : Float → LeanInitPureExtern int32 -- Float.toInt32
  -- | lean_isize_to_float : denote LeanPrimTy.isize → LeanInitPureExtern float -- ISize.toFloat
  | lean_int8_to_float : Int8 → LeanInitPureExtern float -- Int8.toFloat
  | lean_float_to_int8 : Float → LeanInitPureExtern int8 -- Float.toInt8
  | lean_int64_to_float : Int64 → LeanInitPureExtern float -- Int64.toFloat
  | lean_float_to_int64 : Float → LeanInitPureExtern int64 -- Float.toInt64
  -- | lean_float_to_isize : Float → LeanInitPureExtern LeanPrimTy.isize -- Float.toISize
  -------------------------------
  -- Init/Data/Float/Float32.lean
  -------------------------------
  | tanhf : Float32 → LeanInitPureExtern float32 -- Float32.tanh
  | exp2f : Float32 → LeanInitPureExtern float32 -- Float32.exp2
  | lean_float32_div : Float32 → Float32 → LeanInitPureExtern float32 -- Float32.div
  | logf : Float32 → LeanInitPureExtern float32 -- Float32.log
  | lean_float32_decLe__Float32_le : Float32 → Float32 → LeanInitPureExtern LeanPrimTy.bool -- Float32.le
  | lean_float32_decLe__Float32_decLe : Float32 → Float32 → LeanInitPureExtern LeanPrimTy.bool -- Float32.decLe
  | lean_float_to_float32 : Float → LeanInitPureExtern float32 -- Float.toFloat32
  | lean_float32_to_bits__Float32_toModel : Float32 → LeanInitPureExtern float32Model -- Float32.toModel
  | lean_float32_to_bits__Float32_toBits : Float32 → LeanInitPureExtern uint32 -- Float32.toBits
  | lean_float32_of_bits__Float32_ofBits : UInt32 → LeanInitPureExtern float32 -- Float32.ofBits
  | lean_float32_of_bits__Float32_ofModel : Float32.Model → LeanInitPureExtern float32 -- Float32.ofModel
  | atanf : Float32 → LeanInitPureExtern float32 -- Float32.atan
  | acoshf : Float32 → LeanInitPureExtern float32 -- Float32.acosh
  | lean_float32_frexp : Float32 → LeanInitPureExtern (prod float32 int) -- Float32.frExp
  | lean_float32_to_uint64 : Float32 → LeanInitPureExtern uint64 -- Float32.toUInt64
  | lean_float32_sub : Float32 → Float32 → LeanInitPureExtern float32 -- Float32.sub
  | lean_float32_to_uint16 : Float32 → LeanInitPureExtern uint16 -- Float32.toUInt16
  -- | lean_usize_to_float32 : denote LeanPrimTy.usize → LeanInitPureExtern float32 -- USize.toFloat32
  | asinf : Float32 → LeanInitPureExtern float32 -- Float32.asin
  | powf : Float32 → Float32 → LeanInitPureExtern float32 -- Float32.pow
  | lean_float32_beq : Float32 → Float32 → LeanInitPureExtern LeanPrimTy.bool -- Float32.beq
  | lean_uint8_to_float32 : UInt8 → LeanInitPureExtern float32 -- UInt8.toFloat32
  | tanf : Float32 → LeanInitPureExtern float32 -- Float32.tan
  | lean_float32_to_float : Float32 → LeanInitPureExtern float -- Float32.toFloat
  | lean_float32_isnan : Float32 → LeanInitPureExtern LeanPrimTy.bool -- Float32.isNaN
  | log10f : Float32 → LeanInitPureExtern float32 -- Float32.log10
  | cbrtf : Float32 → LeanInitPureExtern float32 -- Float32.cbrt
  | atan2f : Float32 → Float32 → LeanInitPureExtern float32 -- Float32.atan2
  | sinhf : Float32 → LeanInitPureExtern float32 -- Float32.sinh
  | cosf : Float32 → LeanInitPureExtern float32 -- Float32.cos
  | lean_uint32_to_float32 : UInt32 → LeanInitPureExtern float32 -- UInt32.toFloat32
  | lean_float32_isinf : Float32 → LeanInitPureExtern LeanPrimTy.bool -- Float32.isInf
  | lean_float32_negate : Float32 → LeanInitPureExtern float32 -- Float32.neg
  -- | lean_float32_to_usize : Float32 → LeanInitPureExtern LeanPrimTy.usize -- Float32.toUSize
  | ceilf : Float32 → LeanInitPureExtern float32 -- Float32.ceil
  | lean_float32_isfinite : Float32 → LeanInitPureExtern LeanPrimTy.bool -- Float32.isFinite
  | lean_float32_add : Float32 → Float32 → LeanInitPureExtern float32 -- Float32.add
  | lean_float32_scaleb : Float32 → Int → LeanInitPureExtern float32 -- Float32.scaleB
  | sinf : Float32 → LeanInitPureExtern float32 -- Float32.sin
  | lean_float32_mul : Float32 → Float32 → LeanInitPureExtern float32 -- Float32.mul
  | lean_float32_to_string : Float32 → LeanInitPureExtern string -- Float32.toString
  | asinhf : Float32 → LeanInitPureExtern float32 -- Float32.asinh
  | lean_float32_to_uint32 : Float32 → LeanInitPureExtern uint32 -- Float32.toUInt32
  | log2f : Float32 → LeanInitPureExtern float32 -- Float32.log2
  | lean_uint64_to_float32 : UInt64 → LeanInitPureExtern float32 -- UInt64.toFloat32
  | atanhf : Float32 → LeanInitPureExtern float32 -- Float32.atanh
  | floorf : Float32 → LeanInitPureExtern float32 -- Float32.floor
  | fabsf : Float32 → LeanInitPureExtern float32 -- Float32.abs
  | roundf : Float32 → LeanInitPureExtern float32 -- Float32.round
  | lean_float32_decLt__Float32_lt : Float32 → Float32 → LeanInitPureExtern LeanPrimTy.bool -- Float32.lt
  | lean_float32_decLt__Float32_decLt : Float32 → Float32 → LeanInitPureExtern LeanPrimTy.bool -- Float32.decLt
  | acosf : Float32 → LeanInitPureExtern float32 -- Float32.acos
  | sqrtf : Float32 → LeanInitPureExtern float32 -- Float32.sqrt
  | lean_uint16_to_float32 : UInt16 → LeanInitPureExtern float32 -- UInt16.toFloat32
  | coshf : Float32 → LeanInitPureExtern float32 -- Float32.cosh
  | expf : Float32 → LeanInitPureExtern float32 -- Float32.exp
  | lean_float32_to_uint8 : Float32 → LeanInitPureExtern uint8 -- Float32.toUInt8
  ------------------------------
  -- Init/Data/SInt/Float32.lean
  ------------------------------
  | lean_float32_to_int64 : Float32 → LeanInitPureExtern int64 -- Float32.toInt64
  -- | lean_float32_to_isize : Float32 → LeanInitPureExtern LeanPrimTy.isize -- Float32.toISize
  | lean_int32_to_float32 : Int32 → LeanInitPureExtern float32 -- Int32.toFloat32
  | lean_float32_to_int8 : Float32 → LeanInitPureExtern int8 -- Float32.toInt8
  | lean_float32_to_int16 : Float32 → LeanInitPureExtern int16 -- Float32.toInt16
  -- | lean_isize_to_float32 : denote LeanPrimTy.isize → LeanInitPureExtern float32 -- ISize.toFloat32
  | lean_int8_to_float32 : Int8 → LeanInitPureExtern float32 -- Int8.toFloat32
  | lean_float32_to_int32 : Float32 → LeanInitPureExtern int32 -- Float32.toInt32
  | lean_int16_to_float32 : Int16 → LeanInitPureExtern float32 -- Int16.toFloat32
  | lean_int64_to_float32 : Int64 → LeanInitPureExtern float32 -- Int64.toFloat32
  ----------------------------
  -- Init/Data/Ord/String.lean
  ----------------------------
  | lean_string_compare : String → String → LeanInitPureExtern ordering -- String.compare
  ----------------------
  -- Init/System/IO.lean
  ----------------------
  -- | lean_io_process_child_pid : {cfg : IO.Process.StdioConfig} → denote (io_process_child cfg) → LeanInitPureExtern uint32 -- IO.Process.Child.pid
  ---------------------------
  -- Init/System/Promise.lean
  ---------------------------
  -- | lean_io_promise_result_opt : (αt : MyTy) → denote (io_promise αt) → LeanInitPureExtern (task (option αt)) -- IO.Promise.result?
  -- | lean_option_get_or_block : (αt : MyTy) → Option (denote αt) → LeanInitPureExtern αt -- _private.Init.System.Promise.0.IO.Option.getOrBlock!
  ------------------------
  -- Init/ShareCommon.lean
  ------------------------
  -- | lean_sharecommon_quick : (αt : MyTy) → denote αt → LeanInitPureExtern αt -- ShareCommon.shareCommon'
  -- | lean_state_sharecommon : (αt : MyTy) → {σ : shareCommon_stateFactory} → denote (shareCommon_state σ) → denote αt → LeanInitPureExtern (prod αt (shareCommon_state σ)) -- ShareCommon.State.shareCommon
  -- | lean_sharecommon_eq : denote shareCommon_object → denote shareCommon_object → LeanInitPureExtern LeanPrimTy.bool -- ShareCommon.Object.eq
  -- | lean_sharecommon_hash : denote shareCommon_object → LeanInitPureExtern uint64 -- ShareCommon.Object.hash

end LeanScript

end
