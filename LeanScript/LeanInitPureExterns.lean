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
  -- `Lean.Name` is an ordinary inductive of the language (its `LeanScriptTyWf` instance is
  -- in `LeanScript.Ty.Instances`); no entry of the catalogue answers with one
  (leanName : MyTy)
  (ordering : MyTy)
  -- A byte array is `Array UInt8` and a float array is `Array Float`, so neither is a
  -- type former of its own here; the entries that speak about one are commented out
  -- below, and will be supported either through the ordinary array entries or through a
  -- separate API.
  -- (byteArray : MyTy)
  -- (floatArray : MyTy)

/-!
## The catalogue, in two levels

Each `-- Init/…` section of the catalogue is an inductive of its own (a *family*,
`PreludeExtern`, `StringBasicExtern`, …; the long `UInt`/`SInt` sections are split by
width), and `LeanInitPureExtern` has one constructor per family, holding an entry of it.
The constructors of the entries are the families' (`PreludeExtern.lean_nat_add`); the
generated module `LeanScript.LeanInitPureExternShorthands` gives each one a shorthand
in `LeanInitPureExtern`'s own namespace (`LeanInitPureExtern.lean_nat_add a b` is
`.preludeExtern (.lean_nat_add a b)`), usable in patterns as well, so an entry is still written
`.lean_nat_add a b` wherever a `LeanInitPureExtern` is expected.

Two reasons for the split:
* the compiled runtime keeps a constructor's number in 8 bits, and only the numbers
  `0 … 243` are for ordinary constructors, so compiled code cannot build a constructor
  (with fields) numbered past `243`: with one inductive of 460 entries, a definition
  building one of the later ones did not compile ("tag too big");
* a `match` on an inductive is reduced through its recursor, which takes one minor
  premise per constructor, so every call of a 460-way `Extern.eval` instantiated 460
  alternatives; the two-level `Extern.eval` instantiates the families plus one family.

Every family is written against the same parameters as `LeanInitPureExtern`, but only
the ones its entries use are its own parameters (as for any inductive in a `variable`
context), so the constructor of `LeanInitPureExtern` applies each family to those:
when an entry that uses another parameter (`option`, say) is added to a family, add it
there too.  After editing the catalogue, rerun `python3 scripts/gen_externs.py`.
-/

--------------------
-- Init/Prelude.lean
--------------------
/-- The pure externs of `Init/Prelude.lean`. -/
inductive PreludeExtern : MyTy → Type where
  | lean_uint32_of_nat_mk : BitVec 32 → PreludeExtern uint32 -- UInt32.ofBitVec
  | lean_uint32_dec_eq : UInt32 → UInt32 → PreludeExtern LeanPrimTy.bool -- UInt32.decEq
  -- | lean_byte_array_size : ByteArray → PreludeExtern nat -- ByteArray.size -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  -- | lean_string_to_utf8__String_toByteArray : String → PreludeExtern byteArray -- String.toByteArray -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  | lean_uint32_dec_lt : UInt32 → UInt32 → PreludeExtern LeanPrimTy.bool -- UInt32.decLt
  | lean_nat_div : Nat → Nat → PreludeExtern nat -- Nat.div
  -- | lean_sorry : (αt : MyTy) → Bool → PreludeExtern αt -- sorryAx -- XXX: DONT IMPLEMENT
  | lean_uint32_of_nat__UInt32_ofNatLT : (n : Nat) → (h : n < UInt32.size) → PreludeExtern uint32 -- UInt32.ofNatLT
  | lean_uint32_of_nat__Char_ofNatAux : (n : Nat) → (h : n.isValidChar) → PreludeExtern char -- Char.ofNatAux
  | lean_array_get_borrowed : (αt : MyTy) → (inhabited_default : denote αt) → Array (denote αt) → Nat → PreludeExtern αt -- Array.get!InternalBorrowed
  | lean_uint8_to_nat__UInt8_toBitVec : UInt8 → PreludeExtern (bitvec 8) -- UInt8.toBitVec
  | lean_nat_dec_lt : Nat → Nat → PreludeExtern LeanPrimTy.bool -- Nat.decLt
  -- | lean_string_from_utf8_unchecked : (toByteArray : ByteArray) → toByteArray.IsValidUTF8 → PreludeExtern string -- String.ofByteArray -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  | lean_nat_mod__Nat_modCore : Nat → Nat → PreludeExtern nat -- Nat.modCore
  | lean_nat_mod__Nat_mod : Nat → Nat → PreludeExtern nat -- Nat.mod
  | lean_array_push : (αt : MyTy) → Array (denote αt) → denote αt → PreludeExtern (array αt) -- Array.push
  -- | lean_byte_array_mk : Array UInt8 → PreludeExtern byteArray -- ByteArray.mk -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  | lean_nat_sub : Nat → Nat → PreludeExtern nat -- Nat.sub
  | lean_uint8_dec_lt : UInt8 → UInt8 → PreludeExtern LeanPrimTy.bool -- UInt8.decLt
  -- | lean_byte_array_data : ByteArray → PreludeExtern (array uint8) -- ByteArray.data -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  -- | lean_system_platform_nbits : PreludeExtern (lazy nat) -- System.Platform.getNumBits
  | lean_uint32_dec_le : UInt32 → UInt32 → PreludeExtern LeanPrimTy.bool -- UInt32.decLe
  | lean_array_get_size : (αt : MyTy) → Array (denote αt) → PreludeExtern nat -- Array.size
  | lean_array_to_list : (αt : MyTy) → Array (denote αt) → PreludeExtern (list αt) -- Array.toList
  | lean_nat_dec_eq__Nat_decEq : Nat → Nat → PreludeExtern LeanPrimTy.bool -- Nat.decEq
  | lean_nat_dec_eq__Nat_beq : Nat → Nat → PreludeExtern LeanPrimTy.bool -- Nat.beq
  | lean_array_fget_borrowed : (αt : MyTy) → (a : Array (denote αt)) → (i : Nat) → (h : i < a.size) → PreludeExtern αt -- Array.getInternalBorrowed
  | lean_mk_empty_array_with_capacity__Array_emptyWithCapacity : (αt : MyTy) → Nat → PreludeExtern (array αt) -- Array.emptyWithCapacity
  | lean_mk_empty_array_with_capacity__Array_mkEmpty : (αt : MyTy) → Nat → PreludeExtern (array αt) -- Array.mkEmpty
  | lean_uint8_of_nat__UInt8_ofNat : Nat → PreludeExtern uint8 -- UInt8.ofNat
  | lean_uint8_of_nat__UInt8_ofNatLT : (n : Nat) → (h : n < UInt8.size) → PreludeExtern uint8 -- UInt8.ofNatLT
  -- | lean_is_scalar : (αt : MyTy) → denote αt → PreludeExtern LeanPrimTy.bool -- isScalarObj
  | lean_uint8_dec_le : UInt8 → UInt8 → PreludeExtern LeanPrimTy.bool -- UInt8.decLe
  | lean_nat_dec_le__Nat_ble : Nat → Nat → PreludeExtern LeanPrimTy.bool -- Nat.ble
  | lean_nat_dec_le__Nat_decLe : Nat → Nat → PreludeExtern LeanPrimTy.bool -- Nat.decLe
  | lean_array_get : (αt : MyTy) → (inhabited_default : denote αt) → Array (denote αt) → Nat → PreludeExtern αt -- Array.get!Internal
  | lean_nat_add : Nat → Nat → PreludeExtern nat -- Nat.add
  -- | lean_panic_fn_borrowed : (αt : MyTy) → String → PreludeExtern αt -- panicCore
  | lean_uint16_to_nat__UInt16_toBitVec : UInt16 → PreludeExtern (bitvec 16) -- UInt16.toBitVec
  | lean_uint16_of_nat_mk : BitVec 16 → PreludeExtern uint16 -- UInt16.ofBitVec
  | lean_uint16_dec_eq : UInt16 → UInt16 → PreludeExtern LeanPrimTy.bool -- UInt16.decEq
  | lean_string_dec_eq : String → String → PreludeExtern LeanPrimTy.bool -- String.decEq
  | lean_nat_pred : Nat → PreludeExtern nat -- Nat.pred
  -- | lean_usize_of_nat__USize_ofNatLT : (n : Nat) → (h : n < LeanScript.USize_size) → PreludeExtern LeanPrimTy.usize -- USize.ofNatLT
  | lean_string_mk__String_ofList : List Char → PreludeExtern string -- String.ofList
  | lean_string_hash : String → PreludeExtern uint64 -- String.hash
  | lean_uint64_to_nat__UInt64_toBitVec : UInt64 → PreludeExtern (bitvec 64) -- UInt64.toBitVec
  | lean_uint64_of_nat_mk : BitVec 64 → PreludeExtern uint64 -- UInt64.ofBitVec
  | lean_uint32_to_nat__UInt32_toNat : UInt32 → PreludeExtern nat -- UInt32.toNat
  | lean_uint32_to_nat__UInt32_toBitVec : UInt32 → PreludeExtern (bitvec 32) -- UInt32.toBitVec
  | lean_uint64_dec_eq : UInt64 → UInt64 → PreludeExtern LeanPrimTy.bool -- UInt64.decEq
  | lean_uint16_of_nat__UInt16_ofNatLT : (n : Nat) → (h : n < UInt16.size) → PreludeExtern uint16 -- UInt16.ofNatLT
  | lean_name_eq : denote leanName → denote leanName → PreludeExtern LeanPrimTy.bool -- Lean.Name.beq
  | lean_uint8_of_nat_mk : BitVec 8 → PreludeExtern uint8 -- UInt8.ofBitVec
  -- | lean_mk_empty_byte_array : Nat → PreludeExtern byteArray -- ByteArray.emptyWithCapacity -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  | lean_uint8_dec_eq : UInt8 → UInt8 → PreludeExtern LeanPrimTy.bool -- UInt8.decEq
  | lean_nat_pow : Nat → Nat → PreludeExtern nat -- Nat.pow
  -- | lean_usize_dec_eq : denote LeanPrimTy.usize → denote LeanPrimTy.usize → PreludeExtern LeanPrimTy.bool -- USize.decEq
  -- | lean_usize_of_nat_mk : BitVec 64 → PreludeExtern LeanPrimTy.usize -- USize.ofBitVec
  | lean_array_fget : (αt : MyTy) → (a : Array (denote αt)) → (i : Nat) → (h : i < a.size) → PreludeExtern αt -- Array.getInternal
  | lean_nat_mul : Nat → Nat → PreludeExtern nat -- Nat.mul
  -- | lean_usize_to_nat__USize_toBitVec : denote LeanPrimTy.usize → PreludeExtern (bitvec 64) -- USize.toBitVec
  | lean_string_utf8_byte_size : String → PreludeExtern nat -- String.utf8ByteSize
  -- | lean_byte_array_push : ByteArray → UInt8 → PreludeExtern byteArray -- ByteArray.push -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  | lean_array_mk : (αt : MyTy) → List (denote αt) → PreludeExtern (array αt) -- Array.mk
  | lean_uint64_mix_hash : UInt64 → UInt64 → PreludeExtern uint64 -- mixHash
  | lean_uint64_of_nat__UInt64_ofNatLT : (n : Nat) → (h : n < UInt64.size) → PreludeExtern uint64 -- UInt64.ofNatLT

-----------------
-- Init/Core.lean
-----------------
/-- The pure externs of `Init/Core.lean`. -/
inductive CoreExtern : MyTy → Type where
  -- | lean_task_map : (αt : MyTy) → (βt : MyTy) → (denote αt → denote βt) → denote (task αt) → (prio : Task.Priority := Task.Priority.default) → (sync : Bool := false) → CoreExtern (task βt) -- Task.map
  -- | lean_task_spawn : (αt : MyTy) → (denote (lazy αt)) → (prio : Task.Priority := Task.Priority.default) → CoreExtern (task αt) -- Task.spawn
  | lean_strict_or : Bool → Bool → CoreExtern LeanPrimTy.bool -- strictOr
  | lean_thunk_pure : (αt : MyTy) → denote αt → CoreExtern (thunk αt) -- Thunk.pure
  | lean_mk_thunk : (αt : MyTy) → (denote (lazy αt)) → CoreExtern (thunk αt) -- Thunk.mk
  -- | lean_task_get_own : (αt : MyTy) → denote (task αt) → CoreExtern αt -- Task.get
  -- | lean_task_pure : (αt : MyTy) → denote αt → CoreExtern (task αt) -- Task.pure
  | lean_thunk_get_own : (αt : MyTy) → Thunk (denote αt) → CoreExtern αt -- Thunk.get
  | lean_strict_and : Bool → Bool → CoreExtern LeanPrimTy.bool -- strictAnd
  -- | lean_task_bind : (αt : MyTy) → (βt : MyTy) → denote (task αt) → (denote αt → denote (task βt)) → (prio : Task.Priority := Task.Priority.default) → (sync : Bool := false) → CoreExtern (task βt) -- Task.bind

---------------------------
-- Init/Data/Int/Basic.lean
---------------------------
/-- The pure externs of `Init/Data/Int/Basic.lean`. -/
inductive IntBasicExtern : MyTy → Type where
  | lean_nat_to_int : Nat → IntBasicExtern int -- Int.ofNat
  | lean_int_dec_le : Int → Int → IntBasicExtern LeanPrimTy.bool -- Int.decLe
  | lean_int_dec_lt : Int → Int → IntBasicExtern LeanPrimTy.bool -- Int.decLt
  | lean_int_dec_eq : Int → Int → IntBasicExtern LeanPrimTy.bool -- Int.decEq
  | lean_int_mul : Int → Int → IntBasicExtern int -- Int.mul
  | lean_int_dec_nonneg : Int → IntBasicExtern LeanPrimTy.bool -- Int.decNonneg
  | lean_int_neg_succ_of_nat : Nat → IntBasicExtern int -- Int.negSucc
  | lean_int_add : Int → Int → IntBasicExtern int -- Int.add
  | lean_int_neg : Int → IntBasicExtern int -- Int.neg
  | lean_int_sub : Int → Int → IntBasicExtern int -- Int.sub
  | lean_nat_abs : Int → IntBasicExtern nat -- Int.natAbs

-------------------------------
-- Init/Data/Nat/Div/Basic.lean
-------------------------------
/-- The pure externs of `Init/Data/Nat/Div/Basic.lean`. -/
inductive NatDivExtern : MyTy → Type where
  | lean_nat_div_exact : (x : Nat) → (y : Nat) → (h : y ∣ x) → NatDivExtern nat -- Nat.divExact

-----------------------------------
-- Init/Data/Nat/Bitwise/Basic.lean
-----------------------------------
/-- The pure externs of `Init/Data/Nat/Bitwise/Basic.lean`. -/
inductive NatBitwiseExtern : MyTy → Type where
  | lean_nat_lxor : Nat → Nat → NatBitwiseExtern nat -- Nat.xor
  | lean_nat_shiftl : Nat → Nat → NatBitwiseExtern nat -- Nat.shiftLeft
  | lean_nat_shiftr : Nat → Nat → NatBitwiseExtern nat -- Nat.shiftRight
  | lean_nat_land : Nat → Nat → NatBitwiseExtern nat -- Nat.land
  | lean_nat_lor : Nat → Nat → NatBitwiseExtern nat -- Nat.lor

-------------------------------
-- Init/Data/UInt/BasicAux.lean
-------------------------------
/-- The pure externs of `Init/Data/UInt/BasicAux.lean`. -/
inductive UIntBasicAuxExtern : MyTy → Type where
  | lean_uint64_to_nat__UInt64_toNat : UInt64 → UIntBasicAuxExtern nat -- UInt64.toNat
  | lean_uint32_to_uint8 : UInt32 → UIntBasicAuxExtern uint8 -- UInt32.toUInt8
  -- | lean_usize_to_nat__USize_toNat : denote LeanPrimTy.usize → UIntBasicAuxExtern nat -- USize.toNat
  | lean_uint64_to_uint32 : UInt64 → UIntBasicAuxExtern uint32 -- UInt64.toUInt32
  | lean_uint32_to_uint16 : UInt32 → UIntBasicAuxExtern uint16 -- UInt32.toUInt16
  | lean_uint16_to_uint32 : UInt16 → UIntBasicAuxExtern uint32 -- UInt16.toUInt32
  | lean_uint32_to_uint64 : UInt32 → UIntBasicAuxExtern uint64 -- UInt32.toUInt64
  | lean_uint32_of_nat__UInt32_ofNat : Nat → UIntBasicAuxExtern uint32 -- UInt32.ofNat
  -- | lean_usize_add : denote LeanPrimTy.usize → denote LeanPrimTy.usize → UIntBasicAuxExtern LeanPrimTy.usize -- USize.add
  | lean_uint32_sub : UInt32 → UInt32 → UIntBasicAuxExtern uint32 -- UInt32.sub
  | lean_uint16_to_nat__UInt16_toNat : UInt16 → UIntBasicAuxExtern nat -- UInt16.toNat
  | lean_uint16_to_uint8 : UInt16 → UIntBasicAuxExtern uint8 -- UInt16.toUInt8
  -- | lean_usize_sub : denote LeanPrimTy.usize → denote LeanPrimTy.usize → UIntBasicAuxExtern LeanPrimTy.usize -- USize.sub
  | lean_uint32_add : UInt32 → UInt32 → UIntBasicAuxExtern uint32 -- UInt32.add
  -- | lean_usize_of_nat__USize_ofNat : Nat → UIntBasicAuxExtern LeanPrimTy.usize -- USize.ofNat
  -- | lean_usize_dec_le : denote LeanPrimTy.usize → denote LeanPrimTy.usize → UIntBasicAuxExtern LeanPrimTy.bool -- USize.decLe
  | lean_uint8_to_uint64 : UInt8 → UIntBasicAuxExtern uint64 -- UInt8.toUInt64
  | lean_uint8_to_nat__UInt8_toNat : UInt8 → UIntBasicAuxExtern nat -- UInt8.toNat
  | lean_uint64_of_nat__UInt64_ofNat : Nat → UIntBasicAuxExtern uint64 -- UInt64.ofNat
  | lean_uint8_to_uint32 : UInt8 → UIntBasicAuxExtern uint32 -- UInt8.toUInt32
  | lean_uint16_of_nat__UInt16_ofNat : Nat → UIntBasicAuxExtern uint16 -- UInt16.ofNat
  | lean_uint16_to_uint64 : UInt16 → UIntBasicAuxExtern uint64 -- UInt16.toUInt64
  -- | lean_usize_dec_lt : denote LeanPrimTy.usize → denote LeanPrimTy.usize → UIntBasicAuxExtern LeanPrimTy.bool -- USize.decLt
  | lean_uint64_to_uint8 : UInt64 → UIntBasicAuxExtern uint8 -- UInt64.toUInt8
  | lean_uint64_to_uint16 : UInt64 → UIntBasicAuxExtern uint16 -- UInt64.toUInt16
  | lean_uint8_to_uint16 : UInt8 → UIntBasicAuxExtern uint16 -- UInt8.toUInt16

----------------------------------
-- Init/Data/String/Bootstrap.lean
----------------------------------
/-- The pure externs of `Init/Data/String/Bootstrap.lean`. -/
inductive StringBootstrapExtern : MyTy → Type where
  | lean_string_utf8_get__String_Internal_get : String → String.Pos.Raw → StringBootstrapExtern char -- String.Internal.get
  | lean_string_trim : String → StringBootstrapExtern string -- String.Internal.trim
  | lean_substring_drop : Substring.Raw → Nat → StringBootstrapExtern substringRaw -- Substring.Raw.Internal.drop
  | lean_substring_prev : Substring.Raw → String.Pos.Raw → StringBootstrapExtern stringPosRaw -- Substring.Raw.Internal.prev
  | lean_substring_extract : Substring.Raw → String.Pos.Raw → String.Pos.Raw → StringBootstrapExtern substringRaw -- Substring.Raw.Internal.extract
  | lean_string_foldl : (String → Char → String) → String → String → StringBootstrapExtern string -- String.Internal.foldl
  | lean_substring_tostring : Substring.Raw → StringBootstrapExtern string -- Substring.Raw.Internal.toString
  | lean_string_append__String_Internal_append : String → String → StringBootstrapExtern string -- String.Internal.append
  | lean_string_get_byte_fast__String_Internal_getUTF8Byte : (s : String) → (n : Nat) → (h : n < s.utf8ByteSize) → StringBootstrapExtern uint8 -- String.Internal.getUTF8Byte
  | lean_string_isempty : String → StringBootstrapExtern LeanPrimTy.bool -- String.Internal.isEmpty
  | lean_string_push : String → Char → StringBootstrapExtern string -- String.push
  | lean_string_isprefixof : String → String → StringBootstrapExtern LeanPrimTy.bool -- String.Internal.isPrefixOf
  | lean_string_dropright : String → Nat → StringBootstrapExtern string -- String.Internal.dropRight
  | lean_substring_takewhile : Substring.Raw → (Char → Bool) → StringBootstrapExtern substringRaw -- Substring.Raw.Internal.takeWhile
  | lean_substring_get : Substring.Raw → String.Pos.Raw → StringBootstrapExtern char -- Substring.Raw.Internal.get
  -- `USize` is `Nat` here, so this is `lean_string_get_byte_fast__String_Internal_getUTF8Byte`; `#leanscript_to_term` translates a call of `String.Internal.ugetUTF8Byte` to that entry
  -- | lean_string_uget_byte_fast : (s : String) → (n : Nat) → (h : n < s.utf8ByteSize) → StringBootstrapExtern uint8 -- String.Internal.ugetUTF8Byte
  | lean_string_contains : String → Char → StringBootstrapExtern LeanPrimTy.bool -- String.Internal.contains
  | lean_string_front : String → StringBootstrapExtern char -- String.Internal.front
  | lean_string_posof : String → Char → StringBootstrapExtern stringPosRaw -- String.Internal.posOf
  | lean_substring_all : Substring.Raw → (Char → Bool) → StringBootstrapExtern LeanPrimTy.bool -- Substring.Raw.Internal.all
  | lean_string_intercalate : String → List String → StringBootstrapExtern string -- String.Internal.intercalate
  | lean_string_drop : String → Nat → StringBootstrapExtern string -- String.Internal.drop
  | lean_string_length__String_Internal_length : String → StringBootstrapExtern nat -- String.Internal.length
  | lean_string_utf8_at_end__String_Internal_atEnd : String → String.Pos.Raw → StringBootstrapExtern LeanPrimTy.bool -- String.Internal.atEnd
  | lean_substring_beq : Substring.Raw → Substring.Raw → StringBootstrapExtern LeanPrimTy.bool -- Substring.Raw.Internal.beq
  | lean_string_nextwhile : String → (Char → Bool) → String.Pos.Raw → StringBootstrapExtern stringPosRaw -- String.Internal.nextWhile
  | lean_string_utf8_next__String_Internal_next : String → String.Pos.Raw → StringBootstrapExtern stringPosRaw -- String.Internal.next
  | lean_string_mk__String_mk : List Char → StringBootstrapExtern string -- String.mk
  | lean_string_any : String → (Char → Bool) → StringBootstrapExtern LeanPrimTy.bool -- String.Internal.any
  | lean_string_pushn : String → Char → Nat → StringBootstrapExtern string -- String.Internal.pushn
  | lean_string_capitalize : String → StringBootstrapExtern string -- String.Internal.capitalize
  | lean_string_utf8_extract__String_Internal_extract : String → String.Pos.Raw → String.Pos.Raw → StringBootstrapExtern string -- String.Internal.extract
  | lean_string_pos_min : String.Pos.Raw → String.Pos.Raw → StringBootstrapExtern stringPosRaw -- String.Pos.Raw.Internal.min
  | lean_substring_front : Substring.Raw → StringBootstrapExtern char -- Substring.Raw.Internal.front
  | lean_string_pos_sub : String.Pos.Raw → String.Pos.Raw → StringBootstrapExtern stringPosRaw -- String.Pos.Raw.Internal.sub
  | lean_substring_isempty : Substring.Raw → StringBootstrapExtern LeanPrimTy.bool -- Substring.Raw.Internal.isEmpty
  | lean_string_offsetofpos : String → String.Pos.Raw → StringBootstrapExtern nat -- String.Internal.offsetOfPos

----------------------
-- Init/Data/Repr.lean: every entry is commented out, so it has no family
----------------------
-- | lean_string_of_usize : denote LeanPrimTy.usize → LeanInitPureExtern string -- USize.repr

-----------------
-- Init/Util.lean
-----------------
/-- The pure externs of `Init/Util.lean`. -/
inductive UtilExtern : MyTy → Type where
  -- | lean_dbg_sleep : (αt : MyTy) → UInt32 → (denote (lazy αt)) → UtilExtern αt -- dbgSleep
  -- | lean_ptr_addr : (αt : MyTy) → denote αt → UtilExtern LeanPrimTy.usize -- ptrAddrUnsafe
  -- | lean_dbg_trace : (αt : MyTy) → String → (denote (lazy αt)) → UtilExtern αt -- dbgTrace
  | lean_dbg_trace_if_shared : (αt : MyTy) → String → denote αt → UtilExtern αt -- dbgTraceIfShared
  -- | lean_dbg_stack_trace : (αt : MyTy) → (denote (lazy αt)) → UtilExtern αt -- dbgStackTrace
  -- | lean_is_exclusive_obj : (αt : MyTy) → denote αt → UtilExtern LeanPrimTy.bool -- isExclusiveUnsafe

---------------------------
-- Init/Data/Array/Set.lean
---------------------------
/-- The pure externs of `Init/Data/Array/Set.lean`. -/
inductive ArraySetExtern : MyTy → Type where
  | lean_array_set : (αt : MyTy) → Array (denote αt) → Nat → denote αt → ArraySetExtern (array αt) -- Array.set!
  | lean_array_fset : (αt : MyTy) → (xs : Array (denote αt)) → (i : Nat) → denote αt → (h : i < xs.size := by get_elem_tactic) → ArraySetExtern (array αt) -- Array.set

-----------------------------
-- Init/Data/Array/Basic.lean
-----------------------------
/-- The pure externs of `Init/Data/Array/Basic.lean`. -/
inductive ArrayBasicExtern : MyTy → Type where
  | lean_array_fswap : (αt : MyTy) → (xs : Array (denote αt)) → (i : Nat) → (j : Nat) → (h : i < xs.size := by get_elem_tactic) → (h : j < xs.size := by get_elem_tactic) → ArrayBasicExtern (array αt) -- Array.swap
  -- `USize` is `Nat` here, so this is `lean_array_fget`; `#leanscript_to_term` translates a call of `Array.uget` to that entry
  -- | lean_array_uget : (αt : MyTy) → (xs : Array (denote αt)) → (i : Nat) → (h : i < xs.size) → ArrayBasicExtern αt -- Array.uget
  | lean_mk_array : (αt : MyTy) → Nat → denote αt → ArrayBasicExtern (array αt) -- Array.replicate
  | lean_array_swap : (αt : MyTy) → Array (denote αt) → Nat → Nat → ArrayBasicExtern (array αt) -- Array.swapIfInBounds
  -- | lean_array_uget_borrowed : (αt : MyTy) → (xs : Array (denote αt)) → (i : Nat) → (h : i < xs.size) → ArrayBasicExtern αt -- Array.ugetBorrowed
  | lean_array_pop : (αt : MyTy) → Array (denote αt) → ArrayBasicExtern (array αt) -- Array.pop
  -- `USize` is `Nat` here, so this is `lean_array_fset`; `#leanscript_to_term` translates a call of `Array.uset` to that entry
  -- | lean_array_uset : (αt : MyTy) → (xs : Array (denote αt)) → (i : Nat) → denote αt → (h : i < xs.size) → ArrayBasicExtern (array αt) -- Array.uset
  -- | lean_array_size : (αt : MyTy) → Array (denote αt) → ArrayBasicExtern LeanPrimTy.usize -- Array.usize

----------------------
-- Init/Meta/Defs.lean
----------------------
/-- The pure externs of `Init/Meta/Defs.lean`. -/
inductive MetaDefsExtern : MyTy → Type where
  | lean_version_get_special_desc : MetaDefsExtern (lazy string) -- Lean.version.getSpecialDesc
  | lean_version_get_is_release : MetaDefsExtern (lazy LeanPrimTy.bool) -- Lean.version.getIsRelease
  | lean_version_get_major : MetaDefsExtern (lazy nat) -- _private.Init.Meta.Defs.0.Lean.version.getMajor
  | lean_version_get_patch : MetaDefsExtern (lazy nat) -- _private.Init.Meta.Defs.0.Lean.version.getPatch
  | lean_internal_is_stage0 : MetaDefsExtern (lazy LeanPrimTy.bool) -- Lean.Internal.isStage0
  | lean_version_get_minor : MetaDefsExtern (lazy nat) -- _private.Init.Meta.Defs.0.Lean.version.getMinor
  | lean_get_githash : MetaDefsExtern (lazy string) -- Lean.getGithash
  | lean_internal_has_llvm_backend : MetaDefsExtern (lazy LeanPrimTy.bool) -- Lean.Internal.hasLLVMBackend

--------------------------
-- Init/Data/Nat/Log2.lean
--------------------------
/-- The pure externs of `Init/Data/Nat/Log2.lean`. -/
inductive NatLog2Extern : MyTy → Type where
  | lean_nat_log2 : Nat → NatLog2Extern nat -- Nat.log2

----------------------------------
-- Init/Data/Int/DivMod/Basic.lean
----------------------------------
/-- The pure externs of `Init/Data/Int/DivMod/Basic.lean`. -/
inductive IntDivModExtern : MyTy → Type where
  | lean_int_emod : Int → Int → IntDivModExtern int -- Int.emod
  | lean_int_div_exact : (x : Int) → (y : Int) → (h : y ∣ x) → IntDivModExtern int -- Int.divExact
  | lean_int_mod : Int → Int → IntDivModExtern int -- Int.tmod
  | lean_int_ediv : Int → Int → IntDivModExtern int -- Int.ediv
  | lean_int_div : Int → Int → IntDivModExtern int -- Int.tdiv

-------------------------
-- Init/Data/Nat/Gcd.lean: every entry is commented out, so it has no family
-------------------------
-- `Nat.gcd` is translated as an ordinary function (from its definition, as if it had no
-- `@[extern]`), and `#leanscript_to_term` reads `Nat.gcd._unary` as `Nat.gcd`
-- | lean_nat_gcd__Nat_gcd__unary : (_ : Nat) ×' Nat → LeanInitPureExtern nat -- Nat.gcd._unary
-- | lean_nat_gcd__Nat_gcd : Nat → Nat → LeanInitPureExtern nat -- Nat.gcd

-------------------------------------------------
-- Init/Data/UInt/Basic.lean, the `UInt8` entries
-------------------------------------------------
/-- The pure externs of `Init/Data/UInt/Basic.lean`, on `UInt8`. -/
inductive UInt8BasicExtern : MyTy → Type where
  | lean_uint8_sub : UInt8 → UInt8 → UInt8BasicExtern uint8 -- UInt8.sub
  | lean_uint8_neg : UInt8 → UInt8BasicExtern uint8 -- UInt8.neg
  | lean_uint8_lor : UInt8 → UInt8 → UInt8BasicExtern uint8 -- UInt8.lor
  | lean_uint8_div : UInt8 → UInt8 → UInt8BasicExtern uint8 -- UInt8.div
  | lean_uint8_shift_right : UInt8 → UInt8 → UInt8BasicExtern uint8 -- UInt8.shiftRight
  | lean_uint8_shift_left : UInt8 → UInt8 → UInt8BasicExtern uint8 -- UInt8.shiftLeft
  | lean_uint8_land : UInt8 → UInt8 → UInt8BasicExtern uint8 -- UInt8.land
  | lean_uint8_mul : UInt8 → UInt8 → UInt8BasicExtern uint8 -- UInt8.mul
  | lean_uint8_add : UInt8 → UInt8 → UInt8BasicExtern uint8 -- UInt8.add
  | lean_uint8_complement : UInt8 → UInt8BasicExtern uint8 -- UInt8.complement
  | lean_uint8_mod : UInt8 → UInt8 → UInt8BasicExtern uint8 -- UInt8.mod
  | lean_bool_to_uint8 : Bool → UInt8BasicExtern uint8 -- Bool.toUInt8
  | lean_uint8_xor : UInt8 → UInt8 → UInt8BasicExtern uint8 -- UInt8.xor

--------------------------------------------------
-- Init/Data/UInt/Basic.lean, the `UInt16` entries
--------------------------------------------------
/-- The pure externs of `Init/Data/UInt/Basic.lean`, on `UInt16`. -/
inductive UInt16BasicExtern : MyTy → Type where
  | lean_uint16_neg : UInt16 → UInt16BasicExtern uint16 -- UInt16.neg
  | lean_uint16_add : UInt16 → UInt16 → UInt16BasicExtern uint16 -- UInt16.add
  | lean_uint16_lor : UInt16 → UInt16 → UInt16BasicExtern uint16 -- UInt16.lor
  | lean_uint16_mul : UInt16 → UInt16 → UInt16BasicExtern uint16 -- UInt16.mul
  | lean_uint16_land : UInt16 → UInt16 → UInt16BasicExtern uint16 -- UInt16.land
  | lean_uint16_complement : UInt16 → UInt16BasicExtern uint16 -- UInt16.complement
  | lean_uint16_xor : UInt16 → UInt16 → UInt16BasicExtern uint16 -- UInt16.xor
  | lean_uint16_shift_left : UInt16 → UInt16 → UInt16BasicExtern uint16 -- UInt16.shiftLeft
  | lean_uint16_mod : UInt16 → UInt16 → UInt16BasicExtern uint16 -- UInt16.mod
  | lean_uint16_dec_lt : UInt16 → UInt16 → UInt16BasicExtern LeanPrimTy.bool -- UInt16.decLt
  | lean_uint16_div : UInt16 → UInt16 → UInt16BasicExtern uint16 -- UInt16.div
  | lean_uint16_dec_le : UInt16 → UInt16 → UInt16BasicExtern LeanPrimTy.bool -- UInt16.decLe
  | lean_uint16_sub : UInt16 → UInt16 → UInt16BasicExtern uint16 -- UInt16.sub
  | lean_bool_to_uint16 : Bool → UInt16BasicExtern uint16 -- Bool.toUInt16
  | lean_uint16_shift_right : UInt16 → UInt16 → UInt16BasicExtern uint16 -- UInt16.shiftRight

--------------------------------------------------
-- Init/Data/UInt/Basic.lean, the `UInt32` entries
--------------------------------------------------
/-- The pure externs of `Init/Data/UInt/Basic.lean`, on `UInt32`. -/
inductive UInt32BasicExtern : MyTy → Type where
  | lean_uint32_mod : UInt32 → UInt32 → UInt32BasicExtern uint32 -- UInt32.mod
  | lean_bool_to_uint32 : Bool → UInt32BasicExtern uint32 -- Bool.toUInt32
  | lean_uint32_div : UInt32 → UInt32 → UInt32BasicExtern uint32 -- UInt32.div
  | lean_uint32_shift_right : UInt32 → UInt32 → UInt32BasicExtern uint32 -- UInt32.shiftRight
  | lean_uint32_neg : UInt32 → UInt32BasicExtern uint32 -- UInt32.neg
  | lean_uint32_lor : UInt32 → UInt32 → UInt32BasicExtern uint32 -- UInt32.lor
  | lean_uint32_xor : UInt32 → UInt32 → UInt32BasicExtern uint32 -- UInt32.xor
  | lean_uint32_shift_left : UInt32 → UInt32 → UInt32BasicExtern uint32 -- UInt32.shiftLeft
  | lean_uint32_mul : UInt32 → UInt32 → UInt32BasicExtern uint32 -- UInt32.mul
  | lean_uint32_land : UInt32 → UInt32 → UInt32BasicExtern uint32 -- UInt32.land
  | lean_uint32_complement : UInt32 → UInt32BasicExtern uint32 -- UInt32.complement

--------------------------------------------------
-- Init/Data/UInt/Basic.lean, the `UInt64` entries
--------------------------------------------------
/-- The pure externs of `Init/Data/UInt/Basic.lean`, on `UInt64`. -/
inductive UInt64BasicExtern : MyTy → Type where
  | lean_uint64_shift_left : UInt64 → UInt64 → UInt64BasicExtern uint64 -- UInt64.shiftLeft
  -- | lean_usize_land : denote LeanPrimTy.usize → denote LeanPrimTy.usize → UInt64BasicExtern LeanPrimTy.usize -- USize.land
  -- | lean_usize_mul : denote LeanPrimTy.usize → denote LeanPrimTy.usize → UInt64BasicExtern LeanPrimTy.usize -- USize.mul
  -- | lean_uint16_to_usize : UInt16 → UInt64BasicExtern LeanPrimTy.usize -- UInt16.toUSize
  | lean_uint64_shift_right : UInt64 → UInt64 → UInt64BasicExtern uint64 -- UInt64.shiftRight
  -- | lean_usize_shift_left : denote LeanPrimTy.usize → denote LeanPrimTy.usize → UInt64BasicExtern LeanPrimTy.usize -- USize.shiftLeft
  -- | lean_usize_xor : denote LeanPrimTy.usize → denote LeanPrimTy.usize → UInt64BasicExtern LeanPrimTy.usize -- USize.xor
  | lean_uint64_complement : UInt64 → UInt64BasicExtern uint64 -- UInt64.complement
  | lean_uint64_add : UInt64 → UInt64 → UInt64BasicExtern uint64 -- UInt64.add
  | lean_uint64_lor : UInt64 → UInt64 → UInt64BasicExtern uint64 -- UInt64.lor
  | lean_uint64_mod : UInt64 → UInt64 → UInt64BasicExtern uint64 -- UInt64.mod
  -- | lean_usize_lor : denote LeanPrimTy.usize → denote LeanPrimTy.usize → UInt64BasicExtern LeanPrimTy.usize -- USize.lor
  -- | lean_usize_neg : denote LeanPrimTy.usize → UInt64BasicExtern LeanPrimTy.usize -- USize.neg
  | lean_uint64_div : UInt64 → UInt64 → UInt64BasicExtern uint64 -- UInt64.div
  -- | lean_usize_to_uint64 : denote LeanPrimTy.usize → UInt64BasicExtern uint64 -- USize.toUInt64
  | lean_uint64_mul : UInt64 → UInt64 → UInt64BasicExtern uint64 -- UInt64.mul
  -- | lean_usize_shift_right : denote LeanPrimTy.usize → denote LeanPrimTy.usize → UInt64BasicExtern LeanPrimTy.usize -- USize.shiftRight
  | lean_uint64_land : UInt64 → UInt64 → UInt64BasicExtern uint64 -- UInt64.land
  | lean_bool_to_uint64 : Bool → UInt64BasicExtern uint64 -- Bool.toUInt64
  | lean_uint64_dec_le : UInt64 → UInt64 → UInt64BasicExtern LeanPrimTy.bool -- UInt64.decLe
  -- | lean_usize_of_nat__USize_ofNat32 : (n : Nat) → (h : n < 4294967296) → UInt64BasicExtern LeanPrimTy.usize -- USize.ofNat32
  | lean_uint64_sub : UInt64 → UInt64 → UInt64BasicExtern uint64 -- UInt64.sub
  | lean_uint64_neg : UInt64 → UInt64BasicExtern uint64 -- UInt64.neg
  -- | lean_usize_div : denote LeanPrimTy.usize → denote LeanPrimTy.usize → UInt64BasicExtern LeanPrimTy.usize -- USize.div
  -- | lean_uint32_to_usize : UInt32 → UInt64BasicExtern LeanPrimTy.usize -- UInt32.toUSize
  -- | lean_usize_to_uint16 : denote LeanPrimTy.usize → UInt64BasicExtern uint16 -- USize.toUInt16
  -- | lean_usize_to_uint8 : denote LeanPrimTy.usize → UInt64BasicExtern uint8 -- USize.toUInt8
  -- | lean_usize_mod : denote LeanPrimTy.usize → denote LeanPrimTy.usize → UInt64BasicExtern LeanPrimTy.usize -- USize.mod
  | lean_uint64_dec_lt : UInt64 → UInt64 → UInt64BasicExtern LeanPrimTy.bool -- UInt64.decLt
  -- | lean_uint8_to_usize : UInt8 → UInt64BasicExtern LeanPrimTy.usize -- UInt8.toUSize
  -- | lean_bool_to_usize : Bool → UInt64BasicExtern LeanPrimTy.usize -- Bool.toUSize
  -- | lean_uint64_to_usize : UInt64 → UInt64BasicExtern LeanPrimTy.usize -- UInt64.toUSize
  -- | lean_usize_to_uint32 : denote LeanPrimTy.usize → UInt64BasicExtern uint32 -- USize.toUInt32
  -- | lean_usize_complement : denote LeanPrimTy.usize → UInt64BasicExtern LeanPrimTy.usize -- USize.complement
  | lean_uint64_xor : UInt64 → UInt64 → UInt64BasicExtern uint64 -- UInt64.xor

---------------------------------
-- Init/Data/ByteArray/Basic.lean: every entry is commented out, so it has no family
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
/-- The pure externs of `Init/Data/String/PosRaw.lean`. -/
inductive StringPosRawExtern : MyTy → Type where
  | lean_string_get_byte_fast__String_getUtf8Byte : (s : String) → (p : String.Pos.Raw) → (h : p < s.rawEndPos) → StringPosRawExtern uint8 -- String.getUtf8Byte
  | lean_string_get_byte_fast__String_getUTF8Byte : (s : String) → (p : String.Pos.Raw) → (h : p < s.rawEndPos) → StringPosRawExtern uint8 -- String.getUTF8Byte

-----------------------------
-- Init/Data/String/Defs.lean
-----------------------------
/-- The pure externs of `Init/Data/String/Defs.lean`. -/
inductive StringDefsExtern : MyTy → Type where
  -- | lean_string_to_utf8__String_toUTF8 : String → StringDefsExtern byteArray -- String.toUTF8 -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  | lean_string_append__String_append : String → String → StringDefsExtern string -- String.append

----------------------------
-- Init/System/Platform.lean
----------------------------
/-- The pure externs of `Init/System/Platform.lean`. -/
inductive PlatformExtern : MyTy → Type where
  -- | lean_internal_get_hardware_concurrency : PlatformExtern (lazy uint32) -- System.Platform.Internal.getHardwareConcurrency
  -- | lean_system_platform_linux : PlatformExtern (lazy LeanPrimTy.bool) -- System.Platform.getIsLinux
  | lean_system_platform_emscripten : PlatformExtern (lazy LeanPrimTy.bool) -- System.Platform.getIsEmscripten
  | lean_system_platform_target : PlatformExtern (lazy string) -- System.Platform.getTarget
  -- | lean_system_platform_windows : PlatformExtern (lazy LeanPrimTy.bool) -- System.Platform.getIsWindows
  -- | lean_system_platform_osx : PlatformExtern (lazy LeanPrimTy.bool) -- System.Platform.getIsOSX

------------------------------
-- Init/Data/String/Basic.lean
------------------------------
/-- The pure externs of `Init/Data/String/Basic.lean`. -/
inductive StringBasicExtern : MyTy → Type where
  | lean_string_utf8_next__String_next : String → String.Pos.Raw → StringBasicExtern stringPosRaw -- String.next
  | lean_string_utf8_next__String_Pos_Raw_next : String → String.Pos.Raw → StringBasicExtern stringPosRaw -- String.Pos.Raw.next
  | lean_string_utf8_get__String_Pos_Raw_get : String → String.Pos.Raw → StringBasicExtern char -- String.Pos.Raw.get
  | lean_string_utf8_get__String_get : String → String.Pos.Raw → StringBasicExtern char -- String.get
  | lean_string_utf8_get_opt__String_Pos_Raw_get? : String → String.Pos.Raw → StringBasicExtern (option char) -- String.Pos.Raw.get?
  | lean_string_utf8_get_opt__String_get? : String → String.Pos.Raw → StringBasicExtern (option char) -- String.get?
  | lean_string_utf8_prev__String_Pos_Raw_prev : String → String.Pos.Raw → StringBasicExtern stringPosRaw -- String.Pos.Raw.prev
  | lean_string_utf8_prev__String_prev : String → String.Pos.Raw → StringBasicExtern stringPosRaw -- String.prev
  | lean_string_utf8_next_fast__String_next' : (s : String) → (p : String.Pos.Raw) → (h : ¬String.Pos.Raw.atEnd s p = Bool.true) → StringBasicExtern stringPosRaw -- String.next'
  -- the same function as `lean_string_utf8_next_fast__String_next'`; `#leanscript_to_term` translates a call of `String.Pos.Raw.next'` to that entry
  -- | lean_string_utf8_next_fast__String_Pos_Raw_next' : (s : String) → (p : String.Pos.Raw) → (h : ¬String.Pos.Raw.atEnd s p = Bool.true) → StringBasicExtern stringPosRaw -- String.Pos.Raw.next'
  | lean_string_utf8_next_fast__String_Pos_next : {s : String} → (pos : s.Pos) → (h : pos ≠ s.endPos) → StringBasicExtern (LeanPrimTy.stringPos s) -- String.Pos.next
  | lean_string_data__String_data : String → StringBasicExtern (list char) -- String.data
  | lean_string_data__String_toList : String → StringBasicExtern (list char) -- String.toList
  | lean_string_utf8_extract_fast : {s : String} → s.Pos → s.Pos → StringBasicExtern string -- String.extract
  | lean_string_utf8_at_end__String_atEnd : String → String.Pos.Raw → StringBasicExtern LeanPrimTy.bool -- String.atEnd
  | lean_string_utf8_at_end__String_Pos_Raw_atEnd : String → String.Pos.Raw → StringBasicExtern LeanPrimTy.bool -- String.Pos.Raw.atEnd
  | lean_string_utf8_get_bang__String_Pos_Raw_get! : String → String.Pos.Raw → StringBasicExtern char -- String.Pos.Raw.get!
  | lean_string_utf8_get_bang__String_get! : String → String.Pos.Raw → StringBasicExtern char -- String.get!
  -- | lean_string_utf8_get_fast__String_decodeChar : (s : String) → (byteIdx : Nat) → (h : (s.toByteArray.utf8DecodeChar? byteIdx).isSome = Bool.true) → StringBasicExtern char -- String.decodeChar -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  | lean_string_utf8_get_fast__String_get' : (s : String) → (p : String.Pos.Raw) → (h : ¬String.Pos.Raw.atEnd s p = Bool.true) → StringBasicExtern char -- String.get'
  | lean_string_utf8_get_fast__String_Pos_Raw_get' : (s : String) → (p : String.Pos.Raw) → (h : ¬String.Pos.Raw.atEnd s p = Bool.true) → StringBasicExtern char -- String.Pos.Raw.get'
  | lean_string_is_valid_pos : String → String.Pos.Raw → StringBasicExtern LeanPrimTy.bool -- String.Pos.Raw.isValid
  | lean_string_dec_lt : String → String → StringBasicExtern LeanPrimTy.bool -- String.decidableLT
  -- | lean_string_validate_utf8 : ByteArray → StringBasicExtern LeanPrimTy.bool -- ByteArray.validateUTF8 -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  | lean_string_utf8_extract__String_Pos_Raw_extract : String → String.Pos.Raw → String.Pos.Raw → StringBasicExtern string -- String.Pos.Raw.extract

-------------------------------
-- Init/Data/String/Length.lean
-------------------------------
/-- The pure externs of `Init/Data/String/Length.lean`. -/
inductive StringLengthExtern : MyTy → Type where
  | lean_string_length__String_length : String → StringLengthExtern nat -- String.length

------------------------------------------------
-- Init/Data/SInt/Basic.lean, the `Int8` entries
------------------------------------------------
/-- The pure externs of `Init/Data/SInt/Basic.lean`, on `Int8`. -/
inductive Int8BasicExtern : MyTy → Type where
  | lean_int8_add : Int8 → Int8 → Int8BasicExtern int8 -- Int8.add
  | lean_int8_div : Int8 → Int8 → Int8BasicExtern int8 -- Int8.div
  | lean_int8_to_int16 : Int8 → Int8BasicExtern int16 -- Int8.toInt16
  | lean_int8_shift_right : Int8 → Int8 → Int8BasicExtern int8 -- Int8.shiftRight
  | lean_int8_mod : Int8 → Int8 → Int8BasicExtern int8 -- Int8.mod
  | lean_bool_to_int8 : Bool → Int8BasicExtern int8 -- Bool.toInt8
  | lean_int8_shift_left : Int8 → Int8 → Int8BasicExtern int8 -- Int8.shiftLeft
  | lean_int8_xor : Int8 → Int8 → Int8BasicExtern int8 -- Int8.xor
  | lean_int8_complement : Int8 → Int8BasicExtern int8 -- Int8.complement
  | lean_int8_dec_eq : Int8 → Int8 → Int8BasicExtern LeanPrimTy.bool -- Int8.decEq
  | lean_int8_neg : Int8 → Int8BasicExtern int8 -- Int8.neg
  | lean_int8_dec_lt : Int8 → Int8 → Int8BasicExtern LeanPrimTy.bool -- Int8.decLt
  | lean_int8_abs : Int8 → Int8BasicExtern int8 -- Int8.abs
  | lean_int8_to_int32 : Int8 → Int8BasicExtern int32 -- Int8.toInt32
  | lean_int8_sub : Int8 → Int8 → Int8BasicExtern int8 -- Int8.sub
  | lean_int8_to_int64 : Int8 → Int8BasicExtern int64 -- Int8.toInt64
  | lean_int8_of_nat : Nat → Int8BasicExtern int8 -- Int8.ofNat
  | lean_int8_dec_le : Int8 → Int8 → Int8BasicExtern LeanPrimTy.bool -- Int8.decLe
  | lean_int8_to_int : Int8 → Int8BasicExtern int -- Int8.toInt
  | lean_int8_mul : Int8 → Int8 → Int8BasicExtern int8 -- Int8.mul
  | lean_int8_land : Int8 → Int8 → Int8BasicExtern int8 -- Int8.land
  | lean_int8_of_int : Int → Int8BasicExtern int8 -- Int8.ofInt
  | lean_int8_lor : Int8 → Int8 → Int8BasicExtern int8 -- Int8.lor

-------------------------------------------------
-- Init/Data/SInt/Basic.lean, the `Int16` entries
-------------------------------------------------
/-- The pure externs of `Init/Data/SInt/Basic.lean`, on `Int16`. -/
inductive Int16BasicExtern : MyTy → Type where
  | lean_int16_of_nat : Nat → Int16BasicExtern int16 -- Int16.ofNat
  | lean_int16_dec_le : Int16 → Int16 → Int16BasicExtern LeanPrimTy.bool -- Int16.decLe
  | lean_int16_shift_right : Int16 → Int16 → Int16BasicExtern int16 -- Int16.shiftRight
  | lean_int16_div : Int16 → Int16 → Int16BasicExtern int16 -- Int16.div
  | lean_int16_dec_lt : Int16 → Int16 → Int16BasicExtern LeanPrimTy.bool -- Int16.decLt
  | lean_int16_to_int : Int16 → Int16BasicExtern int -- Int16.toInt
  | lean_int16_mod : Int16 → Int16 → Int16BasicExtern int16 -- Int16.mod
  | lean_int16_dec_eq : Int16 → Int16 → Int16BasicExtern LeanPrimTy.bool -- Int16.decEq
  | lean_bool_to_int16 : Bool → Int16BasicExtern int16 -- Bool.toInt16
  | lean_int16_abs : Int16 → Int16BasicExtern int16 -- Int16.abs
  | lean_int16_to_int32 : Int16 → Int16BasicExtern int32 -- Int16.toInt32
  | lean_int16_complement : Int16 → Int16BasicExtern int16 -- Int16.complement
  | lean_int16_land : Int16 → Int16 → Int16BasicExtern int16 -- Int16.land
  | lean_int16_of_int : Int → Int16BasicExtern int16 -- Int16.ofInt
  | lean_int16_mul : Int16 → Int16 → Int16BasicExtern int16 -- Int16.mul
  | lean_int16_shift_left : Int16 → Int16 → Int16BasicExtern int16 -- Int16.shiftLeft
  | lean_int16_xor : Int16 → Int16 → Int16BasicExtern int16 -- Int16.xor
  | lean_int16_lor : Int16 → Int16 → Int16BasicExtern int16 -- Int16.lor
  | lean_int16_add : Int16 → Int16 → Int16BasicExtern int16 -- Int16.add
  | lean_int16_to_int8 : Int16 → Int16BasicExtern int8 -- Int16.toInt8
  | lean_int16_neg : Int16 → Int16BasicExtern int16 -- Int16.neg
  | lean_int16_sub : Int16 → Int16 → Int16BasicExtern int16 -- Int16.sub
  | lean_int16_to_int64 : Int16 → Int16BasicExtern int64 -- Int16.toInt64

-------------------------------------------------
-- Init/Data/SInt/Basic.lean, the `Int32` entries
-------------------------------------------------
/-- The pure externs of `Init/Data/SInt/Basic.lean`, on `Int32`. -/
inductive Int32BasicExtern : MyTy → Type where
  | lean_int32_of_int : Int → Int32BasicExtern int32 -- Int32.ofInt
  | lean_int32_land : Int32 → Int32 → Int32BasicExtern int32 -- Int32.land
  | lean_int32_mul : Int32 → Int32 → Int32BasicExtern int32 -- Int32.mul
  | lean_int32_dec_le : Int32 → Int32 → Int32BasicExtern LeanPrimTy.bool -- Int32.decLe
  | lean_int32_of_nat : Nat → Int32BasicExtern int32 -- Int32.ofNat
  | lean_int32_to_int64 : Int32 → Int32BasicExtern int64 -- Int32.toInt64
  | lean_int32_sub : Int32 → Int32 → Int32BasicExtern int32 -- Int32.sub
  | lean_int32_neg : Int32 → Int32BasicExtern int32 -- Int32.neg
  | lean_int32_abs : Int32 → Int32BasicExtern int32 -- Int32.abs
  | lean_int32_dec_eq : Int32 → Int32 → Int32BasicExtern LeanPrimTy.bool -- Int32.decEq
  | lean_int32_dec_lt : Int32 → Int32 → Int32BasicExtern LeanPrimTy.bool -- Int32.decLt
  | lean_int32_xor : Int32 → Int32 → Int32BasicExtern int32 -- Int32.xor
  | lean_int32_shift_left : Int32 → Int32 → Int32BasicExtern int32 -- Int32.shiftLeft
  | lean_int32_shift_right : Int32 → Int32 → Int32BasicExtern int32 -- Int32.shiftRight
  | lean_int32_complement : Int32 → Int32BasicExtern int32 -- Int32.complement
  | lean_bool_to_int32 : Bool → Int32BasicExtern int32 -- Bool.toInt32
  | lean_int32_to_int8 : Int32 → Int32BasicExtern int8 -- Int32.toInt8
  | lean_int32_add : Int32 → Int32 → Int32BasicExtern int32 -- Int32.add
  | lean_int32_lor : Int32 → Int32 → Int32BasicExtern int32 -- Int32.lor
  | lean_int32_mod : Int32 → Int32 → Int32BasicExtern int32 -- Int32.mod
  | lean_int32_to_int : Int32 → Int32BasicExtern int -- Int32.toInt
  | lean_int32_to_int16 : Int32 → Int32BasicExtern int16 -- Int32.toInt16
  | lean_int32_div : Int32 → Int32 → Int32BasicExtern int32 -- Int32.div

-------------------------------------------------
-- Init/Data/SInt/Basic.lean, the `Int64` entries
-------------------------------------------------
/-- The pure externs of `Init/Data/SInt/Basic.lean`, on `Int64`. -/
inductive Int64BasicExtern : MyTy → Type where
  -- | lean_isize_complement : denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.isize -- ISize.complement
  -- | lean_int64_to_isize : Int64 → Int64BasicExtern LeanPrimTy.isize -- Int64.toISize
  | lean_int64_sub : Int64 → Int64 → Int64BasicExtern int64 -- Int64.sub
  -- | lean_isize_to_int8 : denote LeanPrimTy.isize → Int64BasicExtern int8 -- ISize.toInt8
  | lean_int64_xor : Int64 → Int64 → Int64BasicExtern int64 -- Int64.xor
  -- | lean_isize_xor : denote LeanPrimTy.isize → denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.isize -- ISize.xor
  | lean_int64_to_int8 : Int64 → Int64BasicExtern int8 -- Int64.toInt8
  -- | lean_isize_shift_left : denote LeanPrimTy.isize → denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.isize -- ISize.shiftLeft
  | lean_int64_mul : Int64 → Int64 → Int64BasicExtern int64 -- Int64.mul
  | lean_int64_of_int : Int → Int64BasicExtern int64 -- Int64.ofInt
  -- | lean_int32_to_isize : Int32 → Int64BasicExtern LeanPrimTy.isize -- Int32.toISize
  | lean_int64_land : Int64 → Int64 → Int64BasicExtern int64 -- Int64.land
  | lean_int64_lor : Int64 → Int64 → Int64BasicExtern int64 -- Int64.lor
  -- | lean_isize_mod : denote LeanPrimTy.isize → denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.isize -- ISize.mod
  -- | lean_isize_shift_right : denote LeanPrimTy.isize → denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.isize -- ISize.shiftRight
  -- | lean_isize_to_int16 : denote LeanPrimTy.isize → Int64BasicExtern int16 -- ISize.toInt16
  -- | lean_isize_div : denote LeanPrimTy.isize → denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.isize -- ISize.div
  -- | lean_isize_add : denote LeanPrimTy.isize → denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.isize -- ISize.add
  -- | lean_isize_lor : denote LeanPrimTy.isize → denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.isize -- ISize.lor
  | lean_int64_mod : Int64 → Int64 → Int64BasicExtern int64 -- Int64.mod
  -- | lean_isize_of_int : Int → Int64BasicExtern LeanPrimTy.isize -- ISize.ofInt
  | lean_int64_shift_left : Int64 → Int64 → Int64BasicExtern int64 -- Int64.shiftLeft
  -- | lean_isize_land : denote LeanPrimTy.isize → denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.isize -- ISize.land
  -- | lean_isize_mul : denote LeanPrimTy.isize → denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.isize -- ISize.mul
  -- | lean_isize_to_int : denote LeanPrimTy.isize → Int64BasicExtern int -- ISize.toInt
  | lean_int64_dec_lt : Int64 → Int64 → Int64BasicExtern LeanPrimTy.bool -- Int64.decLt
  -- | lean_isize_dec_le : denote LeanPrimTy.isize → denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.bool -- ISize.decLe
  -- | lean_isize_of_nat : Nat → Int64BasicExtern LeanPrimTy.isize -- ISize.ofNat
  -- | lean_isize_to_int64 : denote LeanPrimTy.isize → Int64BasicExtern int64 -- ISize.toInt64
  -- | lean_isize_sub : denote LeanPrimTy.isize → denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.isize -- ISize.sub
  | lean_int64_complement : Int64 → Int64BasicExtern int64 -- Int64.complement
  -- | lean_isize_abs : denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.isize -- ISize.abs
  -- | lean_isize_to_int32 : denote LeanPrimTy.isize → Int64BasicExtern int32 -- ISize.toInt32
  | lean_int64_to_int32 : Int64 → Int64BasicExtern int32 -- Int64.toInt32
  | lean_int64_abs : Int64 → Int64BasicExtern int64 -- Int64.abs
  | lean_bool_to_int64 : Bool → Int64BasicExtern int64 -- Bool.toInt64
  -- | lean_bool_to_isize : Bool → Int64BasicExtern LeanPrimTy.isize -- Bool.toISize
  | lean_int64_dec_eq : Int64 → Int64 → Int64BasicExtern LeanPrimTy.bool -- Int64.decEq
  | lean_int64_dec_le : Int64 → Int64 → Int64BasicExtern LeanPrimTy.bool -- Int64.decLe
  | lean_int64_of_nat : Nat → Int64BasicExtern int64 -- Int64.ofNat
  | lean_int64_to_int_sint : Int64 → Int64BasicExtern int -- Int64.toInt
  -- | lean_isize_dec_lt : denote LeanPrimTy.isize → denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.bool -- ISize.decLt
  | lean_int64_neg : Int64 → Int64BasicExtern int64 -- Int64.neg
  -- | lean_isize_neg : denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.isize -- ISize.neg
  | lean_int64_add : Int64 → Int64 → Int64BasicExtern int64 -- Int64.add
  | lean_int64_div : Int64 → Int64 → Int64BasicExtern int64 -- Int64.div
  -- | lean_int8_to_isize : Int8 → Int64BasicExtern LeanPrimTy.isize -- Int8.toISize
  -- | lean_isize_dec_eq : denote LeanPrimTy.isize → denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.bool -- ISize.decEq
  | lean_int64_to_int16 : Int64 → Int64BasicExtern int16 -- Int64.toInt16
  -- | lean_int16_to_isize : Int16 → Int64BasicExtern LeanPrimTy.isize -- Int16.toISize
  | lean_int64_shift_right : Int64 → Int64 → Int64BasicExtern int64 -- Int64.shiftRight

--------------------------------------
-- Init/Data/String/Pattern/Basic.lean
--------------------------------------
/-- The pure externs of `Init/Data/String/Pattern/Basic.lean`. -/
inductive StringPatternExtern : MyTy → Type where
  | lean_string_memcmp : (lhs : String) → (rhs : String) → (lstart : String.Pos.Raw) → (rstart : String.Pos.Raw) → (len : String.Pos.Raw) → len.offsetBy lstart ≤ lhs.rawEndPos → len.offsetBy rstart ≤ rhs.rawEndPos → StringPatternExtern LeanPrimTy.bool -- String.Slice.Pattern.Internal.memcmpStr

------------------------------
-- Init/Data/String/Slice.lean
------------------------------
/-- The pure externs of `Init/Data/String/Slice.lean`. -/
inductive StringSliceExtern : MyTy → Type where
  | lean_slice_dec_lt : String.Slice → String.Slice → StringSliceExtern LeanPrimTy.bool -- String.Slice.instDecidableLt
  | lean_slice_hash : String.Slice → StringSliceExtern uint64 -- String.Slice.hash

-------------------------------
-- Init/Data/String/Modify.lean
-------------------------------
/-- The pure externs of `Init/Data/String/Modify.lean`. -/
inductive StringModifyExtern : MyTy → Type where
  | lean_string_utf8_set__String_Pos_Raw_set : String → String.Pos.Raw → Char → StringModifyExtern string -- String.Pos.Raw.set
  | lean_string_utf8_set__String_Pos_set : {s : String} → (p : s.Pos) → Char → p ≠ s.endPos → StringModifyExtern string -- String.Pos.set
  | lean_string_utf8_set__String_set : String → String.Pos.Raw → Char → StringModifyExtern string -- String.set

-----------------------------
-- Init/Data/Float/Float.lean
-----------------------------
/-- The pure externs of `Init/Data/Float/Float.lean`. -/
inductive FloatExtern : MyTy → Type where
  | lean_float_frexp : Float → FloatExtern (prod float int) -- Float.frExp
  | lean_uint8_to_float : UInt8 → FloatExtern float -- UInt8.toFloat
  | lean_float_to_bits__Float_toModel : Float → FloatExtern floatModel -- Float.toModel
  | lean_float_to_bits__Float_toBits : Float → FloatExtern uint64 -- Float.toBits
  | lean_float_of_bits__Float_ofBits : UInt64 → FloatExtern float -- Float.ofBits
  | lean_float_of_bits__Float_ofModel : Float.Model → FloatExtern float -- Float.ofModel
  | lean_float_isnan : Float → FloatExtern LeanPrimTy.bool -- Float.isNaN
  | log10 : Float → FloatExtern float -- Float.log10
  | cbrt : Float → FloatExtern float -- Float.cbrt
  | log : Float → FloatExtern float -- Float.log
  | lean_float_div : Float → Float → FloatExtern float -- Float.div
  | lean_float_beq : Float → Float → FloatExtern LeanPrimTy.bool -- Float.beq
  | tan : Float → FloatExtern float -- Float.tan
  | tanh : Float → FloatExtern float -- Float.tanh
  | exp2 : Float → FloatExtern float -- Float.exp2
  | lean_float_to_uint16 : Float → FloatExtern uint16 -- Float.toUInt16
  | lean_uint32_to_float : UInt32 → FloatExtern float -- UInt32.toFloat
  | lean_float_decLe__Float_decLe : Float → Float → FloatExtern LeanPrimTy.bool -- Float.decLe
  | lean_float_decLe__Float_le : Float → Float → FloatExtern LeanPrimTy.bool -- Float.le
  | lean_float_to_uint64 : Float → FloatExtern uint64 -- Float.toUInt64
  | sqrt : Float → FloatExtern float -- Float.sqrt
  | acos : Float → FloatExtern float -- Float.acos
  | atan : Float → FloatExtern float -- Float.atan
  | acosh : Float → FloatExtern float -- Float.acosh
  | floor : Float → FloatExtern float -- Float.floor
  | fabs : Float → FloatExtern float -- Float.abs
  | lean_float_to_uint32 : Float → FloatExtern uint32 -- Float.toUInt32
  | lean_float_to_string : Float → FloatExtern string -- Float.toString
  | lean_uint64_to_float : UInt64 → FloatExtern float -- UInt64.toFloat
  | lean_float_decLt__Float_decLt : Float → Float → FloatExtern LeanPrimTy.bool -- Float.decLt
  | lean_float_decLt__Float_lt : Float → Float → FloatExtern LeanPrimTy.bool -- Float.lt
  | lean_float_to_uint8 : Float → FloatExtern uint8 -- Float.toUInt8
  | sin : Float → FloatExtern float -- Float.sin
  -- | lean_usize_to_float : denote LeanPrimTy.usize → FloatExtern float -- USize.toFloat
  | cosh : Float → FloatExtern float -- Float.cosh
  | exp : Float → FloatExtern float -- Float.exp
  | ceil : Float → FloatExtern float -- Float.ceil
  -- | lean_float_to_usize : Float → FloatExtern LeanPrimTy.usize -- Float.toUSize
  | lean_float_isfinite : Float → FloatExtern LeanPrimTy.bool -- Float.isFinite
  | round : Float → FloatExtern float -- Float.round
  | cos : Float → FloatExtern float -- Float.cos
  | log2 : Float → FloatExtern float -- Float.log2
  | atanh : Float → FloatExtern float -- Float.atanh
  | atan2 : Float → Float → FloatExtern float -- Float.atan2
  | sinh : Float → FloatExtern float -- Float.sinh
  | asinh : Float → FloatExtern float -- Float.asinh
  | lean_float_mul : Float → Float → FloatExtern float -- Float.mul
  | lean_uint16_to_float : UInt16 → FloatExtern float -- UInt16.toFloat
  | asin : Float → FloatExtern float -- Float.asin
  | pow : Float → Float → FloatExtern float -- Float.pow
  | lean_float_scaleb : Float → Int → FloatExtern float -- Float.scaleB
  | lean_float_add : Float → Float → FloatExtern float -- Float.add
  | lean_float_sub : Float → Float → FloatExtern float -- Float.sub
  | lean_float_negate : Float → FloatExtern float -- Float.neg
  | lean_float_isinf : Float → FloatExtern LeanPrimTy.bool -- Float.isInf

----------------------------------
-- Init/Data/FloatArray/Basic.lean: every entry is commented out, so it has no family
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
/-- The pure externs of `Init/Data/UInt/Log2.lean`. -/
inductive UIntLog2Extern : MyTy → Type where
  -- | lean_usize_log2 : denote LeanPrimTy.usize → UIntLog2Extern LeanPrimTy.usize -- USize.log2
  | lean_uint16_log2 : UInt16 → UIntLog2Extern uint16 -- UInt16.log2
  | lean_uint64_log2 : UInt64 → UIntLog2Extern uint64 -- UInt64.log2
  | lean_uint8_log2 : UInt8 → UIntLog2Extern uint8 -- UInt8.log2
  | lean_uint32_log2 : UInt32 → UIntLog2Extern uint32 -- UInt32.log2

----------------------------
-- Init/Data/SInt/Float.lean
----------------------------
/-- The pure externs of `Init/Data/SInt/Float.lean`. -/
inductive SIntFloatExtern : MyTy → Type where
  | lean_int32_to_float : Int32 → SIntFloatExtern float -- Int32.toFloat
  | lean_float_to_int16 : Float → SIntFloatExtern int16 -- Float.toInt16
  | lean_int16_to_float : Int16 → SIntFloatExtern float -- Int16.toFloat
  | lean_float_to_int32 : Float → SIntFloatExtern int32 -- Float.toInt32
  -- | lean_isize_to_float : denote LeanPrimTy.isize → SIntFloatExtern float -- ISize.toFloat
  | lean_int8_to_float : Int8 → SIntFloatExtern float -- Int8.toFloat
  | lean_float_to_int8 : Float → SIntFloatExtern int8 -- Float.toInt8
  | lean_int64_to_float : Int64 → SIntFloatExtern float -- Int64.toFloat
  | lean_float_to_int64 : Float → SIntFloatExtern int64 -- Float.toInt64
  -- | lean_float_to_isize : Float → SIntFloatExtern LeanPrimTy.isize -- Float.toISize

-------------------------------
-- Init/Data/Float/Float32.lean
-------------------------------
/-- The pure externs of `Init/Data/Float/Float32.lean`. -/
inductive Float32Extern : MyTy → Type where
  | tanhf : Float32 → Float32Extern float32 -- Float32.tanh
  | exp2f : Float32 → Float32Extern float32 -- Float32.exp2
  | lean_float32_div : Float32 → Float32 → Float32Extern float32 -- Float32.div
  | logf : Float32 → Float32Extern float32 -- Float32.log
  | lean_float32_decLe__Float32_le : Float32 → Float32 → Float32Extern LeanPrimTy.bool -- Float32.le
  | lean_float32_decLe__Float32_decLe : Float32 → Float32 → Float32Extern LeanPrimTy.bool -- Float32.decLe
  | lean_float_to_float32 : Float → Float32Extern float32 -- Float.toFloat32
  | lean_float32_to_bits__Float32_toModel : Float32 → Float32Extern float32Model -- Float32.toModel
  | lean_float32_to_bits__Float32_toBits : Float32 → Float32Extern uint32 -- Float32.toBits
  | lean_float32_of_bits__Float32_ofBits : UInt32 → Float32Extern float32 -- Float32.ofBits
  | lean_float32_of_bits__Float32_ofModel : Float32.Model → Float32Extern float32 -- Float32.ofModel
  | atanf : Float32 → Float32Extern float32 -- Float32.atan
  | acoshf : Float32 → Float32Extern float32 -- Float32.acosh
  | lean_float32_frexp : Float32 → Float32Extern (prod float32 int) -- Float32.frExp
  | lean_float32_to_uint64 : Float32 → Float32Extern uint64 -- Float32.toUInt64
  | lean_float32_sub : Float32 → Float32 → Float32Extern float32 -- Float32.sub
  | lean_float32_to_uint16 : Float32 → Float32Extern uint16 -- Float32.toUInt16
  -- | lean_usize_to_float32 : denote LeanPrimTy.usize → Float32Extern float32 -- USize.toFloat32
  | asinf : Float32 → Float32Extern float32 -- Float32.asin
  | powf : Float32 → Float32 → Float32Extern float32 -- Float32.pow
  | lean_float32_beq : Float32 → Float32 → Float32Extern LeanPrimTy.bool -- Float32.beq
  | lean_uint8_to_float32 : UInt8 → Float32Extern float32 -- UInt8.toFloat32
  | tanf : Float32 → Float32Extern float32 -- Float32.tan
  | lean_float32_to_float : Float32 → Float32Extern float -- Float32.toFloat
  | lean_float32_isnan : Float32 → Float32Extern LeanPrimTy.bool -- Float32.isNaN
  | log10f : Float32 → Float32Extern float32 -- Float32.log10
  | cbrtf : Float32 → Float32Extern float32 -- Float32.cbrt
  | atan2f : Float32 → Float32 → Float32Extern float32 -- Float32.atan2
  | sinhf : Float32 → Float32Extern float32 -- Float32.sinh
  | cosf : Float32 → Float32Extern float32 -- Float32.cos
  | lean_uint32_to_float32 : UInt32 → Float32Extern float32 -- UInt32.toFloat32
  | lean_float32_isinf : Float32 → Float32Extern LeanPrimTy.bool -- Float32.isInf
  | lean_float32_negate : Float32 → Float32Extern float32 -- Float32.neg
  -- | lean_float32_to_usize : Float32 → Float32Extern LeanPrimTy.usize -- Float32.toUSize
  | ceilf : Float32 → Float32Extern float32 -- Float32.ceil
  | lean_float32_isfinite : Float32 → Float32Extern LeanPrimTy.bool -- Float32.isFinite
  | lean_float32_add : Float32 → Float32 → Float32Extern float32 -- Float32.add
  | lean_float32_scaleb : Float32 → Int → Float32Extern float32 -- Float32.scaleB
  | sinf : Float32 → Float32Extern float32 -- Float32.sin
  | lean_float32_mul : Float32 → Float32 → Float32Extern float32 -- Float32.mul
  | lean_float32_to_string : Float32 → Float32Extern string -- Float32.toString
  | asinhf : Float32 → Float32Extern float32 -- Float32.asinh
  | lean_float32_to_uint32 : Float32 → Float32Extern uint32 -- Float32.toUInt32
  | log2f : Float32 → Float32Extern float32 -- Float32.log2
  | lean_uint64_to_float32 : UInt64 → Float32Extern float32 -- UInt64.toFloat32
  | atanhf : Float32 → Float32Extern float32 -- Float32.atanh
  | floorf : Float32 → Float32Extern float32 -- Float32.floor
  | fabsf : Float32 → Float32Extern float32 -- Float32.abs
  | roundf : Float32 → Float32Extern float32 -- Float32.round
  | lean_float32_decLt__Float32_lt : Float32 → Float32 → Float32Extern LeanPrimTy.bool -- Float32.lt
  | lean_float32_decLt__Float32_decLt : Float32 → Float32 → Float32Extern LeanPrimTy.bool -- Float32.decLt
  | acosf : Float32 → Float32Extern float32 -- Float32.acos
  | sqrtf : Float32 → Float32Extern float32 -- Float32.sqrt
  | lean_uint16_to_float32 : UInt16 → Float32Extern float32 -- UInt16.toFloat32
  | coshf : Float32 → Float32Extern float32 -- Float32.cosh
  | expf : Float32 → Float32Extern float32 -- Float32.exp
  | lean_float32_to_uint8 : Float32 → Float32Extern uint8 -- Float32.toUInt8

------------------------------
-- Init/Data/SInt/Float32.lean
------------------------------
/-- The pure externs of `Init/Data/SInt/Float32.lean`. -/
inductive SIntFloat32Extern : MyTy → Type where
  | lean_float32_to_int64 : Float32 → SIntFloat32Extern int64 -- Float32.toInt64
  -- | lean_float32_to_isize : Float32 → SIntFloat32Extern LeanPrimTy.isize -- Float32.toISize
  | lean_int32_to_float32 : Int32 → SIntFloat32Extern float32 -- Int32.toFloat32
  | lean_float32_to_int8 : Float32 → SIntFloat32Extern int8 -- Float32.toInt8
  | lean_float32_to_int16 : Float32 → SIntFloat32Extern int16 -- Float32.toInt16
  -- | lean_isize_to_float32 : denote LeanPrimTy.isize → SIntFloat32Extern float32 -- ISize.toFloat32
  | lean_int8_to_float32 : Int8 → SIntFloat32Extern float32 -- Int8.toFloat32
  | lean_float32_to_int32 : Float32 → SIntFloat32Extern int32 -- Float32.toInt32
  | lean_int16_to_float32 : Int16 → SIntFloat32Extern float32 -- Int16.toFloat32
  | lean_int64_to_float32 : Int64 → SIntFloat32Extern float32 -- Int64.toFloat32

----------------------------
-- Init/Data/Ord/String.lean
----------------------------
/-- The pure externs of `Init/Data/Ord/String.lean`. -/
inductive OrdStringExtern : MyTy → Type where
  | lean_string_compare : String → String → OrdStringExtern ordering -- String.compare

----------------------
-- Init/System/IO.lean: every entry is commented out, so it has no family
----------------------
-- | lean_io_process_child_pid : {cfg : IO.Process.StdioConfig} → denote (io_process_child cfg) → LeanInitPureExtern uint32 -- IO.Process.Child.pid

---------------------------
-- Init/System/Promise.lean: every entry is commented out, so it has no family
---------------------------
-- | lean_io_promise_result_opt : (αt : MyTy) → denote (io_promise αt) → LeanInitPureExtern (task (option αt)) -- IO.Promise.result?
-- | lean_option_get_or_block : (αt : MyTy) → Option (denote αt) → LeanInitPureExtern αt -- _private.Init.System.Promise.0.IO.Option.getOrBlock!

------------------------
-- Init/ShareCommon.lean: every entry is commented out, so it has no family
------------------------
-- | lean_sharecommon_quick : (αt : MyTy) → denote αt → LeanInitPureExtern αt -- ShareCommon.shareCommon'
-- | lean_state_sharecommon : (αt : MyTy) → {σ : shareCommon_stateFactory} → denote (shareCommon_state σ) → denote αt → LeanInitPureExtern (prod αt (shareCommon_state σ)) -- ShareCommon.State.shareCommon
-- | lean_sharecommon_eq : denote shareCommon_object → denote shareCommon_object → LeanInitPureExtern LeanPrimTy.bool -- ShareCommon.Object.eq
-- | lean_sharecommon_hash : denote shareCommon_object → LeanInitPureExtern uint64 -- ShareCommon.Object.hash

/-- A pure extern of `Init`, applied to all of its arguments (and to the proofs it takes):
    an entry of one of the families above.

    **No `DecidableEq`/`BEq`.**  `Float`, `Float32` and their models have `DecidableEq`
    (structural equality of the bits), so the `Float` fields are not what prevents it.
    What does:
    * some entries hold **functions** — `lean_string_foldl` holds a
      `String → Char → String`, and `lean_string_any`, `lean_string_nextwhile`,
      `lean_substring_all` and `lean_substring_takewhile` a `Char → Bool` — and equality
      of functions like `String → Char → String` cannot be decided;
    * other fields are values `denote αt` of an arbitrary type of the language, which can
      itself be a function type;
    * and the index of an entry is computed through the abstract coercions and type
      formers above, so `deriving DecidableEq` cannot unify the indices of two entries. -/
inductive LeanInitPureExtern : MyTy → Type where
  /-- An entry of `PreludeExtern` (`Init/Prelude.lean`). -/
  | preludeExtern {τ : MyTy} : PreludeExtern denote list leanName τ → LeanInitPureExtern τ
  /-- An entry of `CoreExtern` (`Init/Core.lean`). -/
  | coreExtern {τ : MyTy} : CoreExtern denote τ → LeanInitPureExtern τ
  /-- An entry of `IntBasicExtern` (`Init/Data/Int/Basic.lean`). -/
  | intBasicExtern {τ : MyTy} : IntBasicExtern τ → LeanInitPureExtern τ
  /-- An entry of `NatDivExtern` (`Init/Data/Nat/Div/Basic.lean`). -/
  | natDivExtern {τ : MyTy} : NatDivExtern τ → LeanInitPureExtern τ
  /-- An entry of `NatBitwiseExtern` (`Init/Data/Nat/Bitwise/Basic.lean`). -/
  | natBitwiseExtern {τ : MyTy} : NatBitwiseExtern τ → LeanInitPureExtern τ
  /-- An entry of `UIntBasicAuxExtern` (`Init/Data/UInt/BasicAux.lean`). -/
  | uintBasicAuxExtern {τ : MyTy} : UIntBasicAuxExtern τ → LeanInitPureExtern τ
  /-- An entry of `StringBootstrapExtern` (`Init/Data/String/Bootstrap.lean`). -/
  | stringBootstrapExtern {τ : MyTy} : StringBootstrapExtern τ → LeanInitPureExtern τ
  /-- An entry of `UtilExtern` (`Init/Util.lean`). -/
  | utilExtern {τ : MyTy} : UtilExtern denote τ → LeanInitPureExtern τ
  /-- An entry of `ArraySetExtern` (`Init/Data/Array/Set.lean`). -/
  | arraySetExtern {τ : MyTy} : ArraySetExtern denote τ → LeanInitPureExtern τ
  /-- An entry of `ArrayBasicExtern` (`Init/Data/Array/Basic.lean`). -/
  | arrayBasicExtern {τ : MyTy} : ArrayBasicExtern denote τ → LeanInitPureExtern τ
  /-- An entry of `MetaDefsExtern` (`Init/Meta/Defs.lean`). -/
  | metaDefsExtern {τ : MyTy} : MetaDefsExtern τ → LeanInitPureExtern τ
  /-- An entry of `NatLog2Extern` (`Init/Data/Nat/Log2.lean`). -/
  | natLog2Extern {τ : MyTy} : NatLog2Extern τ → LeanInitPureExtern τ
  /-- An entry of `IntDivModExtern` (`Init/Data/Int/DivMod/Basic.lean`). -/
  | intDivModExtern {τ : MyTy} : IntDivModExtern τ → LeanInitPureExtern τ
  /-- An entry of `UInt8BasicExtern` (`Init/Data/UInt/Basic.lean`, the `UInt8` entries). -/
  | uint8BasicExtern {τ : MyTy} : UInt8BasicExtern τ → LeanInitPureExtern τ
  /-- An entry of `UInt16BasicExtern` (`Init/Data/UInt/Basic.lean`, the `UInt16` entries). -/
  | uint16BasicExtern {τ : MyTy} : UInt16BasicExtern τ → LeanInitPureExtern τ
  /-- An entry of `UInt32BasicExtern` (`Init/Data/UInt/Basic.lean`, the `UInt32` entries). -/
  | uint32BasicExtern {τ : MyTy} : UInt32BasicExtern τ → LeanInitPureExtern τ
  /-- An entry of `UInt64BasicExtern` (`Init/Data/UInt/Basic.lean`, the `UInt64` entries). -/
  | uint64BasicExtern {τ : MyTy} : UInt64BasicExtern τ → LeanInitPureExtern τ
  /-- An entry of `StringPosRawExtern` (`Init/Data/String/PosRaw.lean`). -/
  | stringPosRawExtern {τ : MyTy} : StringPosRawExtern τ → LeanInitPureExtern τ
  /-- An entry of `StringDefsExtern` (`Init/Data/String/Defs.lean`). -/
  | stringDefsExtern {τ : MyTy} : StringDefsExtern τ → LeanInitPureExtern τ
  /-- An entry of `PlatformExtern` (`Init/System/Platform.lean`). -/
  | platformExtern {τ : MyTy} : PlatformExtern τ → LeanInitPureExtern τ
  /-- An entry of `StringBasicExtern` (`Init/Data/String/Basic.lean`). -/
  | stringBasicExtern {τ : MyTy} : StringBasicExtern option list τ → LeanInitPureExtern τ
  /-- An entry of `StringLengthExtern` (`Init/Data/String/Length.lean`). -/
  | stringLengthExtern {τ : MyTy} : StringLengthExtern τ → LeanInitPureExtern τ
  /-- An entry of `Int8BasicExtern` (`Init/Data/SInt/Basic.lean`, the `Int8` entries). -/
  | int8BasicExtern {τ : MyTy} : Int8BasicExtern τ → LeanInitPureExtern τ
  /-- An entry of `Int16BasicExtern` (`Init/Data/SInt/Basic.lean`, the `Int16` entries). -/
  | int16BasicExtern {τ : MyTy} : Int16BasicExtern τ → LeanInitPureExtern τ
  /-- An entry of `Int32BasicExtern` (`Init/Data/SInt/Basic.lean`, the `Int32` entries). -/
  | int32BasicExtern {τ : MyTy} : Int32BasicExtern τ → LeanInitPureExtern τ
  /-- An entry of `Int64BasicExtern` (`Init/Data/SInt/Basic.lean`, the `Int64` entries). -/
  | int64BasicExtern {τ : MyTy} : Int64BasicExtern τ → LeanInitPureExtern τ
  /-- An entry of `StringPatternExtern` (`Init/Data/String/Pattern/Basic.lean`). -/
  | stringPatternExtern {τ : MyTy} : StringPatternExtern τ → LeanInitPureExtern τ
  /-- An entry of `StringSliceExtern` (`Init/Data/String/Slice.lean`). -/
  | stringSliceExtern {τ : MyTy} : StringSliceExtern τ → LeanInitPureExtern τ
  /-- An entry of `StringModifyExtern` (`Init/Data/String/Modify.lean`). -/
  | stringModifyExtern {τ : MyTy} : StringModifyExtern τ → LeanInitPureExtern τ
  /-- An entry of `FloatExtern` (`Init/Data/Float/Float.lean`). -/
  | floatExtern {τ : MyTy} : FloatExtern prod τ → LeanInitPureExtern τ
  /-- An entry of `UIntLog2Extern` (`Init/Data/UInt/Log2.lean`). -/
  | uintLog2Extern {τ : MyTy} : UIntLog2Extern τ → LeanInitPureExtern τ
  /-- An entry of `SIntFloatExtern` (`Init/Data/SInt/Float.lean`). -/
  | sIntFloatExtern {τ : MyTy} : SIntFloatExtern τ → LeanInitPureExtern τ
  /-- An entry of `Float32Extern` (`Init/Data/Float/Float32.lean`). -/
  | float32Extern {τ : MyTy} : Float32Extern prod τ → LeanInitPureExtern τ
  /-- An entry of `SIntFloat32Extern` (`Init/Data/SInt/Float32.lean`). -/
  | sIntFloat32Extern {τ : MyTy} : SIntFloat32Extern τ → LeanInitPureExtern τ
  /-- An entry of `OrdStringExtern` (`Init/Data/Ord/String.lean`). -/
  | ordStringExtern {τ : MyTy} : OrdStringExtern ordering τ → LeanInitPureExtern τ

end LeanScript

end
