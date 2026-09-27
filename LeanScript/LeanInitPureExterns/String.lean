module
prelude
public import LeanScript.Ty.LeanPrimTy
public import LeanScript.Ty.LeanPrimTyCovariant
set_option autoImplicit false
@[expose] public section
namespace LeanScript

/-!
# The catalogue of pure externs: strings (`String`, `String.Pos`, `Substring`, slices, patterns, `Ord String`)

One part of the catalogue `LeanScript.LeanInitPureExtern` (see
`LeanScript.LeanInitPureExterns` for how it is organised).  Every family is written against
the same parameters as `LeanInitPureExtern`; only the ones its entries use become its own.
-/

open LeanPrimTy
open LeanPrimTyCovariant

variable {MyTy : Type}
  [Coe LeanPrimTy MyTy]
  [Coe (LeanPrimTyCovariant LeanPrimTy) MyTy]
  [Coe (LeanPrimTyCovariant MyTy) MyTy]
  (option : MyTy → MyTy)
  (fn1 : MyTy → MyTy → MyTy)
  (fn2 : MyTy → MyTy → MyTy → MyTy)
  (prod : MyTy → MyTy → MyTy)
  (ordering : MyTy)
  (leanName : MyTy)

----------------------------------
-- Init/Data/String/Bootstrap.lean
----------------------------------
/-- The pure externs of `Init/Data/String/Bootstrap.lean`. -/
inductive StringBootstrapExtern : List MyTy → MyTy → Type where
  | lean_string_utf8_get__String_Internal_get : StringBootstrapExtern [string, stringPosRaw] char -- String.Internal.get
  | lean_string_trim : StringBootstrapExtern [string] string -- String.Internal.trim
  | lean_substring_drop : StringBootstrapExtern [substringRaw, nat] substringRaw -- Substring.Raw.Internal.drop
  | lean_substring_prev : StringBootstrapExtern [substringRaw, stringPosRaw] stringPosRaw -- Substring.Raw.Internal.prev
  | lean_substring_extract : StringBootstrapExtern [substringRaw, stringPosRaw, stringPosRaw] substringRaw -- Substring.Raw.Internal.extract
  | lean_string_foldl : StringBootstrapExtern [(fn2 string char string), string, string] string -- String.Internal.foldl
  | lean_substring_tostring : StringBootstrapExtern [substringRaw] string -- Substring.Raw.Internal.toString
  | lean_string_append__String_Internal_append : StringBootstrapExtern [string, string] string -- String.Internal.append
  | lean_string_get_byte_fast__String_Internal_getUTF8Byte : StringBootstrapExtern [string, nat] uint8 -- String.Internal.getUTF8Byte (decides `n < s.utf8ByteSize`)
  | lean_string_isempty : StringBootstrapExtern [string] LeanPrimTy.bool -- String.Internal.isEmpty
  | lean_string_push : StringBootstrapExtern [string, char] string -- String.push
  | lean_string_isprefixof : StringBootstrapExtern [string, string] LeanPrimTy.bool -- String.Internal.isPrefixOf
  | lean_string_dropright : StringBootstrapExtern [string, nat] string -- String.Internal.dropRight
  | lean_substring_takewhile : StringBootstrapExtern [substringRaw, (fn1 char LeanPrimTy.bool)] substringRaw -- Substring.Raw.Internal.takeWhile
  | lean_substring_get : StringBootstrapExtern [substringRaw, stringPosRaw] char -- Substring.Raw.Internal.get
  -- `USize` is `Nat` here, so this is `lean_string_get_byte_fast__String_Internal_getUTF8Byte`; a call of `String.Internal.ugetUTF8Byte` is that entry
  -- | lean_string_uget_byte_fast : (s : String) → (n : Nat) → (h : n < s.utf8ByteSize) → StringBootstrapExtern uint8 -- String.Internal.ugetUTF8Byte
  | lean_string_contains : StringBootstrapExtern [string, char] LeanPrimTy.bool -- String.Internal.contains
  | lean_string_front : StringBootstrapExtern [string] char -- String.Internal.front
  | lean_string_posof : StringBootstrapExtern [string, char] stringPosRaw -- String.Internal.posOf
  | lean_substring_all : StringBootstrapExtern [substringRaw, (fn1 char LeanPrimTy.bool)] LeanPrimTy.bool -- Substring.Raw.Internal.all
  | lean_string_intercalate : StringBootstrapExtern [string, (list string)] string -- String.Internal.intercalate
  | lean_string_drop : StringBootstrapExtern [string, nat] string -- String.Internal.drop
  | lean_string_length__String_Internal_length : StringBootstrapExtern [string] nat -- String.Internal.length
  | lean_string_utf8_at_end__String_Internal_atEnd : StringBootstrapExtern [string, stringPosRaw] LeanPrimTy.bool -- String.Internal.atEnd
  | lean_substring_beq : StringBootstrapExtern [substringRaw, substringRaw] LeanPrimTy.bool -- Substring.Raw.Internal.beq
  | lean_string_nextwhile : StringBootstrapExtern [string, (fn1 char LeanPrimTy.bool), stringPosRaw] stringPosRaw -- String.Internal.nextWhile
  | lean_string_utf8_next__String_Internal_next : StringBootstrapExtern [string, stringPosRaw] stringPosRaw -- String.Internal.next
  | lean_string_mk__String_mk : StringBootstrapExtern [(list char)] string -- String.mk
  | lean_string_any : StringBootstrapExtern [string, (fn1 char LeanPrimTy.bool)] LeanPrimTy.bool -- String.Internal.any
  | lean_string_pushn : StringBootstrapExtern [string, char, nat] string -- String.Internal.pushn
  | lean_string_capitalize : StringBootstrapExtern [string] string -- String.Internal.capitalize
  | lean_string_utf8_extract__String_Internal_extract : StringBootstrapExtern [string, stringPosRaw, stringPosRaw] string -- String.Internal.extract
  | lean_string_pos_min : StringBootstrapExtern [stringPosRaw, stringPosRaw] stringPosRaw -- String.Pos.Raw.Internal.min
  | lean_substring_front : StringBootstrapExtern [substringRaw] char -- Substring.Raw.Internal.front
  | lean_string_pos_sub : StringBootstrapExtern [stringPosRaw, stringPosRaw] stringPosRaw -- String.Pos.Raw.Internal.sub
  | lean_substring_isempty : StringBootstrapExtern [substringRaw] LeanPrimTy.bool -- Substring.Raw.Internal.isEmpty
  | lean_string_offsetofpos : StringBootstrapExtern [string, stringPosRaw] nat -- String.Internal.offsetOfPos

-------------------------------
-- Init/Data/String/PosRaw.lean
-------------------------------
/-- The pure externs of `Init/Data/String/PosRaw.lean`. -/
inductive StringPosRawExtern : List MyTy → MyTy → Type where
  | lean_string_get_byte_fast__String_getUtf8Byte : StringPosRawExtern [string, stringPosRaw] uint8 -- String.getUtf8Byte (decides `p < s.rawEndPos`)
  | lean_string_get_byte_fast__String_getUTF8Byte : StringPosRawExtern [string, stringPosRaw] uint8 -- String.getUTF8Byte (decides `p < s.rawEndPos`)

-----------------------------
-- Init/Data/String/Defs.lean
-----------------------------
/-- The pure externs of `Init/Data/String/Defs.lean`. -/
inductive StringDefsExtern : List MyTy → MyTy → Type where
  -- | lean_string_to_utf8__String_toUTF8 : String → StringDefsExtern byteArray -- String.toUTF8 -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  | lean_string_append__String_append : StringDefsExtern [string, string] string -- String.append

------------------------------
-- Init/Data/String/Basic.lean
------------------------------
/-- The pure externs of `Init/Data/String/Basic.lean`. -/
inductive StringBasicExtern : List MyTy → MyTy → Type where
  | lean_string_utf8_next__String_next : StringBasicExtern [string, stringPosRaw] stringPosRaw -- String.next
  | lean_string_utf8_next__String_Pos_Raw_next : StringBasicExtern [string, stringPosRaw] stringPosRaw -- String.Pos.Raw.next
  | lean_string_utf8_get__String_Pos_Raw_get : StringBasicExtern [string, stringPosRaw] char -- String.Pos.Raw.get
  | lean_string_utf8_get__String_get : StringBasicExtern [string, stringPosRaw] char -- String.get
  | lean_string_utf8_get_opt__String_Pos_Raw_get? : StringBasicExtern [string, stringPosRaw] (option char) -- String.Pos.Raw.get?
  | lean_string_utf8_get_opt__String_get? : StringBasicExtern [string, stringPosRaw] (option char) -- String.get?
  | lean_string_utf8_prev__String_Pos_Raw_prev : StringBasicExtern [string, stringPosRaw] stringPosRaw -- String.Pos.Raw.prev
  | lean_string_utf8_prev__String_prev : StringBasicExtern [string, stringPosRaw] stringPosRaw -- String.prev
  | lean_string_utf8_next_fast__String_next' : StringBasicExtern [string, stringPosRaw] stringPosRaw -- String.next' (decides `¬String.Pos.Raw.atEnd s p = Bool.true`)
  -- the same function as `lean_string_utf8_next_fast__String_next'`; a call of `String.Pos.Raw.next'` is that entry
  -- | lean_string_utf8_next_fast__String_Pos_Raw_next' : (s : String) → (p : String.Pos.Raw) → (h : ¬String.Pos.Raw.atEnd s p = Bool.true) → StringBasicExtern stringPosRaw -- String.Pos.Raw.next'
  | lean_string_utf8_next_fast__String_Pos_next : (s : String) → (h_len : 2 ≤ s.length) → StringBasicExtern [(LeanPrimTy.stringPos s h_len)] (LeanPrimTy.stringPos s h_len) -- String.Pos.next (decides `pos ≠ s.endPos`)
  | lean_string_data__String_data : StringBasicExtern [string] (list char) -- String.data
  | lean_string_data__String_toList : StringBasicExtern [string] (list char) -- String.toList
  | lean_string_utf8_extract_fast : (s : String) → (h_len : 2 ≤ s.length) → StringBasicExtern [(LeanPrimTy.stringPos s h_len), (LeanPrimTy.stringPos s h_len)] string -- String.extract
  | lean_string_utf8_at_end__String_atEnd : StringBasicExtern [string, stringPosRaw] LeanPrimTy.bool -- String.atEnd
  | lean_string_utf8_at_end__String_Pos_Raw_atEnd : StringBasicExtern [string, stringPosRaw] LeanPrimTy.bool -- String.Pos.Raw.atEnd
  | lean_string_utf8_get_bang__String_Pos_Raw_get! : StringBasicExtern [string, stringPosRaw] char -- String.Pos.Raw.get!
  | lean_string_utf8_get_bang__String_get! : StringBasicExtern [string, stringPosRaw] char -- String.get!
  -- | lean_string_utf8_get_fast__String_decodeChar : (s : String) → (byteIdx : Nat) → (h : (s.toByteArray.utf8DecodeChar? byteIdx).isSome = Bool.true) → StringBasicExtern char -- String.decodeChar -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  | lean_string_utf8_get_fast__String_get' : StringBasicExtern [string, stringPosRaw] char -- String.get' (decides `¬String.Pos.Raw.atEnd s p = Bool.true`)
  | lean_string_utf8_get_fast__String_Pos_Raw_get' : StringBasicExtern [string, stringPosRaw] char -- String.Pos.Raw.get' (decides `¬String.Pos.Raw.atEnd s p = Bool.true`)
  | lean_string_is_valid_pos : StringBasicExtern [string, stringPosRaw] LeanPrimTy.bool -- String.Pos.Raw.isValid
  | lean_string_dec_lt : StringBasicExtern [string, string] LeanPrimTy.bool -- String.decidableLT
  -- | lean_string_validate_utf8 : ByteArray → StringBasicExtern LeanPrimTy.bool -- ByteArray.validateUTF8 -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
  | lean_string_utf8_extract__String_Pos_Raw_extract : StringBasicExtern [string, stringPosRaw, stringPosRaw] string -- String.Pos.Raw.extract

-------------------------------
-- Init/Data/String/Length.lean
-------------------------------
/-- The pure externs of `Init/Data/String/Length.lean`. -/
inductive StringLengthExtern : List MyTy → MyTy → Type where
  | lean_string_length__String_length : StringLengthExtern [string] nat -- String.length

--------------------------------------
-- Init/Data/String/Pattern/Basic.lean
--------------------------------------
/-- The pure externs of `Init/Data/String/Pattern/Basic.lean`. -/
inductive StringPatternExtern : List MyTy → MyTy → Type where
  | lean_string_memcmp : StringPatternExtern [string, string, stringPosRaw, stringPosRaw, stringPosRaw] LeanPrimTy.bool -- String.Slice.Pattern.Internal.memcmpStr (decides `len.offsetBy lstart ≤ lhs.rawEndPos`, `len.offsetBy rstart ≤ rhs.rawEndPos`)

------------------------------
-- Init/Data/String/Slice.lean
------------------------------
/-- The pure externs of `Init/Data/String/Slice.lean`. -/
inductive StringSliceExtern : List MyTy → MyTy → Type where
  | lean_slice_dec_lt : StringSliceExtern [stringSlice, stringSlice] LeanPrimTy.bool -- String.Slice.instDecidableLt
  | lean_slice_hash : StringSliceExtern [stringSlice] uint64 -- String.Slice.hash

-------------------------------
-- Init/Data/String/Modify.lean
-------------------------------
/-- The pure externs of `Init/Data/String/Modify.lean`. -/
inductive StringModifyExtern : List MyTy → MyTy → Type where
  | lean_string_utf8_set__String_Pos_Raw_set : StringModifyExtern [string, stringPosRaw, char] string -- String.Pos.Raw.set
  | lean_string_utf8_set__String_Pos_set : (s : String) → (h_len : 2 ≤ s.length) → StringModifyExtern [(LeanPrimTy.stringPos s h_len), char] string -- String.Pos.set (decides `p ≠ s.endPos`)
  | lean_string_utf8_set__String_set : StringModifyExtern [string, stringPosRaw, char] string -- String.set

----------------------------
-- Init/Data/Ord/String.lean
----------------------------
/-- The pure externs of `Init/Data/Ord/String.lean`. -/
inductive OrdStringExtern : List MyTy → MyTy → Type where
  | lean_string_compare : OrdStringExtern [string, string] ordering -- String.compare

end LeanScript

end
