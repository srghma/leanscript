module

public import Init
public import LeanScript.LeanInitPureExterns
public import LeanScript.ExternEvalHelpers

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
-- The catalogue lists a deprecated Lean name and its replacement as *separate* entries
-- whenever both are `@[extern]`-bound to the same C symbol (`String.get?` and
-- `String.Pos.Raw.get?`, …), so both are given their meaning here and the deprecation
-- linter is not what this file is checking.
set_option linter.deprecated false

/-!
# Running the entries of `LeanScript.LeanInitPureExterns`

`LeanScript.LeanInitPureExterns` is a *catalogue of saturated applications*: each of its
594 constructors holds the **Lean values** an `@[extern]` function of `Init` is applied
to, and the constructor's index is the type the application answers with.  So the
catalogue has a meaning in the obvious way — `lean_nat_add a b` means `Nat.add a b` —
and this file gives it, as one total Lean function.

Three things had to be settled first.

## 1.  A type language to index the catalogue by

`LeanInitPureExtern` is parametrised by the type language `MyTy` it is indexed by,
by that language's denotation `denote : MyTy → Type`, and by the fourteen type formers
it needs (`option`, `list`, `prod`, `io_promise`, `byteArray`, …).  `LeanScript.Ty` is
*not* such a language: it has no `IO.Promise`, no `ShareCommon.State` and no
`IO.Process.Child`, on purpose — those are run-time handles, not values.  So the
catalogue is run at its own instantiation, `ETy` below, which is exactly large enough to
index it and whose denotation `ETy.denote` is a plain, reducible Lean function.

`ETy` is the *semantic* domain of the catalogue, not a new source language: nothing
compiles to it.  What `LeanScript.Eval` needs from the catalogue — the meaning of
`Nat.add`, `String.append`, `Array.push`, … — it takes directly, through
`LeanScript.Expr.Term.prim`, which applies the Lean function itself.  That is why `Term` has no `extern` node: a constructor
of `LeanInitPureExtern` holds *values*, not sub-terms, so it could never be one.

## 2.  `thunk` and `lazy` denote the identity, and there is no `task` or `promise`

As in `LeanScript.Den`, the covariant wrappers of `LeanPrimTyCovariant` that are
*deferred computations* are the identity on values: `ETy.denote (thunk α)` is
`ETy.denote α`.  A `Thunk` and a delayed value both hold one value of the wrapped type
and differ only in *when* it is computed, which a pure semantics does not see, so an
entry that builds one — `Thunk.pure`, `Thunk.mk` — denotes the value itself.

`task` and `promise` are **not** wrappers of the language: they are commented out of
`LeanPrimTyCovariant`, so the catalogue lists no entry that builds or reads one.

## 3.  The catalogue lists exactly the entries that have a meaning

An entry with no meaning as a function of its arguments' *values* is commented out of
`LeanScript.LeanInitPureExterns` itself, rather than answered for with `none` here.
That is what makes this file a total function into the value: there is no `Option`, and
so nothing an evaluator built on it could get stuck on.  Each line that is commented out
below is the record of an entry the catalogue no longer lists, and the reasons are:

* `sorryAx` — `lean_sorry` is `sorryAx`.  Implementing it would put an axiom into every
  term that mentions it; it is left out deliberately, as its own comment in the
  catalogue asks.
* *the host* — the entry reads a fact about the machine the *compiled program* runs on
  (`lean_system_platform_nbits`, `lean_system_platform_windows`,
  `lean_internal_get_hardware_concurrency`, …).  Reading it off the machine that runs
  the compiler would bake in the wrong answer.  The facts that a program may *fix* —
  the version numbers, the git hash, the target — are not host reads at all and are
  given constant answers here.
* *a handle* — the entry speaks about a run-time handle (`IO.Promise`,
  `ShareCommon.State`, `ShareCommon.Object`, `IO.Process.Child`) or about a `Task`,
  none of which is a value.
* *the representation* — the entry reads how a value is *stored* (`lean_ptr_addr`,
  `lean_is_exclusive_obj`, `lean_is_scalar`, …), which a value does not determine.
  Reading a *borrowed* value is not one of these: borrowing is invisible to a pure
  semantics, so `lean_array_get_borrowed` and `lean_array_fget_borrowed` — each of
  which carries the default or the proof it needs — are given their meaning here.
* *private* — the Lean function the entry names is private to its own module and cannot
  be referred to from here.
* `usize` — `LeanPrimTy.usize` abbreviates `uint64`, so the catalogue's index says
  `UInt64` where the Lean function wants a `USize`.  Fixing this is a change to
  `LeanPrimTy` (a `usize` constructor of its own), not to this table.
* *unsafe* — the Lean function is an `unsafe` declaration, which the kernel will not
  let a safe definition mention.
* *no default* — `lean_panic_fn_borrowed` needs an `Inhabited` default that the entry
  does not carry.

Of the 594 entries the catalogue used to list, 97 are commented out of it and the
remaining **497 are given their meaning here**, each by a line of `EExtern.eval`.
-/

namespace LeanScript

/-! ## `ETy`: a type language large enough to index the catalogue -/

/-- The type language the catalogue is run at: the closed types of `LeanScript.Ty`,
    together with the handful of Lean types the catalogue names that `Ty` has no former
    for (`Option`, `List`, `×`, `Ordering`).  It exists only
    to give `LeanInitPureExtern` an instantiation whose denotation is a plain Lean
    function; no source program is translated into it.

    There is no former here for a run-time *handle* — `IO.Promise`, `IO.Process.Child`,
    `ShareCommon.Object`, `ShareCommon.State` — because the catalogue no longer lists an
    entry that speaks about one: a handle is not a value, so an entry holding one could
    not be given a meaning, and an evaluator that had to answer for it would be stuck. -/
inductive ETy where
  /-- A terminal type: `ETy.denote (.prim p)` is `p.denote`. -/
  | prim : LeanPrimTy → ETy
  /-- `array`, `thunk` or `lazy`.  The last two are the identity. -/
  | cov : LeanPrimTyCovariant ETy → ETy
  /-- `Option α`. -/
  | option : ETy → ETy
  /-- `List α`. -/
  | list : ETy → ETy
  /-- `α × β`. -/
  | prod : ETy → ETy → ETy
  /-- `Ordering`. -/
  | ordering : ETy
  -- A byte array is `Array UInt8` and a float array is `Array Float`, so the catalogue
  -- no longer has a former for either and lists no entry that speaks about one.
  -- | byteArray : ETy
  -- | floatArray : ETy

/-- The Lean type an `ETy` describes.  `thunk` and `lazy` are the identity: they are
    *when* a value is computed, which a pure semantics does not see. -/
@[reducible] def ETy.denote : ETy → Type
  | .prim p => p.denote
  | .cov (.array a) => Array (ETy.denote a)
  | .cov (.thunk a) => ETy.denote a
  | .cov (.lazy a) => ETy.denote a
  | .option a => Option (ETy.denote a)
  | .list a => List (ETy.denote a)
  | .prod a b => ETy.denote a × ETy.denote b
  | .ordering => Ordering

instance : Coe LeanPrimTy ETy := ⟨.prim⟩
instance : Coe (LeanPrimTyCovariant LeanPrimTy) ETy := ⟨fun c => .cov (c.map .prim)⟩
instance : Coe (LeanPrimTyCovariant ETy) ETy := ⟨.cov⟩

/-- The catalogue, at the instantiation this file runs it at. -/
abbrev EExtern : ETy → Type :=
  LeanInitPureExtern ETy.denote ETy.option ETy.list ETy.prod .ordering

/-! ## The meaning of each entry

One line per constructor of the catalogue, in the catalogue's own order: `entry
arguments => the Lean function the entry names, applied to them`.  Every constructor the
catalogue has is here — an entry with no pure meaning is not listed by the catalogue at
all — so this is an ordinary total function into the value, with no `Option` in the way
and nothing for an evaluator to get stuck on.  The lines that are commented out are the
entries the catalogue itself no longer lists, kept here as the record of why. -/

/-- The value the entry denotes: a total, terminating Lean function. -/
def EExtern.eval : {t : ETy} → EExtern t → ETy.denote t
  | _, .lean_uint32_of_nat_mk x1 => UInt32.ofBitVec x1
  | _, .lean_uint32_dec_eq x1 x2 => @Decidable.decide _ (UInt32.decEq x1 x2)
  -- a byte or float array: | _, .lean_byte_array_size x1 => ByteArray.size x1
  -- a byte or float array: | _, .lean_string_to_utf8__String_toByteArray x1 => String.toByteArray x1
  | _, .lean_uint32_dec_lt x1 x2 => @Decidable.decide _ (UInt32.decLt x1 x2)
  | _, .lean_nat_div x1 x2 => Nat.div x1 x2
  -- NO sorryAx: _, .lean_sorry x1 x2 => some (sorryAx x2)
  | _, .lean_uint32_of_nat__UInt32_ofNatLT x1 x2 => UInt32.ofNatLT x1 x2
  | _, .lean_uint32_of_nat__Char_ofNatAux x1 x2 => Char.ofNatAux x1 x2
  | _, .lean_array_get_borrowed _ x2 x3 x4 => @Array.get!Internal _ ⟨x2⟩ x3 x4  -- the entry carries the `Inhabited` default itself; borrowing is a representation detail a pure semantics does not see
  | _, .lean_uint8_to_nat__UInt8_toBitVec x1 => UInt8.toBitVec x1
  | _, .lean_nat_dec_lt x1 x2 => @Decidable.decide _ (Nat.decLt x1 x2)
  -- a byte or float array: | _, .lean_string_from_utf8_unchecked x1 x2 => String.ofByteArray x1 x2
  | _, .lean_nat_mod__Nat_modCore x1 x2 => x1 % x2  -- `Nat.modCore_eq_mod`: `Nat.modCore` is `%`, and is `@[irreducible]` with no compiled form
  | _, .lean_nat_mod__Nat_mod x1 x2 => Nat.mod x1 x2
  | _, .lean_array_push _ x2 x3 => Array.push x2 x3
  -- a byte or float array: | _, .lean_byte_array_mk x1 => ByteArray.mk x1
  | _, .lean_nat_sub x1 x2 => Nat.sub x1 x2
  | _, .lean_uint8_dec_lt x1 x2 => @Decidable.decide _ (UInt8.decLt x1 x2)
  -- a byte or float array: | _, .lean_byte_array_data x1 => ByteArray.data x1
  -- NO handle: | _, .lean_system_platform_nbits => some (@Decidable.decide _ (System.Platform.getNumBits))
  | _, .lean_uint32_dec_le x1 x2 => @Decidable.decide _ (UInt32.decLe x1 x2)
  | _, .lean_array_get_size _ x2 => Array.size x2
  | _, .lean_array_to_list _ x2 => Array.toList x2
  | _, .lean_nat_dec_eq__Nat_decEq x1 x2 => @Decidable.decide _ (Nat.decEq x1 x2)
  | _, .lean_nat_dec_eq__Nat_beq x1 x2 => Nat.beq x1 x2
  | _, .lean_array_fget_borrowed _ x2 x3 x4 => Array.getInternal x2 x3 x4  -- borrowing is a representation detail a pure semantics does not see
  | _, .lean_mk_empty_array_with_capacity__Array_emptyWithCapacity _ x2 => Array.emptyWithCapacity x2
  | _, .lean_mk_empty_array_with_capacity__Array_mkEmpty _ x2 => Array.mkEmpty x2
  | _, .lean_uint8_of_nat__UInt8_ofNat x1 => UInt8.ofNat x1
  | _, .lean_uint8_of_nat__UInt8_ofNatLT x1 x2 => UInt8.ofNatLT x1 x2
  -- NO unsafe:| _, .lean_is_scalar x1 x2 => some (isScalarObj x2)
  | _, .lean_uint8_dec_le x1 x2 => @Decidable.decide _ (UInt8.decLe x1 x2)
  | _, .lean_nat_dec_le__Nat_ble x1 x2 => Nat.ble x1 x2
  | _, .lean_nat_dec_le__Nat_decLe x1 x2 => @Decidable.decide _ (Nat.decLe x1 x2)
  | _, .lean_array_get _ x2 x3 x4 => @Array.get!Internal _ ⟨x2⟩ x3 x4
  | _, .lean_nat_add x1 x2 => Nat.add x1 x2
  -- NO inhabited: | _, .lean_panic_fn_borrowed αt msg => some (panicCore msg)  -- `panicCore` needs an `Inhabited` default, which this entry does not carry
  | _, .lean_uint16_to_nat__UInt16_toBitVec x1 => UInt16.toBitVec x1
  | _, .lean_uint16_of_nat_mk x1 => UInt16.ofBitVec x1
  | _, .lean_uint16_dec_eq x1 x2 => @Decidable.decide _ (UInt16.decEq x1 x2)
  | _, .lean_string_dec_eq x1 x2 => @Decidable.decide _ (String.decEq x1 x2)
  | _, .lean_nat_pred x1 => Nat.pred x1
  -- NO usize: | _, .lean_usize_of_nat__USize_ofNatLT x1 x2 => some (@Decidable.decide _ (USize.ofNatLT x1 x2))
  | _, .lean_string_mk__String_ofList x1 => String.ofList x1
  | _, .lean_string_hash x1 => String.hash x1
  | _, .lean_uint64_to_nat__UInt64_toBitVec x1 => UInt64.toBitVec x1
  | _, .lean_uint64_of_nat_mk x1 => UInt64.ofBitVec x1
  | _, .lean_uint32_to_nat__UInt32_toNat x1 => UInt32.toNat x1
  | _, .lean_uint32_to_nat__UInt32_toBitVec x1 => UInt32.toBitVec x1
  | _, .lean_uint64_dec_eq x1 x2 => @Decidable.decide _ (UInt64.decEq x1 x2)
  | _, .lean_uint16_of_nat__UInt16_ofNatLT x1 x2 => UInt16.ofNatLT x1 x2
  | _, .lean_name_eq x1 x2 => Lean.Name.beq x1 x2
  | _, .lean_uint8_of_nat_mk x1 => UInt8.ofBitVec x1
  -- a byte or float array: | _, .lean_mk_empty_byte_array x1 => ByteArray.emptyWithCapacity x1
  | _, .lean_uint8_dec_eq x1 x2 => @Decidable.decide _ (UInt8.decEq x1 x2)
  | _, .lean_nat_pow x1 x2 => Nat.pow x1 x2
  -- NO usize: | _, .lean_usize_dec_eq x1 x2 => some (@Decidable.decide _ (USize.decEq x1 x2))
  -- NO usize: | _, .lean_usize_of_nat_mk x1 => some (@Decidable.decide _ (USize.ofBitVec x1))
  | _, .lean_array_fget _ x2 x3 x4 => Array.getInternal x2 x3 x4
  | _, .lean_nat_mul x1 x2 => Nat.mul x1 x2
  -- NO usize: | _, .lean_usize_to_nat__USize_toBitVec x1 => some (@Decidable.decide _ (USize.toBitVec x1))
  | _, .lean_string_utf8_byte_size x1 => String.utf8ByteSize x1
  -- a byte or float array: | _, .lean_byte_array_push x1 x2 => ByteArray.push x1 x2
  | _, .lean_array_mk _ x2 => Array.mk x2
  | _, .lean_uint64_mix_hash x1 x2 => mixHash x1 x2
  | _, .lean_uint64_of_nat__UInt64_ofNatLT x1 x2 => UInt64.ofNatLT x1 x2
  -- NO handle: | _, .lean_task_map _ _ x3 x4 x5 x6 => some (@Decidable.decide _ (Task.map x3 x4 x5 x6))
  -- NO handle: | _, .lean_task_spawn _ x2 x3 => some (@Decidable.decide _ (Task.spawn x2 x3))
  | _, .lean_strict_or x1 x2 => strictOr x1 x2
  | _, .lean_thunk_pure _ x2 => x2  -- a thunk denotes the value it will answer with
  | _, .lean_mk_thunk _ x2 => x2  -- a thunk denotes the value its body answers with
  -- NO handle: | _, .lean_task_get_own _ x2 => some (@Decidable.decide _ (Task.get x2))
  -- NO handle: | _, .lean_task_pure _ x2 => some (@Decidable.decide _ (Task.pure x2))
  | _, .lean_thunk_get_own _ x2 => Thunk.get x2
  | _, .lean_strict_and x1 x2 => strictAnd x1 x2
  -- NO handle: | _, .lean_task_bind _ _ x3 x4 x5 x6 => some (@Decidable.decide _ (Task.bind x3 x4 x5 x6))
  | _, .lean_nat_to_int x1 => Int.ofNat x1
  | _, .lean_int_dec_le x1 x2 => @Decidable.decide _ (Int.decLe x1 x2)
  | _, .lean_int_dec_lt x1 x2 => @Decidable.decide _ (Int.decLt x1 x2)
  | _, .lean_int_dec_eq x1 x2 => @Decidable.decide _ (Int.decEq x1 x2)
  | _, .lean_int_mul x1 x2 => Int.mul x1 x2
  | _, .lean_int_dec_nonneg x1 => @Decidable.decide _ (Int.decNonneg x1)
  | _, .lean_int_neg_succ_of_nat x1 => Int.negSucc x1
  | _, .lean_int_add x1 x2 => Int.add x1 x2
  | _, .lean_int_neg x1 => Int.neg x1
  | _, .lean_int_sub x1 x2 => Int.sub x1 x2
  | _, .lean_nat_abs x1 => Int.natAbs x1
  | _, .lean_nat_div_exact x1 x2 x3 => Nat.divExact x1 x2 x3
  | _, .lean_nat_lxor x1 x2 => Nat.xor x1 x2
  | _, .lean_nat_shiftl x1 x2 => Nat.shiftLeft x1 x2
  | _, .lean_nat_shiftr x1 x2 => Nat.shiftRight x1 x2
  | _, .lean_nat_land x1 x2 => Nat.land x1 x2
  | _, .lean_nat_lor x1 x2 => Nat.lor x1 x2
  | _, .lean_uint64_to_nat__UInt64_toNat x1 => UInt64.toNat x1
  | _, .lean_uint32_to_uint8 x1 => UInt32.toUInt8 x1
  -- NO usize: | _, .lean_usize_to_nat__USize_toNat x1 => some (@Decidable.decide _ (USize.toNat x1))
  | _, .lean_uint64_to_uint32 x1 => UInt64.toUInt32 x1
  | _, .lean_uint32_to_uint16 x1 => UInt32.toUInt16 x1
  | _, .lean_uint16_to_uint32 x1 => UInt16.toUInt32 x1
  | _, .lean_uint32_to_uint64 x1 => UInt32.toUInt64 x1
  | _, .lean_uint32_of_nat__UInt32_ofNat x1 => UInt32.ofNat x1
  -- NO usize: | _, .lean_usize_add x1 x2 => some (@Decidable.decide _ (USize.add x1 x2))
  | _, .lean_uint32_sub x1 x2 => UInt32.sub x1 x2
  | _, .lean_uint16_to_nat__UInt16_toNat x1 => UInt16.toNat x1
  | _, .lean_uint16_to_uint8 x1 => UInt16.toUInt8 x1
  -- NO usize: | _, .lean_usize_sub x1 x2 => some (@Decidable.decide _ (USize.sub x1 x2))
  | _, .lean_uint32_add x1 x2 => UInt32.add x1 x2
  -- NO usize: | _, .lean_usize_of_nat__USize_ofNat x1 => some (@Decidable.decide _ (USize.ofNat x1))
  -- NO usize: | _, .lean_usize_dec_le x1 x2 => some (@Decidable.decide _ (USize.decLe x1 x2))
  | _, .lean_uint8_to_uint64 x1 => UInt8.toUInt64 x1
  | _, .lean_uint8_to_nat__UInt8_toNat x1 => UInt8.toNat x1
  | _, .lean_uint64_of_nat__UInt64_ofNat x1 => UInt64.ofNat x1
  | _, .lean_uint8_to_uint32 x1 => UInt8.toUInt32 x1
  | _, .lean_uint16_of_nat__UInt16_ofNat x1 => UInt16.ofNat x1
  | _, .lean_uint16_to_uint64 x1 => UInt16.toUInt64 x1
  -- NO usize: | _, .lean_usize_dec_lt x1 x2 => some (@Decidable.decide _ (USize.decLt x1 x2))
  | _, .lean_uint64_to_uint8 x1 => UInt64.toUInt8 x1
  | _, .lean_uint64_to_uint16 x1 => UInt64.toUInt16 x1
  | _, .lean_uint8_to_uint16 x1 => UInt8.toUInt16 x1
  | _, .lean_string_utf8_get__String_Internal_get x1 x2 => String.Internal.get x1 x2
  | _, .lean_string_trim x1 => String.Internal.trim x1
  | _, .lean_substring_drop x1 x2 => Substring.Raw.Internal.drop x1 x2
  | _, .lean_substring_prev x1 x2 => Substring.Raw.Internal.prev x1 x2
  | _, .lean_substring_extract x1 x2 x3 => Substring.Raw.Internal.extract x1 x2 x3
  | _, .lean_string_foldl x1 x2 x3 => String.Internal.foldl x1 x2 x3
  | _, .lean_substring_tostring x1 => Substring.Raw.Internal.toString x1
  | _, .lean_string_append__String_Internal_append x1 x2 => String.Internal.append x1 x2
  | _, .lean_string_get_byte_fast__String_Internal_getUTF8Byte x1 x2 x3 => String.Internal.getUTF8Byte x1 x2 x3
  | _, .lean_string_isempty x1 => String.Internal.isEmpty x1
  | _, .lean_string_push x1 x2 => String.push x1 x2
  | _, .lean_string_isprefixof x1 x2 => String.Internal.isPrefixOf x1 x2
  | _, .lean_string_dropright x1 x2 => String.Internal.dropRight x1 x2
  | _, .lean_substring_takewhile x1 x2 => Substring.Raw.Internal.takeWhile x1 x2
  | _, .lean_substring_get x1 x2 => Substring.Raw.Internal.get x1 x2
  | _, .lean_string_uget_byte_fast x1 x2 x3 => String.Internal.ugetUTF8Byte x1 x2 x3
  | _, .lean_string_contains x1 x2 => String.Internal.contains x1 x2
  | _, .lean_string_front x1 => String.Internal.front x1
  | _, .lean_string_posof x1 x2 => String.Internal.posOf x1 x2
  | _, .lean_substring_all x1 x2 => Substring.Raw.Internal.all x1 x2
  | _, .lean_string_intercalate x1 x2 => String.Internal.intercalate x1 x2
  | _, .lean_string_drop x1 x2 => String.Internal.drop x1 x2
  | _, .lean_string_length__String_Internal_length x1 => String.Internal.length x1
  | _, .lean_string_utf8_at_end__String_Internal_atEnd x1 x2 => String.Internal.atEnd x1 x2
  | _, .lean_substring_beq x1 x2 => Substring.Raw.Internal.beq x1 x2
  | _, .lean_string_nextwhile x1 x2 x3 => String.Internal.nextWhile x1 x2 x3
  | _, .lean_string_utf8_next__String_Internal_next x1 x2 => String.Internal.next x1 x2
  | _, .lean_string_mk__String_mk x1 => String.mk x1
  | _, .lean_string_any x1 x2 => String.Internal.any x1 x2
  | _, .lean_string_pushn x1 x2 x3 => String.Internal.pushn x1 x2 x3
  | _, .lean_string_capitalize x1 => String.Internal.capitalize x1
  | _, .lean_string_utf8_extract__String_Internal_extract x1 x2 x3 => String.Internal.extract x1 x2 x3
  | _, .lean_string_pos_min x1 x2 => String.Pos.Raw.Internal.min x1 x2
  | _, .lean_substring_front x1 => Substring.Raw.Internal.front x1
  | _, .lean_string_pos_sub x1 x2 => String.Pos.Raw.Internal.sub x1 x2
  | _, .lean_substring_isempty x1 => Substring.Raw.Internal.isEmpty x1
  | _, .lean_string_offsetofpos x1 x2 => String.Internal.offsetOfPos x1 x2
  -- NO usize: | _, .lean_string_of_usize x1 => some (@Decidable.decide _ (USize.repr x1))
  -- NO handle: | _, .lean_dbg_sleep _ x2 x3 => some (@Decidable.decide _ (dbgSleep x2 x3))
  -- NO usize: | _, .lean_ptr_addr _ x2 => some (@Decidable.decide _ (ptrAddrUnsafe x2))
  -- NO handle: | _, .lean_dbg_trace _ x2 x3 => some (@Decidable.decide _ (dbgTrace x2 x3))
  | _, .lean_dbg_trace_if_shared _ x2 x3 => dbgTraceIfShared x2 x3
  -- NO handle: | _, .lean_dbg_stack_trace _ x2 => some (@Decidable.decide _ (dbgStackTrace x2))
  -- NO unsafe:| _, .lean_is_exclusive_obj x1 x2 => some (isExclusiveUnsafe x2)
  | _, .lean_array_set _ x2 x3 x4 => Array.set! x2 x3 x4
  | _, .lean_array_fset _ x2 x3 x4 x5 => Array.set x2 x3 x4 x5
  | _, .lean_array_fswap _ x2 x3 x4 x5 x6 => Array.swap x2 x3 x4 x5 x6
  | _, .lean_array_uget _ x2 x3 x4 => Array.uget x2 x3 x4
  | _, .lean_mk_array _ x2 x3 => Array.replicate x2 x3
  | _, .lean_array_swap _ x2 x3 x4 => Array.swapIfInBounds x2 x3 x4
  -- NO unsafe:| _, .lean_array_uget_borrowed x1 x2 x3 x4 => some (Array.ugetBorrowed x2 x3 x4)
  | _, .lean_array_pop _ x2 => Array.pop x2
  | _, .lean_array_uset _ x2 x3 x4 x5 => Array.uset x2 x3 x4 x5
  -- NO usize: | _, .lean_array_size _ x2 => some (@Decidable.decide _ (Array.usize x2))
  | _, .lean_version_get_special_desc => ("leanscript" : String)
  | _, .lean_version_get_is_release => false
  | _, .lean_version_get_major => (0 : Nat)
  | _, .lean_version_get_patch => (0 : Nat)
  | _, .lean_internal_is_stage0 => false
  | _, .lean_version_get_minor => (0 : Nat)
  | _, .lean_get_githash => ("leanscript" : String)
  | _, .lean_internal_has_llvm_backend => false
  | _, .lean_nat_log2 x1 => Nat.log2 x1
  | _, .lean_int_emod x1 x2 => Int.emod x1 x2
  | _, .lean_int_div_exact x1 x2 x3 => Int.divExact x1 x2 x3
  | _, .lean_int_mod x1 x2 => Int.tmod x1 x2
  | _, .lean_int_ediv x1 x2 => Int.ediv x1 x2
  | _, .lean_int_div x1 x2 => Int.tdiv x1 x2
  | _, .lean_nat_gcd__Nat_gcd__unary x1 => Nat.gcd x1.1 x1.2  -- `Nat.gcd._unary` is the packed form of `Nat.gcd`, and is noncomputable
  | _, .lean_nat_gcd__Nat_gcd x1 x2 => Nat.gcd x1 x2
  | _, .lean_uint64_shift_left x1 x2 => UInt64.shiftLeft x1 x2
  | _, .lean_uint32_mod x1 x2 => UInt32.mod x1 x2
  | _, .lean_uint16_neg x1 => UInt16.neg x1
  -- NO usize: | _, .lean_usize_land x1 x2 => some (@Decidable.decide _ (USize.land x1 x2))
  -- NO usize: | _, .lean_usize_mul x1 x2 => some (@Decidable.decide _ (USize.mul x1 x2))
  -- NO usize: | _, .lean_uint16_to_usize x1 => some (@Decidable.decide _ (UInt16.toUSize x1))
  | _, .lean_uint64_shift_right x1 x2 => UInt64.shiftRight x1 x2
  -- NO usize: | _, .lean_usize_shift_left x1 x2 => some (@Decidable.decide _ (USize.shiftLeft x1 x2))
  | _, .lean_uint16_add x1 x2 => UInt16.add x1 x2
  -- NO usize: | _, .lean_usize_xor x1 x2 => some (@Decidable.decide _ (USize.xor x1 x2))
  | _, .lean_uint64_complement x1 => UInt64.complement x1
  | _, .lean_bool_to_uint32 x1 => Bool.toUInt32 x1
  | _, .lean_uint16_lor x1 x2 => UInt16.lor x1 x2
  | _, .lean_uint16_mul x1 x2 => UInt16.mul x1 x2
  | _, .lean_uint16_land x1 x2 => UInt16.land x1 x2
  | _, .lean_uint8_sub x1 x2 => UInt8.sub x1 x2
  | _, .lean_uint32_div x1 x2 => UInt32.div x1 x2
  | _, .lean_uint64_add x1 x2 => UInt64.add x1 x2
  | _, .lean_uint8_neg x1 => UInt8.neg x1
  | _, .lean_uint16_complement x1 => UInt16.complement x1
  | _, .lean_uint64_lor x1 x2 => UInt64.lor x1 x2
  | _, .lean_uint64_mod x1 x2 => UInt64.mod x1 x2
  | _, .lean_uint8_lor x1 x2 => UInt8.lor x1 x2
  | _, .lean_uint32_shift_right x1 x2 => UInt32.shiftRight x1 x2
  | _, .lean_uint16_xor x1 x2 => UInt16.xor x1 x2
  -- NO usize: | _, .lean_usize_lor x1 x2 => some (@Decidable.decide _ (USize.lor x1 x2))
  | _, .lean_uint8_div x1 x2 => UInt8.div x1 x2
  | _, .lean_uint16_shift_left x1 x2 => UInt16.shiftLeft x1 x2
  | _, .lean_uint32_neg x1 => UInt32.neg x1
  | _, .lean_uint16_mod x1 x2 => UInt16.mod x1 x2
  -- NO usize: | _, .lean_usize_neg x1 => some (@Decidable.decide _ (USize.neg x1))
  | _, .lean_uint64_div x1 x2 => UInt64.div x1 x2
  | _, .lean_uint16_dec_lt x1 x2 => @Decidable.decide _ (UInt16.decLt x1 x2)
  | _, .lean_uint8_shift_right x1 x2 => UInt8.shiftRight x1 x2
  -- NO usize: | _, .lean_usize_to_uint64 x1 => some (@Decidable.decide _ (USize.toUInt64 x1))
  | _, .lean_uint32_lor x1 x2 => UInt32.lor x1 x2
  | _, .lean_uint64_mul x1 x2 => UInt64.mul x1 x2
  -- NO usize: | _, .lean_usize_shift_right x1 x2 => some (@Decidable.decide _ (USize.shiftRight x1 x2))
  | _, .lean_uint64_land x1 x2 => UInt64.land x1 x2
  | _, .lean_uint8_shift_left x1 x2 => UInt8.shiftLeft x1 x2
  | _, .lean_uint16_div x1 x2 => UInt16.div x1 x2
  | _, .lean_bool_to_uint64 x1 => Bool.toUInt64 x1
  | _, .lean_uint8_land x1 x2 => UInt8.land x1 x2
  | _, .lean_uint64_dec_le x1 x2 => @Decidable.decide _ (UInt64.decLe x1 x2)
  | _, .lean_uint8_mul x1 x2 => UInt8.mul x1 x2
  -- NO usize: | _, .lean_usize_of_nat__USize_ofNat32 x1 x2 => some (@Decidable.decide _ (USize.ofNat32 x1 x2))
  | _, .lean_uint64_sub x1 x2 => UInt64.sub x1 x2
  | _, .lean_uint64_neg x1 => UInt64.neg x1
  | _, .lean_uint8_add x1 x2 => UInt8.add x1 x2
  -- NO usize: | _, .lean_usize_div x1 x2 => some (@Decidable.decide _ (USize.div x1 x2))
  -- NO usize: | _, .lean_uint32_to_usize x1 => some (@Decidable.decide _ (UInt32.toUSize x1))
  | _, .lean_uint8_complement x1 => UInt8.complement x1
  -- NO usize: | _, .lean_usize_to_uint16 x1 => some (@Decidable.decide _ (USize.toUInt16 x1))
  | _, .lean_uint32_xor x1 x2 => UInt32.xor x1 x2
  | _, .lean_uint16_dec_le x1 x2 => @Decidable.decide _ (UInt16.decLe x1 x2)
  -- NO usize: | _, .lean_usize_to_uint8 x1 => some (@Decidable.decide _ (USize.toUInt8 x1))
  | _, .lean_uint32_shift_left x1 x2 => UInt32.shiftLeft x1 x2
  | _, .lean_uint16_sub x1 x2 => UInt16.sub x1 x2
  | _, .lean_uint32_mul x1 x2 => UInt32.mul x1 x2
  | _, .lean_uint32_land x1 x2 => UInt32.land x1 x2
  -- NO usize: | _, .lean_usize_mod x1 x2 => some (@Decidable.decide _ (USize.mod x1 x2))
  | _, .lean_uint8_mod x1 x2 => UInt8.mod x1 x2
  | _, .lean_uint64_dec_lt x1 x2 => @Decidable.decide _ (UInt64.decLt x1 x2)
  | _, .lean_bool_to_uint8 x1 => Bool.toUInt8 x1
  | _, .lean_uint32_complement x1 => UInt32.complement x1
  -- NO usize: | _, .lean_uint8_to_usize x1 => some (@Decidable.decide _ (UInt8.toUSize x1))
  | _, .lean_bool_to_uint16 x1 => Bool.toUInt16 x1
  | _, .lean_uint8_xor x1 x2 => UInt8.xor x1 x2
  -- NO usize: | _, .lean_bool_to_usize x1 => some (@Decidable.decide _ (Bool.toUSize x1))
  -- NO usize: | _, .lean_uint64_to_usize x1 => some (@Decidable.decide _ (UInt64.toUSize x1))
  | _, .lean_uint16_shift_right x1 x2 => UInt16.shiftRight x1 x2
  -- NO usize: | _, .lean_usize_to_uint32 x1 => some (@Decidable.decide _ (USize.toUInt32 x1))
  -- NO usize: | _, .lean_usize_complement x1 => some (@Decidable.decide _ (USize.complement x1))
  | _, .lean_uint64_xor x1 x2 => UInt64.xor x1 x2
  -- a byte or float array: | _, .lean_byte_array_copy_slice x1 x2 x3 x4 x5 x6 => ByteArray.copySlice x1 x2 x3 x4 x5 x6
  -- a byte or float array: | _, .lean_byte_array_hash x1 => ByteArray.hash x1
  -- NO usize: | _, .lean_sarray_size__ByteArray_usize x1 => some (@Decidable.decide _ (ByteArray.usize x1))
  -- a byte or float array: | _, .lean_sarray_dec_eq__ByteArray_beq x1 x2 => ByteArray.beq x1 x2
  -- a byte or float array: | _, .lean_sarray_dec_eq__ByteArray_decEq x1 x2 => @Decidable.decide _ (ByteArray.decEq x1 x2)
  -- a byte or float array: | _, .lean_byte_array_set x1 x2 x3 => ByteArray.set! x1 x2 x3
  -- a byte or float array: | _, .lean_byte_array_fget x1 x2 x3 => ByteArray.get x1 x2 x3
  -- a byte or float array: | _, .lean_byte_array_uset x1 x2 x3 x4 => ByteArray.uset x1 x2 x3 x4
  -- a byte or float array: | _, .lean_byte_array_fset x1 x2 x3 x4 => ByteArray.set x1 x2 x3 x4
  -- a byte or float array: | _, .lean_byte_array_uget x1 x2 x3 => ByteArray.uget x1 x2 x3
  -- a byte or float array: | _, .lean_byte_array_get x1 x2 => ByteArray.get! x1 x2
  | _, .lean_string_get_byte_fast__String_getUtf8Byte x1 x2 x3 => String.getUtf8Byte x1 x2 x3
  | _, .lean_string_get_byte_fast__String_getUTF8Byte x1 x2 x3 => String.getUTF8Byte x1 x2 x3
  -- a byte or float array: | _, .lean_string_to_utf8__String_toUTF8 x1 => String.toUTF8 x1
  | _, .lean_string_append__String_append x1 x2 => String.append x1 x2
  -- NO handle: | _, .lean_internal_get_hardware_concurrency => some (@Decidable.decide _ (System.Platform.Internal.getHardwareConcurrency))
  -- NO handle: | _, .lean_system_platform_linux => some (@Decidable.decide _ (System.Platform.getIsLinux))
  | _, .lean_system_platform_emscripten => false
  | _, .lean_system_platform_target => ("nodeorbrowser" : String)
  -- NO handle: | _, .lean_system_platform_windows => some (@Decidable.decide _ (System.Platform.getIsWindows))
  -- NO handle: | _, .lean_system_platform_osx => some (@Decidable.decide _ (System.Platform.getIsOSX))
  | _, .lean_string_utf8_next__String_next x1 x2 => String.next x1 x2
  | _, .lean_string_utf8_next__String_Pos_Raw_next x1 x2 => String.Pos.Raw.next x1 x2
  | _, .lean_string_utf8_get__String_Pos_Raw_get x1 x2 => String.Pos.Raw.get x1 x2
  | _, .lean_string_utf8_get__String_get x1 x2 => String.get x1 x2
  | _, .lean_string_utf8_get_opt__String_Pos_Raw_get? x1 x2 => String.Pos.Raw.get? x1 x2
  | _, .lean_string_utf8_get_opt__String_get? x1 x2 => String.get? x1 x2
  | _, .lean_string_utf8_prev__String_Pos_Raw_prev x1 x2 => String.Pos.Raw.prev x1 x2
  | _, .lean_string_utf8_prev__String_prev x1 x2 => String.prev x1 x2
  | _, .lean_string_utf8_next_fast__String_next' x1 x2 x3 => String.next' x1 x2 x3
  | _, .lean_string_utf8_next_fast__String_Pos_Raw_next' x1 x2 x3 => String.Pos.Raw.next' x1 x2 x3
  | _, .lean_string_utf8_next_fast__String_Pos_next x1 x2 => String.Pos.next x1 x2
  | _, .lean_string_data__String_data x1 => String.data x1
  | _, .lean_string_data__String_toList x1 => String.toList x1
  | _, .lean_string_utf8_extract_fast x1 x2 => String.extract x1 x2
  | _, .lean_string_utf8_at_end__String_atEnd x1 x2 => String.atEnd x1 x2
  | _, .lean_string_utf8_at_end__String_Pos_Raw_atEnd x1 x2 => String.Pos.Raw.atEnd x1 x2
  | _, .lean_string_utf8_get_bang__String_Pos_Raw_get! x1 x2 => String.Pos.Raw.get! x1 x2
  | _, .lean_string_utf8_get_bang__String_get! x1 x2 => String.get! x1 x2
  -- a byte or float array: | _, .lean_string_utf8_get_fast__String_decodeChar x1 x2 x3 => String.decodeChar x1 x2 x3
  | _, .lean_string_utf8_get_fast__String_get' x1 x2 x3 => String.get' x1 x2 x3
  | _, .lean_string_utf8_get_fast__String_Pos_Raw_get' x1 x2 x3 => String.Pos.Raw.get' x1 x2 x3
  | _, .lean_string_is_valid_pos x1 x2 => String.Pos.Raw.isValid x1 x2
  | _, .lean_string_dec_lt x1 x2 => @Decidable.decide _ (String.decidableLT x1 x2)
  -- a byte or float array: | _, .lean_string_validate_utf8 x1 => ByteArray.validateUTF8 x1
  | _, .lean_string_utf8_extract__String_Pos_Raw_extract x1 x2 x3 => String.Pos.Raw.extract x1 x2 x3
  | _, .lean_string_length__String_length x1 => String.length x1
  -- NO usize: | _, .lean_isize_complement x1 => some (@Decidable.decide _ (ISize.complement x1))
  | _, .lean_int8_add x1 x2 => Int8.add x1 x2
  | _, .lean_int16_of_nat x1 => Int16.ofNat x1
  | _, .lean_int16_dec_le x1 x2 => @Decidable.decide _ (Int16.decLe x1 x2)
  | _, .lean_int32_of_int x1 => Int32.ofInt x1
  -- NO usize: | _, .lean_int64_to_isize x1 => some (@Decidable.decide _ (Int64.toISize x1))
  | _, .lean_int32_land x1 x2 => Int32.land x1 x2
  | _, .lean_int8_div x1 x2 => Int8.div x1 x2
  | _, .lean_int32_mul x1 x2 => Int32.mul x1 x2
  | _, .lean_int64_sub x1 x2 => Int64.sub x1 x2
  | _, .lean_int16_shift_right x1 x2 => Int16.shiftRight x1 x2
  -- NO usize: | _, .lean_isize_to_int8 x1 => some (@Decidable.decide _ (ISize.toInt8 x1))
  | _, .lean_int64_xor x1 x2 => Int64.xor x1 x2
  | _, .lean_int32_dec_le x1 x2 => @Decidable.decide _ (Int32.decLe x1 x2)
  | _, .lean_int32_of_nat x1 => Int32.ofNat x1
  -- NO usize: | _, .lean_isize_xor x1 x2 => some (@Decidable.decide _ (ISize.xor x1 x2))
  | _, .lean_int64_to_int8 x1 => Int64.toInt8 x1
  -- NO usize: | _, .lean_isize_shift_left x1 x2 => some (@Decidable.decide _ (ISize.shiftLeft x1 x2))
  | _, .lean_int64_mul x1 x2 => Int64.mul x1 x2
  | _, .lean_int32_to_int64 x1 => Int32.toInt64 x1
  | _, .lean_int8_to_int16 x1 => Int8.toInt16 x1
  | _, .lean_int32_sub x1 x2 => Int32.sub x1 x2
  | _, .lean_int64_of_int x1 => Int64.ofInt x1
  -- NO usize: | _, .lean_int32_to_isize x1 => some (@Decidable.decide _ (Int32.toISize x1))
  | _, .lean_int64_land x1 x2 => Int64.land x1 x2
  | _, .lean_int8_shift_right x1 x2 => Int8.shiftRight x1 x2
  | _, .lean_int64_lor x1 x2 => Int64.lor x1 x2
  | _, .lean_int16_div x1 x2 => Int16.div x1 x2
  -- NO usize: | _, .lean_isize_mod x1 x2 => some (@Decidable.decide _ (ISize.mod x1 x2))
  | _, .lean_int32_neg x1 => Int32.neg x1
  | _, .lean_int8_mod x1 x2 => Int8.mod x1 x2
  | _, .lean_int32_abs x1 => Int32.abs x1
  | _, .lean_bool_to_int8 x1 => Bool.toInt8 x1
  -- NO usize: | _, .lean_isize_shift_right x1 x2 => some (@Decidable.decide _ (ISize.shiftRight x1 x2))
  -- NO usize: | _, .lean_isize_to_int16 x1 => some (@Decidable.decide _ (ISize.toInt16 x1))
  | _, .lean_int8_shift_left x1 x2 => Int8.shiftLeft x1 x2
  | _, .lean_int16_dec_lt x1 x2 => @Decidable.decide _ (Int16.decLt x1 x2)
  | _, .lean_int8_xor x1 x2 => Int8.xor x1 x2
  | _, .lean_int32_dec_eq x1 x2 => @Decidable.decide _ (Int32.decEq x1 x2)
  | _, .lean_int16_to_int x1 => Int16.toInt x1
  | _, .lean_int16_mod x1 x2 => Int16.mod x1 x2
  -- NO usize: | _, .lean_isize_div x1 x2 => some (@Decidable.decide _ (ISize.div x1 x2))
  | _, .lean_int16_dec_eq x1 x2 => @Decidable.decide _ (Int16.decEq x1 x2)
  | _, .lean_int8_complement x1 => Int8.complement x1
  -- NO usize: | _, .lean_isize_add x1 x2 => some (@Decidable.decide _ (ISize.add x1 x2))
  | _, .lean_bool_to_int16 x1 => Bool.toInt16 x1
  | _, .lean_int32_dec_lt x1 x2 => @Decidable.decide _ (Int32.decLt x1 x2)
  -- NO usize: | _, .lean_isize_lor x1 x2 => some (@Decidable.decide _ (ISize.lor x1 x2))
  | _, .lean_int64_mod x1 x2 => Int64.mod x1 x2
  -- NO usize: | _, .lean_isize_of_int x1 => some (@Decidable.decide _ (ISize.ofInt x1))
  | _, .lean_int64_shift_left x1 x2 => Int64.shiftLeft x1 x2
  | _, .lean_int16_abs x1 => Int16.abs x1
  -- NO usize: | _, .lean_isize_land x1 x2 => some (@Decidable.decide _ (ISize.land x1 x2))
  | _, .lean_int16_to_int32 x1 => Int16.toInt32 x1
  -- NO usize: | _, .lean_isize_mul x1 x2 => some (@Decidable.decide _ (ISize.mul x1 x2))
  -- NO usize: | _, .lean_isize_to_int x1 => some (@Decidable.decide _ (ISize.toInt x1))
  | _, .lean_int64_dec_lt x1 x2 => @Decidable.decide _ (Int64.decLt x1 x2)
  -- NO usize: | _, .lean_isize_dec_le x1 x2 => some (@Decidable.decide _ (ISize.decLe x1 x2))
  | _, .lean_int8_dec_eq x1 x2 => @Decidable.decide _ (Int8.decEq x1 x2)
  | _, .lean_int32_xor x1 x2 => Int32.xor x1 x2
  -- NO usize: | _, .lean_isize_of_nat x1 => some (@Decidable.decide _ (ISize.ofNat x1))
  | _, .lean_int16_complement x1 => Int16.complement x1
  | _, .lean_int32_shift_left x1 x2 => Int32.shiftLeft x1 x2
  -- NO usize: | _, .lean_isize_to_int64 x1 => some (@Decidable.decide _ (ISize.toInt64 x1))
  -- NO usize: | _, .lean_isize_sub x1 x2 => some (@Decidable.decide _ (ISize.sub x1 x2))
  | _, .lean_int64_complement x1 => Int64.complement x1
  -- NO usize: | _, .lean_isize_abs x1 => some (@Decidable.decide _ (ISize.abs x1))
  | _, .lean_int16_land x1 x2 => Int16.land x1 x2
  | _, .lean_int16_of_int x1 => Int16.ofInt x1
  | _, .lean_int32_shift_right x1 x2 => Int32.shiftRight x1 x2
  | _, .lean_int8_neg x1 => Int8.neg x1
  | _, .lean_int16_mul x1 x2 => Int16.mul x1 x2
  -- NO usize: | _, .lean_isize_to_int32 x1 => some (@Decidable.decide _ (ISize.toInt32 x1))
  | _, .lean_int64_to_int32 x1 => Int64.toInt32 x1
  | _, .lean_int16_shift_left x1 x2 => Int16.shiftLeft x1 x2
  | _, .lean_int64_abs x1 => Int64.abs x1
  | _, .lean_int32_complement x1 => Int32.complement x1
  | _, .lean_int16_xor x1 x2 => Int16.xor x1 x2
  | _, .lean_bool_to_int64 x1 => Bool.toInt64 x1
  -- NO usize: | _, .lean_bool_to_isize x1 => some (@Decidable.decide _ (Bool.toISize x1))
  | _, .lean_int8_dec_lt x1 x2 => @Decidable.decide _ (Int8.decLt x1 x2)
  | _, .lean_int64_dec_eq x1 x2 => @Decidable.decide _ (Int64.decEq x1 x2)
  | _, .lean_int64_dec_le x1 x2 => @Decidable.decide _ (Int64.decLe x1 x2)
  | _, .lean_bool_to_int32 x1 => Bool.toInt32 x1
  | _, .lean_int64_of_nat x1 => Int64.ofNat x1
  | _, .lean_int32_to_int8 x1 => Int32.toInt8 x1
  | _, .lean_int64_to_int_sint x1 => Int64.toInt x1
  | _, .lean_int32_add x1 x2 => Int32.add x1 x2
  -- NO usize: | _, .lean_isize_dec_lt x1 x2 => some (@Decidable.decide _ (ISize.decLt x1 x2))
  | _, .lean_int64_neg x1 => Int64.neg x1
  | _, .lean_int32_lor x1 x2 => Int32.lor x1 x2
  | _, .lean_int8_abs x1 => Int8.abs x1
  | _, .lean_int8_to_int32 x1 => Int8.toInt32 x1
  | _, .lean_int32_mod x1 x2 => Int32.mod x1 x2
  -- NO usize: | _, .lean_isize_neg x1 => some (@Decidable.decide _ (ISize.neg x1))
  | _, .lean_int32_to_int x1 => Int32.toInt x1
  | _, .lean_int64_add x1 x2 => Int64.add x1 x2
  | _, .lean_int8_sub x1 x2 => Int8.sub x1 x2
  | _, .lean_int32_to_int16 x1 => Int32.toInt16 x1
  | _, .lean_int8_to_int64 x1 => Int8.toInt64 x1
  | _, .lean_int16_lor x1 x2 => Int16.lor x1 x2
  | _, .lean_int64_div x1 x2 => Int64.div x1 x2
  -- NO usize: | _, .lean_int8_to_isize x1 => some (@Decidable.decide _ (Int8.toISize x1))
  -- NO usize: | _, .lean_isize_dec_eq x1 x2 => some (@Decidable.decide _ (ISize.decEq x1 x2))
  | _, .lean_int16_add x1 x2 => Int16.add x1 x2
  | _, .lean_int8_of_nat x1 => Int8.ofNat x1
  | _, .lean_int8_dec_le x1 x2 => @Decidable.decide _ (Int8.decLe x1 x2)
  | _, .lean_int16_to_int8 x1 => Int16.toInt8 x1
  | _, .lean_int8_to_int x1 => Int8.toInt x1
  | _, .lean_int8_mul x1 x2 => Int8.mul x1 x2
  | _, .lean_int16_neg x1 => Int16.neg x1
  | _, .lean_int64_to_int16 x1 => Int64.toInt16 x1
  | _, .lean_int8_land x1 x2 => Int8.land x1 x2
  | _, .lean_int32_div x1 x2 => Int32.div x1 x2
  | _, .lean_int8_of_int x1 => Int8.ofInt x1
  -- NO usize: | _, .lean_int16_to_isize x1 => some (@Decidable.decide _ (Int16.toISize x1))
  | _, .lean_int16_sub x1 x2 => Int16.sub x1 x2
  | _, .lean_int16_to_int64 x1 => Int16.toInt64 x1
  | _, .lean_int8_lor x1 x2 => Int8.lor x1 x2
  | _, .lean_int64_shift_right x1 x2 => Int64.shiftRight x1 x2
  | _, .lean_string_memcmp x1 x2 x3 x4 x5 x6 x7 => String.Slice.Pattern.Internal.memcmpStr x1 x2 x3 x4 x5 x6 x7
  | _, .lean_slice_dec_lt x1 x2 => @Decidable.decide _ (String.Slice.instDecidableLt x1 x2)
  | _, .lean_slice_hash x1 => String.Slice.hash x1
  | _, .lean_string_utf8_set__String_Pos_Raw_set x1 x2 x3 => String.Pos.Raw.set x1 x2 x3
  | _, .lean_string_utf8_set__String_Pos_set x1 x2 x3 => String.Pos.set x1 x2 x3
  | _, .lean_string_utf8_set__String_set x1 x2 x3 => String.set x1 x2 x3
  | _, .lean_float_frexp x1 => Float.frExp x1
  | _, .lean_uint8_to_float x1 => UInt8.toFloat x1
  | _, .lean_float_to_bits__Float_toModel x1 => Float.toModel x1
  | _, .lean_float_to_bits__Float_toBits x1 => Float.toBits x1
  | _, .lean_float_of_bits__Float_ofBits x1 => Float.ofBits x1
  | _, .lean_float_of_bits__Float_ofModel x1 => Float.ofModel x1
  | _, .lean_float_isnan x1 => Float.isNaN x1
  | _, .log10 x1 => Float.log10 x1
  | _, .cbrt x1 => Float.cbrt x1
  | _, .log x1 => Float.log x1
  | _, .lean_float_div x1 x2 => Float.div x1 x2
  | _, .lean_float_beq x1 x2 => Float.beq x1 x2
  | _, .tan x1 => Float.tan x1
  | _, .tanh x1 => Float.tanh x1
  | _, .exp2 x1 => Float.exp2 x1
  | _, .lean_float_to_uint16 x1 => Float.toUInt16 x1
  | _, .lean_uint32_to_float x1 => UInt32.toFloat x1
  | _, .lean_float_decLe__Float_decLe x1 x2 => @Decidable.decide _ (Float.decLe x1 x2)
  | _, .lean_float_decLe__Float_le x1 x2 => Float.le x1 x2
  | _, .lean_float_to_uint64 x1 => Float.toUInt64 x1
  | _, .sqrt x1 => Float.sqrt x1
  | _, .acos x1 => Float.acos x1
  | _, .atan x1 => Float.atan x1
  | _, .acosh x1 => Float.acosh x1
  | _, .floor x1 => Float.floor x1
  | _, .fabs x1 => Float.abs x1
  | _, .lean_float_to_uint32 x1 => Float.toUInt32 x1
  | _, .lean_float_to_string x1 => Float.toString x1
  | _, .lean_uint64_to_float x1 => UInt64.toFloat x1
  | _, .lean_float_decLt__Float_decLt x1 x2 => @Decidable.decide _ (Float.decLt x1 x2)
  | _, .lean_float_decLt__Float_lt x1 x2 => Float.lt x1 x2
  | _, .lean_float_to_uint8 x1 => Float.toUInt8 x1
  | _, .sin x1 => Float.sin x1
  -- NO usize: | _, .lean_usize_to_float x1 => some (@Decidable.decide _ (USize.toFloat x1))
  | _, .cosh x1 => Float.cosh x1
  | _, .exp x1 => Float.exp x1
  | _, .ceil x1 => Float.ceil x1
  -- NO usize: | _, .lean_float_to_usize x1 => some (@Decidable.decide _ (Float.toUSize x1))
  | _, .lean_float_isfinite x1 => Float.isFinite x1
  | _, .round x1 => Float.round x1
  | _, .cos x1 => Float.cos x1
  | _, .log2 x1 => Float.log2 x1
  | _, .atanh x1 => Float.atanh x1
  | _, .atan2 x1 x2 => Float.atan2 x1 x2
  | _, .sinh x1 => Float.sinh x1
  | _, .asinh x1 => Float.asinh x1
  | _, .lean_float_mul x1 x2 => Float.mul x1 x2
  | _, .lean_uint16_to_float x1 => UInt16.toFloat x1
  | _, .asin x1 => Float.asin x1
  | _, .pow x1 x2 => Float.pow x1 x2
  | _, .lean_float_scaleb x1 x2 => Float.scaleB x1 x2
  | _, .lean_float_add x1 x2 => Float.add x1 x2
  | _, .lean_float_sub x1 x2 => Float.sub x1 x2
  | _, .lean_float_negate x1 => Float.neg x1
  | _, .lean_float_isinf x1 => Float.isInf x1
  -- a byte or float array: | _, .lean_mk_empty_float_array x1 => FloatArray.emptyWithCapacity x1
  -- a byte or float array: | _, .lean_float_array_get x1 x2 => FloatArray.get! x1 x2
  -- a byte or float array: | _, .lean_float_array_uget x1 x2 x3 => FloatArray.uget x1 x2 x3
  -- a byte or float array: | _, .lean_float_array_fset x1 x2 x3 x4 => FloatArray.set x1 x2 x3 x4
  -- a byte or float array: | _, .lean_float_array_uset x1 x2 x3 x4 => FloatArray.uset x1 x2 x3 x4
  -- a byte or float array: | _, .lean_float_array_fget x1 x2 x3 => FloatArray.get x1 x2 x3
  -- a byte or float array: | _, .lean_float_array_set x1 x2 x3 => FloatArray.set! x1 x2 x3
  -- a byte or float array: | _, .lean_float_array_data x1 => FloatArray.data x1
  -- NO usize: | _, .lean_sarray_size__FloatArray_usize x1 => some (@Decidable.decide _ (FloatArray.usize x1))
  -- a byte or float array: | _, .lean_float_array_mk x1 => FloatArray.mk x1
  -- a byte or float array: | _, .lean_float_array_size x1 => FloatArray.size x1
  -- a byte or float array: | _, .lean_float_array_push x1 x2 => FloatArray.push x1 x2
  -- NO usize: | _, .lean_usize_log2 x1 => some (@Decidable.decide _ (USize.log2 x1))
  | _, .lean_uint16_log2 x1 => UInt16.log2 x1
  | _, .lean_uint64_log2 x1 => UInt64.log2 x1
  | _, .lean_uint8_log2 x1 => UInt8.log2 x1
  | _, .lean_uint32_log2 x1 => UInt32.log2 x1
  | _, .lean_int32_to_float x1 => Int32.toFloat x1
  | _, .lean_float_to_int16 x1 => Float.toInt16 x1
  | _, .lean_int16_to_float x1 => Int16.toFloat x1
  | _, .lean_float_to_int32 x1 => Float.toInt32 x1
  -- NO usize: | _, .lean_isize_to_float x1 => some (@Decidable.decide _ (ISize.toFloat x1))
  | _, .lean_int8_to_float x1 => Int8.toFloat x1
  | _, .lean_float_to_int8 x1 => Float.toInt8 x1
  | _, .lean_int64_to_float x1 => Int64.toFloat x1
  | _, .lean_float_to_int64 x1 => Float.toInt64 x1
  -- NO usize: | _, .lean_float_to_isize x1 => some (@Decidable.decide _ (Float.toISize x1))
  | _, .tanhf x1 => Float32.tanh x1
  | _, .exp2f x1 => Float32.exp2 x1
  | _, .lean_float32_div x1 x2 => Float32.div x1 x2
  | _, .logf x1 => Float32.log x1
  | _, .lean_float32_decLe__Float32_le x1 x2 => Float32.le x1 x2
  | _, .lean_float32_decLe__Float32_decLe x1 x2 => @Decidable.decide _ (Float32.decLe x1 x2)
  | _, .lean_float_to_float32 x1 => Float.toFloat32 x1
  | _, .lean_float32_to_bits__Float32_toModel x1 => Float32.toModel x1
  | _, .lean_float32_to_bits__Float32_toBits x1 => Float32.toBits x1
  | _, .lean_float32_of_bits__Float32_ofBits x1 => Float32.ofBits x1
  | _, .lean_float32_of_bits__Float32_ofModel x1 => Float32.ofModel x1
  | _, .atanf x1 => Float32.atan x1
  | _, .acoshf x1 => Float32.acosh x1
  | _, .lean_float32_frexp x1 => Float32.frExp x1
  | _, .lean_float32_to_uint64 x1 => Float32.toUInt64 x1
  | _, .lean_float32_sub x1 x2 => Float32.sub x1 x2
  | _, .lean_float32_to_uint16 x1 => Float32.toUInt16 x1
  -- NO usize: | _, .lean_usize_to_float32 x1 => some (@Decidable.decide _ (USize.toFloat32 x1))
  | _, .asinf x1 => Float32.asin x1
  | _, .powf x1 x2 => Float32.pow x1 x2
  | _, .lean_float32_beq x1 x2 => Float32.beq x1 x2
  | _, .lean_uint8_to_float32 x1 => UInt8.toFloat32 x1
  | _, .tanf x1 => Float32.tan x1
  | _, .lean_float32_to_float x1 => Float32.toFloat x1
  | _, .lean_float32_isnan x1 => Float32.isNaN x1
  | _, .log10f x1 => Float32.log10 x1
  | _, .cbrtf x1 => Float32.cbrt x1
  | _, .atan2f x1 x2 => Float32.atan2 x1 x2
  | _, .sinhf x1 => Float32.sinh x1
  | _, .cosf x1 => Float32.cos x1
  | _, .lean_uint32_to_float32 x1 => UInt32.toFloat32 x1
  | _, .lean_float32_isinf x1 => Float32.isInf x1
  | _, .lean_float32_negate x1 => Float32.neg x1
  -- NO usize: | _, .lean_float32_to_usize x1 => some (@Decidable.decide _ (Float32.toUSize x1))
  | _, .ceilf x1 => Float32.ceil x1
  | _, .lean_float32_isfinite x1 => Float32.isFinite x1
  | _, .lean_float32_add x1 x2 => Float32.add x1 x2
  | _, .lean_float32_scaleb x1 x2 => Float32.scaleB x1 x2
  | _, .sinf x1 => Float32.sin x1
  | _, .lean_float32_mul x1 x2 => Float32.mul x1 x2
  | _, .lean_float32_to_string x1 => Float32.toString x1
  | _, .asinhf x1 => Float32.asinh x1
  | _, .lean_float32_to_uint32 x1 => Float32.toUInt32 x1
  | _, .log2f x1 => Float32.log2 x1
  | _, .lean_uint64_to_float32 x1 => UInt64.toFloat32 x1
  | _, .atanhf x1 => Float32.atanh x1
  | _, .floorf x1 => Float32.floor x1
  | _, .fabsf x1 => Float32.abs x1
  | _, .roundf x1 => Float32.round x1
  | _, .lean_float32_decLt__Float32_lt x1 x2 => Float32.lt x1 x2
  | _, .lean_float32_decLt__Float32_decLt x1 x2 => @Decidable.decide _ (Float32.decLt x1 x2)
  | _, .acosf x1 => Float32.acos x1
  | _, .sqrtf x1 => Float32.sqrt x1
  | _, .lean_uint16_to_float32 x1 => UInt16.toFloat32 x1
  | _, .coshf x1 => Float32.cosh x1
  | _, .expf x1 => Float32.exp x1
  | _, .lean_float32_to_uint8 x1 => Float32.toUInt8 x1
  | _, .lean_float32_to_int64 x1 => Float32.toInt64 x1
  -- NO usize: | _, .lean_float32_to_isize x1 => some (@Decidable.decide _ (Float32.toISize x1))
  | _, .lean_int32_to_float32 x1 => Int32.toFloat32 x1
  | _, .lean_float32_to_int8 x1 => Float32.toInt8 x1
  | _, .lean_float32_to_int16 x1 => Float32.toInt16 x1
  -- NO usize: | _, .lean_isize_to_float32 x1 => some (@Decidable.decide _ (ISize.toFloat32 x1))
  | _, .lean_int8_to_float32 x1 => Int8.toFloat32 x1
  | _, .lean_float32_to_int32 x1 => Float32.toInt32 x1
  | _, .lean_int16_to_float32 x1 => Int16.toFloat32 x1
  | _, .lean_int64_to_float32 x1 => Int64.toFloat32 x1
  | _, .lean_string_compare x1 x2 => String.compare x1 x2
  -- NO handle: | _, .lean_io_process_child_pid x1 => IO.Process.Child.pid x1
  -- NO handle: | _, .lean_io_promise_result_opt _ x2 => some (@Decidable.decide _ (IO.Promise.result? x2))
  -- NO private: _, .lean_option_get_or_block x1 x2 => some (_private.Init.System.Promise.0.IO.Option.getOrBlock! x2)
  -- NO handle: | _, .lean_sharecommon_quick _ x2 => ShareCommon.shareCommon' x2
  -- NO handle: | _, .lean_state_sharecommon _ x2 x3 => ShareCommon.State.shareCommon x2 x3
  -- NO unsafe:| _, .lean_sharecommon_eq x1 x2 => some (ShareCommon.Object.eq x1 x2)
  -- NO unsafe:| _, .lean_sharecommon_hash x1 => some (ShareCommon.Object.hash x1)

/-! ## The table runs

The answers are ascribed: `ETy.denote ↑LeanPrimTy.nat` *is* `Nat`, but only once the
`Coe` instance and `ETy.denote` are unfolded, which the elaborator does not do while it
is looking for an `OfNat` instance. -/

example : EExtern.eval (.lean_nat_add 2 3) = (5 : Nat) := by rfl
example : EExtern.eval (.lean_nat_sub 3 10) = (0 : Nat) := by rfl
example : EExtern.eval (.lean_nat_mul 6 7) = (42 : Nat) := by rfl
example : EExtern.eval (.lean_nat_dec_lt 2 3) = true := by rfl
example : EExtern.eval (.lean_nat_dec_lt 3 3) = false := by rfl
example :
    EExtern.eval (.lean_string_append__String_append "ab" "cd") = ("abcd" : String) := by rfl
example :
    EExtern.eval (.lean_array_push (ETy.prim .nat) (#[1, 2] : Array Nat) 3)
      = (#[1, 2, 3] : Array Nat) := by rfl
example :
    EExtern.eval (.lean_array_to_list (ETy.prim .nat) (#[1, 2] : Array Nat))
      = ([1, 2] : List Nat) := by rfl
example : EExtern.eval (.lean_int_neg 7) = (-7 : Int) := by rfl
-- an entry that carries its own `Inhabited` default: the index is in range here, and
-- out of range it answers with the default the entry carries
example :
    EExtern.eval (.lean_array_get_borrowed (ETy.prim .nat) 0 (#[7, 8] : Array Nat) 1)
      = (8 : Nat) := by rfl
example :
    EExtern.eval (.lean_array_get_borrowed (ETy.prim .nat) 99 (#[7, 8] : Array Nat) 5)
      = (99 : Nat) := by rfl
-- a delayed value denotes the value itself
example : EExtern.eval (.lean_thunk_pure (ETy.prim .nat) 3) = (3 : Nat) := by rfl
-- the facts about the host are fixed, so that a compiled program does not depend on the
-- machine it was compiled on
example : EExtern.eval .lean_system_platform_target = ("nodeorbrowser" : String) := by rfl
example : EExtern.eval .lean_version_get_major = (0 : Nat) := by rfl

end LeanScript

end

/-!
## The earlier version of this file

What was here before targeted a shape the catalogue no longer has: four *families*
`LeanInitPureExtern_T_T`, `LeanInitPureExtern_U_T`, … indexed by the arity and kind of
the entry, and a `LeanScript.ExternEval` module.  Neither exists in this tree —
`LeanScript.LeanInitPureExterns` is one inductive — and most of its lines were the
placeholder `...nothing`.  It is preserved below rather than deleted.
-/

/-
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

-/
