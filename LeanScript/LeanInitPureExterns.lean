module
prelude
public import LeanScript.LeanPrimTy
public import LeanScript.LeanPrimTyCovariant
set_option autoImplicit false
@[expose] public section
namespace LeanScript

open LeanPrimTy
open LeanPrimTyCovariant

protected abbrev LeanPrimTy.usize : LeanPrimTy := uint64
protected abbrev LeanPrimTy.LeanPrimTy.isize : LeanPrimTy := int64

/-!
# The catalogue of the pure `@[extern]` functions of Lean's `Init`

Every entry of the *terminal* families (`LeanInitPureExtern_U_T`,
`LeanInitPureExtern_T_T`, `LeanInitPureExtern_T_T_T`,
`LeanInitPureExtern_T_T_T_T`, `LeanInitPureExtern_T_T_T_T_T`) that is listed here has a
meaning as a **total** Lean function of the values of its arguments
(`LeanScript.ExternEval1`, `LeanScript.ExternEval2`, `LeanScript.ExternEvalMisc`), so the
evaluator of `LeanScript.Eval` can always run it.  The entries that had no such meaning
are commented out rather than deleted, each marked with the reason:

* `(†)` — **the entry's type is not the type its name says.**  `byteArray`,
  `floatArray`, `ordering` and `name` are not constructors of `LeanPrimTy` (a byte
  array is `Array UInt8` at this layer, an `Ordering` is an enum, a `Name` is an
  inductive), so with `autoImplicit` on they were silently read as *type variables*:
  `lean_byte_array_size` had type `LeanInitPureExtern_T_T ?α .nat` for every
  terminal `?α`, i.e. "the size of a `Nat`, of a `Float`, of anything at all".  Such an
  entry denotes no function of its argument's value.  `set_option autoImplicit false`
  above is what keeps them from coming back.  They belong in the polymorphic families,
  where `byteArray` and `floatArray` are genuine parameters (`Extern3At`, `Extern6At`);
  moving them there is a change to the catalogue *and* to every instantiation of it.
* `(‡)` — **the answer is a fact about the machine the compiled program runs on**, not a
  function of any value: the version of the toolchain, the platform, the width of a
  word, the number of cores.  Reading it off the machine that runs the *compiler* would
  bake the wrong answer into the semantics.  They come back as soon as the backend has a
  target description to read them from; until then `LeanInitPureExtern_U_T` is empty, and
  `LeanInitPureExtern_U_T.eval` is total for the vacuous reason.

* `(§)` — **a second name for an entry that is already here.**  `Float.toModel` and
  `Float.toBits` are compiled to the *same* C function (`lean_float_to_bits`), and so
  are `Float.ofModel`/`Float.ofBits` and their `Float32` counterparts; what `toModel`
  answers with is `Float.Model`, the abstract model of a float, which is not a terminal
  type of this language (and is not a type of the current toolchain at all).  At the
  type written here they were a duplicate of `lean_float_to_bits`, so the language would
  have had two names for one function, only one of which was the function its name says.
  Use `lean_float_to_bits`, `lean_float_of_bits`, `lean_float32_to_bits` and
  `lean_float32_of_bits`, which are entries of this family and do run.
-/

/-- The constants of the runtime.  **Empty**: every entry is a fact about the target
    machine, see `(‡)` above. -/
inductive LeanInitPureExtern_U_T : LeanPrimTy → Type where
  | lean_version_get_special_desc          : LeanInitPureExtern_U_T .string -- always "leanscript"
  | lean_version_get_is_release            : LeanInitPureExtern_U_T .bool -- always false
  | lean_version_get_major                 : LeanInitPureExtern_U_T .nat -- always 0
  | lean_version_get_patch                 : LeanInitPureExtern_U_T .nat -- always 0
  | lean_internal_is_stage0                : LeanInitPureExtern_U_T .bool -- always false
  | lean_version_get_minor                 : LeanInitPureExtern_U_T .nat -- always 0
  | lean_get_githash                       : LeanInitPureExtern_U_T .string -- always "leanscript"
  | lean_internal_has_llvm_backend         : LeanInitPureExtern_U_T .bool -- always false
  | lean_system_platform_emscripten        : LeanInitPureExtern_U_T .bool -- always false
  | lean_system_platform_target            : LeanInitPureExtern_U_T .string -- always "nodeorbrowser"
  -- can:
  -- 1. `/^win/i.test(globalThis.process?.platform || globalThis.Deno?.build?.os || globalThis.navigator?.userAgentData?.platform || globalThis.navigator?.platform || '') || /windows/i.test(globalThis.navigator?.userAgent || '')`
  -- 2. `/^(darwin|macos)$/i.test(globalThis.process?.platform || globalThis.Deno?.build?.os || globalThis.navigator?.userAgentData?.platform || '') || /mac/i.test(globalThis.navigator?.platform || globalThis.navigator?.userAgent || '')`
  -- 3. etc linux
  -- 4. bits `/64/.test(globalThis.process?.arch ?? '') || /x86_64|Win64|WOW64|arm64/i.test(globalThis.navigator?.userAgent ?? '') ? 64 : 32`
  -- but I want all lazy be optimizable too, so dont want to support
  -- (‡) | lean_system_platform_nbits             : LeanInitPureExtern_U_T .nat
  -- (‡) | lean_system_platform_windows           : LeanInitPureExtern_U_T .bool
  -- (‡) | lean_system_platform_osx               : LeanInitPureExtern_U_T .bool
  -- (‡) | lean_system_platform_linux             : LeanInitPureExtern_U_T .bool -- no support bc IO
  -- (‡) | lean_internal_get_hardware_concurrency : LeanInitPureExtern_U_T .uint32 -- always 0

inductive LeanInitPureExtern_T_T_T_P_T : LeanPrimTy → Prop → LeanPrimTy → Type where
  | uint32_of_nat__UInt32_ofNatLT : (n : Nat) → UInt32 → LeanInitPureExtern_T_T_T_P_T nat (LT.lt n UInt32.size) uint32
  | uint32_of_nat__Char_ofNatAux : (n : Nat) → Char → LeanInitPureExtern_T_T_T_P_T nat n.isValidChar char

--   | lean_uint32_of_nat                | def 🌌         | UInt32.ofNatLT              | (n : @& Nat) → instLTNat.lt n UInt32.size → UInt32                         |
-- |                                   |               | Char.ofNatAux               | (n : @& Nat) → n.isValidChar → Char                                        |
-- | lean_uint32_of_nat    | def | UInt32.ofNat      | (@& Nat) → UInt32                                          |


inductive LeanInitPureExtern_T_T : LeanPrimTy → LeanPrimTy → Type where
  | uint32_of_nat__UInt32_ofNat : (n : Nat) → UInt32 → LeanInitPureExtern_T_T nat uint32
  -- (†) | lean_byte_array_size            : LeanInitPureExtern_T_T byteArray nat
  -- (†) | lean_string_to_utf8             : LeanInitPureExtern_T_T string byteArray
  | lean_uint32_of_nat_lt           : LeanInitPureExtern_T_T nat uint32
  | lean_char_of_nat_aux            : LeanInitPureExtern_T_T nat char
  | lean_uint8_to_bitvec            : LeanInitPureExtern_T_T uint8 (bitvec 8)
  -- (†) | lean_string_from_utf8_unchecked : LeanInitPureExtern_T_T byteArray string
  | lean_uint8_of_nat               : LeanInitPureExtern_T_T nat uint8
  | lean_uint8_of_nat_lt            : LeanInitPureExtern_T_T nat uint8
  | lean_uint16_to_bitvec           : LeanInitPureExtern_T_T uint16 (bitvec 16)
  | lean_uint16_of_nat_mk           : LeanInitPureExtern_T_T (bitvec 16) uint16
  | lean_nat_pred                   : LeanInitPureExtern_T_T nat nat
  | lean_usize_of_nat_lt            : LeanInitPureExtern_T_T nat LeanPrimTy.usize
  | lean_string_hash                : LeanInitPureExtern_T_T string uint64
  | lean_uint64_to_bitvec           : LeanInitPureExtern_T_T uint64 (bitvec 64)
  | lean_uint64_of_nat_mk           : LeanInitPureExtern_T_T (bitvec 64) uint64
  | lean_uint32_to_nat              : LeanInitPureExtern_T_T uint32 nat
  | lean_uint32_to_bitvec           : LeanInitPureExtern_T_T uint32 (bitvec 32)
  | lean_uint16_of_nat_lt           : LeanInitPureExtern_T_T nat uint16
  | lean_uint8_of_nat_mk            : LeanInitPureExtern_T_T (bitvec 8) uint8
  -- (†) | lean_mk_empty_byte_array        : LeanInitPureExtern_T_T nat byteArray
  | lean_usize_of_nat_mk            : LeanInitPureExtern_T_T (bitvec 64) LeanPrimTy.usize
  | lean_usize_to_bitvec            : LeanInitPureExtern_T_T LeanPrimTy.usize (bitvec 64)
  | lean_string_utf8_byte_size      : LeanInitPureExtern_T_T string nat
  | lean_uint64_of_nat_lt           : LeanInitPureExtern_T_T nat uint64
  | lean_nat_to_int                 : LeanInitPureExtern_T_T nat int
  | lean_int_to_nat                 : LeanInitPureExtern_T_T int nat
  | lean_int_dec_nonneg             : LeanInitPureExtern_T_T int bool
  | lean_int_neg_succ_of_nat        : LeanInitPureExtern_T_T nat int
  | lean_int_neg                    : LeanInitPureExtern_T_T int int
  | lean_nat_abs                    : LeanInitPureExtern_T_T int nat
  | lean_uint64_to_nat              : LeanInitPureExtern_T_T uint64 nat
  | lean_uint32_to_uint8            : LeanInitPureExtern_T_T uint32 uint8
  | lean_usize_to_nat               : LeanInitPureExtern_T_T LeanPrimTy.usize nat
  | lean_uint64_to_uint32           : LeanInitPureExtern_T_T uint64 uint32
  | lean_uint32_to_uint16           : LeanInitPureExtern_T_T uint32 uint16
  | lean_uint16_to_uint32           : LeanInitPureExtern_T_T uint16 uint32
  | lean_uint32_to_uint64           : LeanInitPureExtern_T_T uint32 uint64
  | lean_uint32_of_nat              : LeanInitPureExtern_T_T nat uint32
  | lean_uint16_to_nat              : LeanInitPureExtern_T_T uint16 nat
  | lean_uint16_to_uint8            : LeanInitPureExtern_T_T uint16 uint8
  | lean_usize_of_nat               : LeanInitPureExtern_T_T nat LeanPrimTy.usize
  | lean_uint8_to_uint64            : LeanInitPureExtern_T_T uint8 uint64
  | lean_uint8_to_nat               : LeanInitPureExtern_T_T uint8 nat
  | lean_uint64_of_nat              : LeanInitPureExtern_T_T nat uint64
  | lean_uint8_to_uint32            : LeanInitPureExtern_T_T uint8 uint32
  | lean_uint16_of_nat              : LeanInitPureExtern_T_T nat uint16
  | lean_uint16_to_uint64           : LeanInitPureExtern_T_T uint16 uint64
  | lean_uint64_to_uint8            : LeanInitPureExtern_T_T uint64 uint8
  | lean_uint64_to_uint16           : LeanInitPureExtern_T_T uint64 uint16
  | lean_uint8_to_uint16            : LeanInitPureExtern_T_T uint8 uint16
  | lean_string_trim                : LeanInitPureExtern_T_T string string
  | lean_substring_tostring         : LeanInitPureExtern_T_T substring string
  | lean_string_isempty             : LeanInitPureExtern_T_T string bool
  | lean_string_front               : LeanInitPureExtern_T_T string char
  | lean_string_length              : LeanInitPureExtern_T_T string nat
  | lean_string_capitalize          : LeanInitPureExtern_T_T string string
  | lean_substring_front            : LeanInitPureExtern_T_T substring char
  | lean_substring_isempty          : LeanInitPureExtern_T_T substring bool
  | lean_string_of_usize            : LeanInitPureExtern_T_T LeanPrimTy.usize string
  | lean_nat_log2                   : LeanInitPureExtern_T_T nat nat
  | lean_uint16_neg                 : LeanInitPureExtern_T_T uint16 uint16
  | lean_uint16_to_usize            : LeanInitPureExtern_T_T uint16 LeanPrimTy.usize
  | lean_uint64_complement          : LeanInitPureExtern_T_T uint64 uint64
  | lean_bool_to_uint32             : LeanInitPureExtern_T_T bool uint32
  | lean_uint8_neg                  : LeanInitPureExtern_T_T uint8 uint8
  | lean_uint16_complement          : LeanInitPureExtern_T_T uint16 uint16
  | lean_uint32_neg                 : LeanInitPureExtern_T_T uint32 uint32
  | lean_usize_neg                  : LeanInitPureExtern_T_T LeanPrimTy.usize LeanPrimTy.usize
  | lean_usize_to_uint64            : LeanInitPureExtern_T_T LeanPrimTy.usize uint64
  | lean_bool_to_uint64             : LeanInitPureExtern_T_T bool uint64
  | lean_usize_of_nat32             : LeanInitPureExtern_T_T nat LeanPrimTy.usize
  | lean_uint64_neg                 : LeanInitPureExtern_T_T uint64 uint64
  | lean_uint32_to_usize            : LeanInitPureExtern_T_T uint32 LeanPrimTy.usize
  | lean_uint8_complement           : LeanInitPureExtern_T_T uint8 uint8
  | lean_usize_to_uint16            : LeanInitPureExtern_T_T LeanPrimTy.usize uint16
  | lean_usize_to_uint8             : LeanInitPureExtern_T_T LeanPrimTy.usize uint8
  | lean_bool_to_uint8              : LeanInitPureExtern_T_T bool uint8
  | lean_uint32_complement          : LeanInitPureExtern_T_T uint32 uint32
  | lean_uint8_to_usize             : LeanInitPureExtern_T_T uint8 LeanPrimTy.usize
  | lean_bool_to_uint16             : LeanInitPureExtern_T_T bool uint16
  | lean_bool_to_usize              : LeanInitPureExtern_T_T bool LeanPrimTy.usize
  | lean_uint64_to_usize            : LeanInitPureExtern_T_T uint64 LeanPrimTy.usize
  | lean_usize_to_uint32            : LeanInitPureExtern_T_T LeanPrimTy.usize uint32
  | lean_usize_complement           : LeanInitPureExtern_T_T LeanPrimTy.usize LeanPrimTy.usize
  -- (†) | lean_byte_array_hash            : LeanInitPureExtern_T_T byteArray uint64
  -- (†) | lean_sarray_size                : LeanInitPureExtern_T_T byteArray LeanPrimTy.usize
  -- (†) | lean_string_to_utf8_defs        : LeanInitPureExtern_T_T string byteArray
  -- (†) | lean_string_validate_utf8       : LeanInitPureExtern_T_T byteArray bool
  | lean_string_length_def          : LeanInitPureExtern_T_T string nat
  | lean_isize_complement           : LeanInitPureExtern_T_T LeanPrimTy.isize LeanPrimTy.isize
  | lean_int16_of_nat               : LeanInitPureExtern_T_T nat int16
  | lean_int32_of_int               : LeanInitPureExtern_T_T int int32
  | lean_int64_to_isize             : LeanInitPureExtern_T_T int64 LeanPrimTy.isize
  | lean_isize_to_int8              : LeanInitPureExtern_T_T LeanPrimTy.isize int8
  | lean_int32_of_nat               : LeanInitPureExtern_T_T nat int32
  | lean_int64_to_int8              : LeanInitPureExtern_T_T int64 int8
  | lean_int32_to_int64             : LeanInitPureExtern_T_T int32 int64
  | lean_int8_to_int16              : LeanInitPureExtern_T_T int8 int16
  | lean_int64_of_int               : LeanInitPureExtern_T_T int int64
  | lean_int32_to_isize             : LeanInitPureExtern_T_T int32 LeanPrimTy.isize
  | lean_int32_neg                  : LeanInitPureExtern_T_T int32 int32
  | lean_int32_abs                  : LeanInitPureExtern_T_T int32 int32
  | lean_bool_to_int8               : LeanInitPureExtern_T_T bool int8
  | lean_isize_to_int16             : LeanInitPureExtern_T_T LeanPrimTy.isize int16
  | lean_int16_to_int               : LeanInitPureExtern_T_T int16 int
  | lean_int8_complement            : LeanInitPureExtern_T_T int8 int8
  | lean_bool_to_int16              : LeanInitPureExtern_T_T bool int16
  | lean_isize_of_int               : LeanInitPureExtern_T_T int LeanPrimTy.isize
  | lean_int16_abs                  : LeanInitPureExtern_T_T int16 int16
  | lean_int16_to_int32             : LeanInitPureExtern_T_T int16 int32
  | lean_isize_to_int               : LeanInitPureExtern_T_T LeanPrimTy.isize int
  | lean_isize_of_nat               : LeanInitPureExtern_T_T nat LeanPrimTy.isize
  | lean_int16_complement           : LeanInitPureExtern_T_T int16 int16
  | lean_isize_to_int64             : LeanInitPureExtern_T_T LeanPrimTy.isize int64
  | lean_int64_complement           : LeanInitPureExtern_T_T int64 int64
  | lean_isize_abs                  : LeanInitPureExtern_T_T LeanPrimTy.isize LeanPrimTy.isize
  | lean_int16_of_int               : LeanInitPureExtern_T_T int int16
  | lean_int8_neg                   : LeanInitPureExtern_T_T int8 int8
  | lean_isize_to_int32             : LeanInitPureExtern_T_T LeanPrimTy.isize int32
  | lean_int64_to_int32             : LeanInitPureExtern_T_T int64 int32
  | lean_int64_abs                  : LeanInitPureExtern_T_T int64 int64
  | lean_int32_complement           : LeanInitPureExtern_T_T int32 int32
  | lean_bool_to_int64              : LeanInitPureExtern_T_T bool int64
  | lean_bool_to_isize              : LeanInitPureExtern_T_T bool LeanPrimTy.isize
  | lean_bool_to_int32              : LeanInitPureExtern_T_T bool int32
  | lean_int64_of_nat               : LeanInitPureExtern_T_T nat int64
  | lean_int32_to_int8              : LeanInitPureExtern_T_T int32 int8
  | lean_int64_to_int_sint          : LeanInitPureExtern_T_T int64 int
  | lean_int64_neg                  : LeanInitPureExtern_T_T int64 int64
  | lean_int8_abs                   : LeanInitPureExtern_T_T int8 int8
  | lean_int8_to_int32              : LeanInitPureExtern_T_T int8 int32
  | lean_isize_neg                  : LeanInitPureExtern_T_T LeanPrimTy.isize LeanPrimTy.isize
  | lean_int32_to_int               : LeanInitPureExtern_T_T int32 int
  | lean_int32_to_int16             : LeanInitPureExtern_T_T int32 int16
  | lean_int8_to_int64              : LeanInitPureExtern_T_T int8 int64
  | lean_int8_to_isize              : LeanInitPureExtern_T_T int8 LeanPrimTy.isize
  | lean_int8_of_nat                : LeanInitPureExtern_T_T nat int8
  | lean_int16_to_int8              : LeanInitPureExtern_T_T int16 int8
  | lean_int8_to_int                : LeanInitPureExtern_T_T int8 int
  | lean_int16_neg                  : LeanInitPureExtern_T_T int16 int16
  | lean_int64_to_int16             : LeanInitPureExtern_T_T int64 int16
  | lean_int8_of_int                : LeanInitPureExtern_T_T int int8
  | lean_int16_to_isize             : LeanInitPureExtern_T_T int16 LeanPrimTy.isize
  | lean_int16_to_int64             : LeanInitPureExtern_T_T int16 int64
  | lean_slice_hash                 : LeanInitPureExtern_T_T stringSlice uint64
  | lean_uint8_to_float             : LeanInitPureExtern_T_T uint8 float
  | lean_float_to_bits              : LeanInitPureExtern_T_T float uint64
  | lean_float_of_bits              : LeanInitPureExtern_T_T uint64 float
  | lean_float_isnan                : LeanInitPureExtern_T_T float bool
  | log10                           : LeanInitPureExtern_T_T float float
  | cbrt                            : LeanInitPureExtern_T_T float float
  | log                             : LeanInitPureExtern_T_T float float
  | tan                             : LeanInitPureExtern_T_T float float
  | tanh                            : LeanInitPureExtern_T_T float float
  | exp2                            : LeanInitPureExtern_T_T float float
  | lean_float_to_uint16            : LeanInitPureExtern_T_T float uint16
  | lean_uint32_to_float            : LeanInitPureExtern_T_T uint32 float
  | lean_float_to_uint64            : LeanInitPureExtern_T_T float uint64
  | sqrt                            : LeanInitPureExtern_T_T float float
  | acos                            : LeanInitPureExtern_T_T float float
  | atan                            : LeanInitPureExtern_T_T float float
  | acosh                           : LeanInitPureExtern_T_T float float
  | floor                           : LeanInitPureExtern_T_T float float
  | fabs                            : LeanInitPureExtern_T_T float float
  | lean_float_to_uint32            : LeanInitPureExtern_T_T float uint32
  | lean_float_to_string            : LeanInitPureExtern_T_T float string
  | lean_uint64_to_float            : LeanInitPureExtern_T_T uint64 float
  | lean_float_to_uint8             : LeanInitPureExtern_T_T float uint8
  | sin                             : LeanInitPureExtern_T_T float float
  | lean_usize_to_float             : LeanInitPureExtern_T_T LeanPrimTy.usize float
  | cosh                            : LeanInitPureExtern_T_T float float
  | exp                             : LeanInitPureExtern_T_T float float
  | ceil                            : LeanInitPureExtern_T_T float float
  | lean_float_to_usize             : LeanInitPureExtern_T_T float LeanPrimTy.usize
  | lean_float_isfinite             : LeanInitPureExtern_T_T float bool
  | round                           : LeanInitPureExtern_T_T float float
  | cos                             : LeanInitPureExtern_T_T float float
  | log2                            : LeanInitPureExtern_T_T float float
  | atanh                           : LeanInitPureExtern_T_T float float
  | sinh                            : LeanInitPureExtern_T_T float float
  | asinh                           : LeanInitPureExtern_T_T float float
  | lean_uint16_to_float            : LeanInitPureExtern_T_T uint16 float
  | asin                            : LeanInitPureExtern_T_T float float
  | lean_float_negate               : LeanInitPureExtern_T_T float float
  | lean_float_isinf                : LeanInitPureExtern_T_T float bool
  -- (†) | lean_mk_empty_float_array       : LeanInitPureExtern_T_T nat floatArray
  -- (†) | lean_float_array_usize          : LeanInitPureExtern_T_T floatArray LeanPrimTy.usize
  -- (†) | lean_float_array_size           : LeanInitPureExtern_T_T floatArray nat
  | lean_usize_log2                 : LeanInitPureExtern_T_T LeanPrimTy.usize LeanPrimTy.usize
  | lean_uint16_log2                : LeanInitPureExtern_T_T uint16 uint16
  | lean_uint64_log2                : LeanInitPureExtern_T_T uint64 uint64
  | lean_uint8_log2                 : LeanInitPureExtern_T_T uint8 uint8
  | lean_uint32_log2                : LeanInitPureExtern_T_T uint32 uint32
  | lean_int32_to_float             : LeanInitPureExtern_T_T int32 float
  | lean_float_to_int16             : LeanInitPureExtern_T_T float int16
  | lean_int16_to_float             : LeanInitPureExtern_T_T int16 float
  | lean_float_to_int32             : LeanInitPureExtern_T_T float int32
  | lean_isize_to_float             : LeanInitPureExtern_T_T LeanPrimTy.isize float
  | lean_int8_to_float              : LeanInitPureExtern_T_T int8 float
  | lean_float_to_int8              : LeanInitPureExtern_T_T float int8
  | lean_int64_to_float             : LeanInitPureExtern_T_T int64 float
  | lean_float_to_int64             : LeanInitPureExtern_T_T float int64
  | lean_float_to_isize             : LeanInitPureExtern_T_T float LeanPrimTy.isize
  | tanhf                           : LeanInitPureExtern_T_T float32 float32
  | exp2f                           : LeanInitPureExtern_T_T float32 float32
  | logf                            : LeanInitPureExtern_T_T float32 float32
  | lean_float_to_float32           : LeanInitPureExtern_T_T float float32
  | lean_float32_to_bits            : LeanInitPureExtern_T_T float32 uint32
  | lean_float32_of_bits            : LeanInitPureExtern_T_T uint32 float32
  | atanf                           : LeanInitPureExtern_T_T float32 float32
  | acoshf                          : LeanInitPureExtern_T_T float32 float32
  | lean_float32_to_uint64          : LeanInitPureExtern_T_T float32 uint64
  | lean_float32_to_uint16          : LeanInitPureExtern_T_T float32 uint16
  | lean_usize_to_float32           : LeanInitPureExtern_T_T LeanPrimTy.usize float32
  | asinf                           : LeanInitPureExtern_T_T float32 float32
  | lean_uint8_to_float32           : LeanInitPureExtern_T_T uint8 float32
  | tanf                            : LeanInitPureExtern_T_T float32 float32
  | lean_float32_to_float           : LeanInitPureExtern_T_T float32 float
  | lean_float32_isnan              : LeanInitPureExtern_T_T float32 bool
  | log10f                          : LeanInitPureExtern_T_T float32 float32
  | cbrtf                           : LeanInitPureExtern_T_T float32 float32
  | sinhf                           : LeanInitPureExtern_T_T float32 float32
  | cosf                            : LeanInitPureExtern_T_T float32 float32
  | lean_uint32_to_float32          : LeanInitPureExtern_T_T uint32 float32
  | lean_float32_isinf              : LeanInitPureExtern_T_T float32 bool
  | lean_float32_negate             : LeanInitPureExtern_T_T float32 float32
  | lean_float32_to_usize           : LeanInitPureExtern_T_T float32 LeanPrimTy.usize
  | ceilf                           : LeanInitPureExtern_T_T float32 float32
  | lean_float32_isfinite           : LeanInitPureExtern_T_T float32 bool
  | sinf                            : LeanInitPureExtern_T_T float32 float32
  | lean_float32_to_string          : LeanInitPureExtern_T_T float32 string
  | asinhf                          : LeanInitPureExtern_T_T float32 float32
  | lean_float32_to_uint32          : LeanInitPureExtern_T_T float32 uint32
  | log2f                           : LeanInitPureExtern_T_T float32 float32
  | lean_uint64_to_float32          : LeanInitPureExtern_T_T uint64 float32
  | atanhf                          : LeanInitPureExtern_T_T float32 float32
  | floorf                          : LeanInitPureExtern_T_T float32 float32
  | fabsf                           : LeanInitPureExtern_T_T float32 float32
  | roundf                          : LeanInitPureExtern_T_T float32 float32
  | acosf                           : LeanInitPureExtern_T_T float32 float32
  | sqrtf                           : LeanInitPureExtern_T_T float32 float32
  | lean_uint16_to_float32          : LeanInitPureExtern_T_T uint16 float32
  | coshf                           : LeanInitPureExtern_T_T float32 float32
  | expf                            : LeanInitPureExtern_T_T float32 float32
  | lean_float32_to_uint8           : LeanInitPureExtern_T_T float32 uint8
  | lean_float32_to_int64           : LeanInitPureExtern_T_T float32 int64
  | lean_float32_to_isize           : LeanInitPureExtern_T_T float32 LeanPrimTy.isize
  | lean_int32_to_float32           : LeanInitPureExtern_T_T int32 float32
  | lean_float32_to_int8            : LeanInitPureExtern_T_T float32 int8
  | lean_float32_to_int16           : LeanInitPureExtern_T_T float32 int16
  | lean_isize_to_float32           : LeanInitPureExtern_T_T LeanPrimTy.isize float32
  | lean_int8_to_float32            : LeanInitPureExtern_T_T int8 float32
  | lean_float32_to_int32           : LeanInitPureExtern_T_T float32 int32
  | lean_int16_to_float32           : LeanInitPureExtern_T_T int16 float32
  | lean_int64_to_float32           : LeanInitPureExtern_T_T int64 float32
  -- | lean_io_process_child_pid       : LeanInitPureExtern_T_T childProcess uint32
  -- Commented out with the `childProcess` handle it reads.
  -- | lean_sharecommon_hash           : LeanInitPureExtern_T_T shareCommonObject uint64
  -- Commented out with the `shareCommonObject` handle it reads: it hashes the *address*
  -- of an object, not its value, so it is not a function of its argument.
  -- (§) | lean_float_to_model             : LeanInitPureExtern_T_T float uint64
  -- (§) | lean_float_of_model             : LeanInitPureExtern_T_T uint64 float
  -- (§) | lean_float32_to_model           : LeanInitPureExtern_T_T float32 uint32
  -- (§) | lean_float32_of_model           : LeanInitPureExtern_T_T uint32 float32

inductive LeanInitPureExtern_T_T_T : LeanPrimTy → LeanPrimTy → LeanPrimTy → Type where
  | lean_uint32_dec_eq            : LeanInitPureExtern_T_T_T uint32 uint32 bool
  | lean_uint32_dec_lt            : LeanInitPureExtern_T_T_T uint32 uint32 bool
  | lean_nat_div                  : LeanInitPureExtern_T_T_T nat nat nat
  | lean_nat_dec_lt               : LeanInitPureExtern_T_T_T nat nat bool
  | lean_nat_mod_core             : LeanInitPureExtern_T_T_T nat nat nat
  | lean_nat_mod                  : LeanInitPureExtern_T_T_T nat nat nat
  | lean_nat_sub                  : LeanInitPureExtern_T_T_T nat nat nat
  | lean_uint8_dec_lt             : LeanInitPureExtern_T_T_T uint8 uint8 bool
  | lean_uint32_dec_le            : LeanInitPureExtern_T_T_T uint32 uint32 bool
  | lean_nat_dec_eq               : LeanInitPureExtern_T_T_T nat nat bool
  | lean_nat_beq                  : LeanInitPureExtern_T_T_T nat nat bool
  | lean_uint8_dec_le             : LeanInitPureExtern_T_T_T uint8 uint8 bool
  | lean_nat_ble                  : LeanInitPureExtern_T_T_T nat nat bool
  | lean_nat_dec_le               : LeanInitPureExtern_T_T_T nat nat bool
  | lean_nat_add                  : LeanInitPureExtern_T_T_T nat nat nat
  | lean_uint16_dec_eq            : LeanInitPureExtern_T_T_T uint16 uint16 bool
  | lean_string_dec_eq            : LeanInitPureExtern_T_T_T string string bool
  | lean_uint64_dec_eq            : LeanInitPureExtern_T_T_T uint64 uint64 bool
  -- (†) | lean_name_eq                  : LeanInitPureExtern_T_T_T name name bool
  | lean_uint8_dec_eq             : LeanInitPureExtern_T_T_T uint8 uint8 bool
  | lean_nat_pow                  : LeanInitPureExtern_T_T_T nat nat nat
  | lean_usize_dec_eq             : LeanInitPureExtern_T_T_T LeanPrimTy.usize LeanPrimTy.usize bool
  | lean_nat_mul                  : LeanInitPureExtern_T_T_T nat nat nat
  -- (†) | lean_byte_array_push          : LeanInitPureExtern_T_T_T byteArray uint8 byteArray
  | lean_uint64_mix_hash          : LeanInitPureExtern_T_T_T uint64 uint64 uint64
  | lean_int_dec_le               : LeanInitPureExtern_T_T_T int int bool
  | lean_int_dec_lt               : LeanInitPureExtern_T_T_T int int bool
  | lean_int_dec_eq               : LeanInitPureExtern_T_T_T int int bool
  | lean_int_mul                  : LeanInitPureExtern_T_T_T int int int
  | lean_int_add                  : LeanInitPureExtern_T_T_T int int int
  | lean_int_sub                  : LeanInitPureExtern_T_T_T int int int
  | lean_nat_div_exact            : LeanInitPureExtern_T_T_T nat nat nat
  | lean_nat_lxor                 : LeanInitPureExtern_T_T_T nat nat nat
  | lean_nat_shiftl               : LeanInitPureExtern_T_T_T nat nat nat
  | lean_nat_shiftr               : LeanInitPureExtern_T_T_T nat nat nat
  | lean_nat_land                 : LeanInitPureExtern_T_T_T nat nat nat
  | lean_nat_lor                  : LeanInitPureExtern_T_T_T nat nat nat
  | lean_usize_add                : LeanInitPureExtern_T_T_T LeanPrimTy.usize LeanPrimTy.usize LeanPrimTy.usize
  | lean_uint32_sub               : LeanInitPureExtern_T_T_T uint32 uint32 uint32
  | lean_usize_sub                : LeanInitPureExtern_T_T_T LeanPrimTy.usize LeanPrimTy.usize LeanPrimTy.usize
  | lean_uint32_add               : LeanInitPureExtern_T_T_T uint32 uint32 uint32
  | lean_usize_dec_le             : LeanInitPureExtern_T_T_T LeanPrimTy.usize LeanPrimTy.usize bool
  | lean_usize_dec_lt             : LeanInitPureExtern_T_T_T LeanPrimTy.usize LeanPrimTy.usize bool
  | lean_string_utf8_get          : LeanInitPureExtern_T_T_T string stringPos char
  | lean_substring_drop           : LeanInitPureExtern_T_T_T substring nat substring
  | lean_substring_prev           : LeanInitPureExtern_T_T_T substring stringPos stringPos
  | lean_string_append            : LeanInitPureExtern_T_T_T string string string
  | lean_string_get_byte_fast     : LeanInitPureExtern_T_T_T string nat uint8
  | lean_string_push              : LeanInitPureExtern_T_T_T string char string
  | lean_string_isprefixof        : LeanInitPureExtern_T_T_T string string bool
  | lean_string_dropright         : LeanInitPureExtern_T_T_T string nat string
  | lean_substring_get            : LeanInitPureExtern_T_T_T substring stringPos char
  | lean_string_contains          : LeanInitPureExtern_T_T_T string char bool
  | lean_string_posof             : LeanInitPureExtern_T_T_T string char stringPos
  | lean_string_drop              : LeanInitPureExtern_T_T_T string nat string
  | lean_string_utf8_at_end       : LeanInitPureExtern_T_T_T string stringPos bool
  | lean_substring_beq            : LeanInitPureExtern_T_T_T substring substring bool
  | lean_string_utf8_next         : LeanInitPureExtern_T_T_T string stringPos stringPos
  | lean_string_pos_min           : LeanInitPureExtern_T_T_T stringPos stringPos stringPos
  | lean_string_pos_sub           : LeanInitPureExtern_T_T_T stringPos stringPos stringPos
  | lean_string_offsetofpos       : LeanInitPureExtern_T_T_T string stringPos nat
  | lean_strict_or                : LeanInitPureExtern_T_T_T bool bool bool
  | lean_strict_and               : LeanInitPureExtern_T_T_T bool bool bool
  | lean_int_emod                 : LeanInitPureExtern_T_T_T int int int
  | lean_int_div_exact            : LeanInitPureExtern_T_T_T int int int
  | lean_int_mod                  : LeanInitPureExtern_T_T_T int int int
  | lean_int_ediv                 : LeanInitPureExtern_T_T_T int int int
  | lean_int_div                  : LeanInitPureExtern_T_T_T int int int
  -- | lean_nat_gcd                  : LeanInitPureExtern_T_T_T nat nat nat -- TODO: fromLean should ignore the `@[extern "lean_nat_gcd"]` attribute for `Nat.gcd` function and treat it as ordinary well-foundedly recursive function
  | lean_uint64_shift_left        : LeanInitPureExtern_T_T_T uint64 uint64 uint64
  | lean_uint32_mod               : LeanInitPureExtern_T_T_T uint32 uint32 uint32
  | lean_usize_land               : LeanInitPureExtern_T_T_T LeanPrimTy.usize LeanPrimTy.usize LeanPrimTy.usize
  | lean_usize_mul                : LeanInitPureExtern_T_T_T LeanPrimTy.usize LeanPrimTy.usize LeanPrimTy.usize
  | lean_uint64_shift_right       : LeanInitPureExtern_T_T_T uint64 uint64 uint64
  | lean_usize_shift_left         : LeanInitPureExtern_T_T_T LeanPrimTy.usize LeanPrimTy.usize LeanPrimTy.usize
  | lean_uint16_add               : LeanInitPureExtern_T_T_T uint16 uint16 uint16
  | lean_usize_xor                : LeanInitPureExtern_T_T_T LeanPrimTy.usize LeanPrimTy.usize LeanPrimTy.usize
  | lean_uint16_lor               : LeanInitPureExtern_T_T_T uint16 uint16 uint16
  | lean_uint16_mul               : LeanInitPureExtern_T_T_T uint16 uint16 uint16
  | lean_uint16_land              : LeanInitPureExtern_T_T_T uint16 uint16 uint16
  | lean_uint8_sub                : LeanInitPureExtern_T_T_T uint8 uint8 uint8
  | lean_uint32_div               : LeanInitPureExtern_T_T_T uint32 uint32 uint32
  | lean_uint64_add               : LeanInitPureExtern_T_T_T uint64 uint64 uint64
  | lean_uint64_lor               : LeanInitPureExtern_T_T_T uint64 uint64 uint64
  | lean_uint64_mod               : LeanInitPureExtern_T_T_T uint64 uint64 uint64
  | lean_uint8_lor                : LeanInitPureExtern_T_T_T uint8 uint8 uint8
  | lean_uint32_shift_right       : LeanInitPureExtern_T_T_T uint32 uint32 uint32
  | lean_uint16_xor               : LeanInitPureExtern_T_T_T uint16 uint16 uint16
  | lean_usize_lor                : LeanInitPureExtern_T_T_T LeanPrimTy.usize LeanPrimTy.usize LeanPrimTy.usize
  | lean_uint8_div                : LeanInitPureExtern_T_T_T uint8 uint8 uint8
  | lean_uint16_shift_left        : LeanInitPureExtern_T_T_T uint16 uint16 uint16
  | lean_uint16_mod               : LeanInitPureExtern_T_T_T uint16 uint16 uint16
  | lean_uint64_div               : LeanInitPureExtern_T_T_T uint64 uint64 uint64
  | lean_uint16_dec_lt            : LeanInitPureExtern_T_T_T uint16 uint16 bool
  | lean_uint8_shift_right        : LeanInitPureExtern_T_T_T uint8 uint8 uint8
  | lean_uint32_lor               : LeanInitPureExtern_T_T_T uint32 uint32 uint32
  | lean_uint64_mul               : LeanInitPureExtern_T_T_T uint64 uint64 uint64
  | lean_usize_shift_right        : LeanInitPureExtern_T_T_T LeanPrimTy.usize LeanPrimTy.usize LeanPrimTy.usize
  | lean_uint64_land              : LeanInitPureExtern_T_T_T uint64 uint64 uint64
  | lean_uint8_shift_left         : LeanInitPureExtern_T_T_T uint8 uint8 uint8
  | lean_uint16_div               : LeanInitPureExtern_T_T_T uint16 uint16 uint16
  | lean_uint8_land               : LeanInitPureExtern_T_T_T uint8 uint8 uint8
  | lean_uint64_dec_le            : LeanInitPureExtern_T_T_T uint64 uint64 bool
  | lean_uint8_mul                : LeanInitPureExtern_T_T_T uint8 uint8 uint8
  | lean_uint64_sub               : LeanInitPureExtern_T_T_T uint64 uint64 uint64
  | lean_uint8_add                : LeanInitPureExtern_T_T_T uint8 uint8 uint8
  | lean_usize_div                : LeanInitPureExtern_T_T_T LeanPrimTy.usize LeanPrimTy.usize LeanPrimTy.usize
  | lean_uint32_xor               : LeanInitPureExtern_T_T_T uint32 uint32 uint32
  | lean_uint16_dec_le            : LeanInitPureExtern_T_T_T uint16 uint16 bool
  | lean_uint32_shift_left        : LeanInitPureExtern_T_T_T uint32 uint32 uint32
  | lean_uint16_sub               : LeanInitPureExtern_T_T_T uint16 uint16 uint16
  | lean_uint32_mul               : LeanInitPureExtern_T_T_T uint32 uint32 uint32
  | lean_uint32_land              : LeanInitPureExtern_T_T_T uint32 uint32 uint32
  | lean_usize_mod                : LeanInitPureExtern_T_T_T LeanPrimTy.usize LeanPrimTy.usize LeanPrimTy.usize
  | lean_uint8_mod                : LeanInitPureExtern_T_T_T uint8 uint8 uint8
  | lean_uint64_dec_lt            : LeanInitPureExtern_T_T_T uint64 uint64 bool
  | lean_uint8_xor                : LeanInitPureExtern_T_T_T uint8 uint8 uint8
  | lean_uint16_shift_right       : LeanInitPureExtern_T_T_T uint16 uint16 uint16
  | lean_uint64_xor               : LeanInitPureExtern_T_T_T uint64 uint64 uint64
  -- (†) | lean_byte_array_fget          : LeanInitPureExtern_T_T_T byteArray nat uint8
  -- (†) | lean_byte_array_uget          : LeanInitPureExtern_T_T_T byteArray LeanPrimTy.usize uint8
  -- (†) | lean_byte_array_get           : LeanInitPureExtern_T_T_T byteArray nat uint8
  -- | lean_string_get_utf8_byte     : LeanInitPureExtern_T_T_T string stringPos uint8 -- TODO: no such func?
  -- | lean_string_get_byte_fast_raw : LeanInitPureExtern_T_T_T string stringPos uint8
  | lean_string_append_defs       : LeanInitPureExtern_T_T_T string string string
  | lean_string_utf8_next_basic   : LeanInitPureExtern_T_T_T string stringPos stringPos
  | lean_string_pos_raw_next      : LeanInitPureExtern_T_T_T string stringPos stringPos
  | lean_string_pos_raw_get       : LeanInitPureExtern_T_T_T string stringPos char
  | lean_string_get_basic         : LeanInitPureExtern_T_T_T string stringPos char
  | lean_string_pos_raw_prev      : LeanInitPureExtern_T_T_T string stringPos stringPos
  | lean_string_prev              : LeanInitPureExtern_T_T_T string stringPos stringPos
  | lean_string_next_fast         : LeanInitPureExtern_T_T_T string stringPos stringPos
  | lean_string_pos_raw_next_fast : LeanInitPureExtern_T_T_T string stringPos stringPos
  | lean_string_pos_next          : LeanInitPureExtern_T_T_T string stringPos stringPos
  | lean_string_at_end_basic      : LeanInitPureExtern_T_T_T string stringPos bool
  | lean_string_pos_raw_at_end    : LeanInitPureExtern_T_T_T string stringPos bool
  | lean_string_pos_raw_get_bang  : LeanInitPureExtern_T_T_T string stringPos char
  | lean_string_get_bang          : LeanInitPureExtern_T_T_T string stringPos char
  -- | lean_string_utf8_get_fast     : LeanInitPureExtern_T_T_T string nat char -- TODO: dependent function, needs special treatment. Use Slice.Pos.get instead of decodeChar?
  | lean_string_get_fast          : LeanInitPureExtern_T_T_T string stringPos char
  | lean_string_pos_raw_get_fast  : LeanInitPureExtern_T_T_T string stringPos char
  | lean_string_is_valid_pos      : LeanInitPureExtern_T_T_T string stringPos bool
  | lean_string_dec_lt            : LeanInitPureExtern_T_T_T string string bool
  | lean_int8_add                 : LeanInitPureExtern_T_T_T int8 int8 int8
  | lean_int16_dec_le             : LeanInitPureExtern_T_T_T int16 int16 bool
  | lean_int32_land               : LeanInitPureExtern_T_T_T int32 int32 int32
  | lean_int8_div                 : LeanInitPureExtern_T_T_T int8 int8 int8
  | lean_int32_mul                : LeanInitPureExtern_T_T_T int32 int32 int32
  | lean_int64_sub                : LeanInitPureExtern_T_T_T int64 int64 int64
  | lean_int16_shift_right        : LeanInitPureExtern_T_T_T int16 int16 int16
  | lean_int64_xor                : LeanInitPureExtern_T_T_T int64 int64 int64
  | lean_int32_dec_le             : LeanInitPureExtern_T_T_T int32 int32 bool
  | lean_isize_xor                : LeanInitPureExtern_T_T_T LeanPrimTy.isize LeanPrimTy.isize LeanPrimTy.isize
  | lean_isize_shift_left         : LeanInitPureExtern_T_T_T LeanPrimTy.isize LeanPrimTy.isize LeanPrimTy.isize
  | lean_int64_mul                : LeanInitPureExtern_T_T_T int64 int64 int64
  | lean_int32_sub                : LeanInitPureExtern_T_T_T int32 int32 int32
  | lean_int64_land               : LeanInitPureExtern_T_T_T int64 int64 int64
  | lean_int8_shift_right         : LeanInitPureExtern_T_T_T int8 int8 int8
  | lean_int64_lor                : LeanInitPureExtern_T_T_T int64 int64 int64
  | lean_int16_div                : LeanInitPureExtern_T_T_T int16 int16 int16
  | lean_isize_mod                : LeanInitPureExtern_T_T_T LeanPrimTy.isize LeanPrimTy.isize LeanPrimTy.isize
  | lean_int8_mod                 : LeanInitPureExtern_T_T_T int8 int8 int8
  | lean_isize_shift_right        : LeanInitPureExtern_T_T_T LeanPrimTy.isize LeanPrimTy.isize LeanPrimTy.isize
  | lean_int8_shift_left          : LeanInitPureExtern_T_T_T int8 int8 int8
  | lean_int16_dec_lt             : LeanInitPureExtern_T_T_T int16 int16 bool
  | lean_int8_xor                 : LeanInitPureExtern_T_T_T int8 int8 int8
  | lean_int32_dec_eq             : LeanInitPureExtern_T_T_T int32 int32 bool
  | lean_int16_mod                : LeanInitPureExtern_T_T_T int16 int16 int16
  | lean_isize_div                : LeanInitPureExtern_T_T_T LeanPrimTy.isize LeanPrimTy.isize LeanPrimTy.isize
  | lean_int16_dec_eq             : LeanInitPureExtern_T_T_T int16 int16 bool
  | lean_isize_add                : LeanInitPureExtern_T_T_T LeanPrimTy.isize LeanPrimTy.isize LeanPrimTy.isize
  | lean_int32_dec_lt             : LeanInitPureExtern_T_T_T int32 int32 bool
  | lean_isize_lor                : LeanInitPureExtern_T_T_T LeanPrimTy.isize LeanPrimTy.isize LeanPrimTy.isize
  | lean_int64_mod                : LeanInitPureExtern_T_T_T int64 int64 int64
  | lean_int64_shift_left         : LeanInitPureExtern_T_T_T int64 int64 int64
  | lean_isize_land               : LeanInitPureExtern_T_T_T LeanPrimTy.isize LeanPrimTy.isize LeanPrimTy.isize
  | lean_isize_mul                : LeanInitPureExtern_T_T_T LeanPrimTy.isize LeanPrimTy.isize LeanPrimTy.isize
  | lean_int64_dec_lt             : LeanInitPureExtern_T_T_T int64 int64 bool
  | lean_isize_dec_le             : LeanInitPureExtern_T_T_T LeanPrimTy.isize LeanPrimTy.isize bool
  | lean_int8_dec_eq              : LeanInitPureExtern_T_T_T int8 int8 bool
  | lean_int32_xor                : LeanInitPureExtern_T_T_T int32 int32 int32
  | lean_int32_shift_left         : LeanInitPureExtern_T_T_T int32 int32 int32
  | lean_isize_sub                : LeanInitPureExtern_T_T_T LeanPrimTy.isize LeanPrimTy.isize LeanPrimTy.isize
  | lean_int16_land               : LeanInitPureExtern_T_T_T int16 int16 int16
  | lean_int32_shift_right        : LeanInitPureExtern_T_T_T int32 int32 int32
  | lean_int16_mul                : LeanInitPureExtern_T_T_T int16 int16 int16
  | lean_int16_shift_left         : LeanInitPureExtern_T_T_T int16 int16 int16
  | lean_int16_xor                : LeanInitPureExtern_T_T_T int16 int16 int16
  | lean_int8_dec_lt              : LeanInitPureExtern_T_T_T int8 int8 bool
  | lean_int64_dec_eq             : LeanInitPureExtern_T_T_T int64 int64 bool
  | lean_int64_dec_le             : LeanInitPureExtern_T_T_T int64 int64 bool
  | lean_int32_add                : LeanInitPureExtern_T_T_T int32 int32 int32
  | lean_isize_dec_lt             : LeanInitPureExtern_T_T_T LeanPrimTy.isize LeanPrimTy.isize bool
  | lean_int32_lor                : LeanInitPureExtern_T_T_T int32 int32 int32
  | lean_int32_mod                : LeanInitPureExtern_T_T_T int32 int32 int32
  | lean_int64_add                : LeanInitPureExtern_T_T_T int64 int64 int64
  | lean_int8_sub                 : LeanInitPureExtern_T_T_T int8 int8 int8
  | lean_int16_lor                : LeanInitPureExtern_T_T_T int16 int16 int16
  | lean_int64_div                : LeanInitPureExtern_T_T_T int64 int64 int64
  | lean_isize_dec_eq             : LeanInitPureExtern_T_T_T LeanPrimTy.isize LeanPrimTy.isize bool
  | lean_int16_add                : LeanInitPureExtern_T_T_T int16 int16 int16
  | lean_int8_dec_le              : LeanInitPureExtern_T_T_T int8 int8 bool
  | lean_int8_mul                 : LeanInitPureExtern_T_T_T int8 int8 int8
  | lean_int8_land                : LeanInitPureExtern_T_T_T int8 int8 int8
  | lean_int32_div                : LeanInitPureExtern_T_T_T int32 int32 int32
  | lean_int16_sub                : LeanInitPureExtern_T_T_T int16 int16 int16
  | lean_int8_lor                 : LeanInitPureExtern_T_T_T int8 int8 int8
  | lean_int64_shift_right        : LeanInitPureExtern_T_T_T int64 int64 int64
  | lean_slice_dec_lt             : LeanInitPureExtern_T_T_T stringSlice stringSlice bool
  | lean_float_div                : LeanInitPureExtern_T_T_T float float float
  | lean_float_beq                : LeanInitPureExtern_T_T_T float float bool
  | lean_float_decLe              : LeanInitPureExtern_T_T_T float float bool
  | lean_float_le                 : LeanInitPureExtern_T_T_T float float bool
  | lean_float_decLt              : LeanInitPureExtern_T_T_T float float bool
  | lean_float_lt                 : LeanInitPureExtern_T_T_T float float bool
  | atan2                         : LeanInitPureExtern_T_T_T float float float
  | lean_float_mul                : LeanInitPureExtern_T_T_T float float float
  | pow                           : LeanInitPureExtern_T_T_T float float float
  | lean_float_scaleb             : LeanInitPureExtern_T_T_T float int64 float
  | lean_float_add                : LeanInitPureExtern_T_T_T float float float
  | lean_float_sub                : LeanInitPureExtern_T_T_T float float float
  -- (†) | lean_float_array_get          : LeanInitPureExtern_T_T_T floatArray nat float
  -- (†) | lean_float_array_uget         : LeanInitPureExtern_T_T_T floatArray LeanPrimTy.usize float
  -- (†) | lean_float_array_fget         : LeanInitPureExtern_T_T_T floatArray nat float
  -- (†) | lean_float_array_push         : LeanInitPureExtern_T_T_T floatArray float floatArray
  | lean_float32_div              : LeanInitPureExtern_T_T_T float32 float32 float32
  | lean_float32_le               : LeanInitPureExtern_T_T_T float32 float32 bool
  | lean_float32_decLe            : LeanInitPureExtern_T_T_T float32 float32 bool
  | lean_float32_sub              : LeanInitPureExtern_T_T_T float32 float32 float32
  | powf                          : LeanInitPureExtern_T_T_T float32 float32 float32
  | lean_float32_beq              : LeanInitPureExtern_T_T_T float32 float32 bool
  | atan2f                        : LeanInitPureExtern_T_T_T float32 float32 float32
  | lean_float32_add              : LeanInitPureExtern_T_T_T float32 float32 float32
  | lean_float32_scaleb           : LeanInitPureExtern_T_T_T float32 int64 float32 -- TODO: wrong type, should be int
  | lean_float32_mul              : LeanInitPureExtern_T_T_T float32 float32 float32
  | lean_float32_lt               : LeanInitPureExtern_T_T_T float32 float32 bool
  | lean_float32_decLt            : LeanInitPureExtern_T_T_T float32 float32 bool
  -- | lean_sharecommon_eq           : LeanInitPureExtern_T_T_T shareCommonObject shareCommonObject bool
  -- Commented out with the `shareCommonObject` handle it reads: it is pointer equality,
  -- not a function of the values.
  | lean_string_uget_byte_fast    : LeanInitPureExtern_T_T_T string LeanPrimTy.usize uint8
  -- (†) | lean_sarray_beq               : LeanInitPureExtern_T_T_T byteArray byteArray bool
  -- (†) | lean_sarray_dec_eq            : LeanInitPureExtern_T_T_T byteArray byteArray bool
  -- (†) | lean_string_compare           : LeanInitPureExtern_T_T_T string string ordering

inductive LeanInitPureExtern_T_T_T_T : LeanPrimTy → LeanPrimTy → LeanPrimTy → LeanPrimTy → Type where
  | lean_substring_extract         : LeanInitPureExtern_T_T_T_T substring stringPos stringPos substring
  | lean_string_pushn              : LeanInitPureExtern_T_T_T_T string char nat string
  | lean_string_utf8_extract       : LeanInitPureExtern_T_T_T_T string stringPos stringPos string
  | lean_string_utf8_extract_fast  : LeanInitPureExtern_T_T_T_T string stringPos stringPos string
  | lean_string_utf8_extract_basic : LeanInitPureExtern_T_T_T_T string stringPos stringPos string
  | lean_string_pos_raw_set        : LeanInitPureExtern_T_T_T_T string stringPos char string
  | lean_string_pos_set            : LeanInitPureExtern_T_T_T_T string stringPos char string
  | lean_string_set                : LeanInitPureExtern_T_T_T_T string stringPos char string

inductive LeanInitPureExtern_T_T_T_T_T : LeanPrimTy → LeanPrimTy → LeanPrimTy → LeanPrimTy → LeanPrimTy → LeanPrimTy → Type where
  | lean_string_memcmp : LeanInitPureExtern_T_T_T_T_T string string stringPos stringPos stringPos bool

---- Now only complex

section

variable {X : Type}
  [Coe LeanPrimTy X]
  [Coe (LeanPrimTyCovariant LeanPrimTy) X]
  [Coe (LeanPrimTyCovariant X) X]
  (option : X → X)
  (list : X → X)
  (fn1 : LeanPrimTy → LeanPrimTy → X)
  (prod : LeanPrimTy → LeanPrimTy → X)

inductive LeanInitPureExtern_X_X : X → X → Type where
  -- | lean_sorry                     : (α : X) → LeanInitPureExtern_X_X bool α -- we should not support
  | lean_array_get_size            : (α : X) → LeanInitPureExtern_X_X (array α) nat
  | lean_array_to_list             : (α : X) → LeanInitPureExtern_X_X (array α) (list α)
  | lean_empty_array_with_capacity : (α : X) → LeanInitPureExtern_X_X nat (array α)
  | lean_array_mk_empty            : (α : X) → LeanInitPureExtern_X_X nat (array α)
  | lean_panic_fn_borrowed         : (α : X) → (c : Inhabited X) → LeanInitPureExtern_X_X string α
  | lean_array_mk                  : (α : X) → LeanInitPureExtern_X_X (list α) (array α)
  | lean_thunk_pure                : (α : X) → LeanInitPureExtern_X_X α (thunk α)
  | lean_mk_thunk                  : (α : X) → LeanInitPureExtern_X_X (lazy α) (thunk α)
  -- | lean_task_get_own              : (α : X) → LeanInitPureExtern_X_X (task α) α
  -- | lean_task_pure                 : (α : X) → LeanInitPureExtern_X_X α (task α)
  | lean_thunk_get_own             : (α : X) → LeanInitPureExtern_X_X (thunk α) α
  | lean_ptr_addr                  : (α : X) → LeanInitPureExtern_X_X α LeanPrimTy.usize
  | lean_dbg_stack_trace           : (α : X) → LeanInitPureExtern_X_X (lazy α) α
  | lean_is_exclusive_obj          : (α : X) → LeanInitPureExtern_X_X α bool
  | lean_array_pop                 : (α : X) → LeanInitPureExtern_X_X (array α) (array α)
  | lean_array_size                : (α : X) → LeanInitPureExtern_X_X (array α) LeanPrimTy.usize
  -- | lean_io_promise_result_opt     : (α : X) → LeanInitPureExtern_X_X (promise α) (task (option α))
  | lean_option_get_or_block       : (α : X) → (c : Nonempty X) → LeanInitPureExtern_X_X (option α) α
  | lean_sharecommon_quick         : (α : X) → LeanInitPureExtern_X_X α α
  -- (†) | lean_byte_array_mk             : LeanInitPureExtern_X_X (array uint8) byteArray
  -- (†) | lean_byte_array_data           : LeanInitPureExtern_X_X byteArray (array uint8)
  | lean_string_mk                 : LeanInitPureExtern_X_X (list char) string
  | lean_string_mk_def             : LeanInitPureExtern_X_X (list char) string
  | lean_string_data               : LeanInitPureExtern_X_X string (list char)
  | lean_string_to_list            : LeanInitPureExtern_X_X string (list char)
  | lean_float_frexp               : LeanInitPureExtern_X_X float (prod float int64)
  -- (†) | lean_float_array_data          : LeanInitPureExtern_X_X floatArray (array float)
  -- (†) | lean_float_array_mk            : LeanInitPureExtern_X_X (array float) floatArray
  | lean_float32_frexp             : LeanInitPureExtern_X_X float32 (prod float32 int64)
  | lean_is_scalar                 : (α : X) → LeanInitPureExtern_X_X α bool

end

section

variable {X : Type}
  [Coe LeanPrimTy X]
  [Coe (LeanPrimTyCovariant LeanPrimTy) X]
  [Coe (LeanPrimTyCovariant X) X]
  (option : X → X)
  (list : X → X)
  (fn1 : LeanPrimTy → LeanPrimTy → X)
  (prodX : X → LeanPrimTy → X)

inductive LeanInitPureExtern_X_X_X : X → X → X → Type where
  | lean_array_get_borrowed     : (α : X) → (c : Inhabited X) → LeanInitPureExtern_X_X_X (array α) nat α
  | lean_array_push             : (α : X) → LeanInitPureExtern_X_X_X (array α) α (array α)
  | lean_array_fget_borrowed    : (α : X) → LeanInitPureExtern_X_X_X (array α) nat α
  | lean_array_get              : (α : X) → (c : Inhabited X) → LeanInitPureExtern_X_X_X (array α) nat α
  | lean_array_fget             : (α : X) → LeanInitPureExtern_X_X_X (array α) nat α
  -- | lean_task_spawn             : (α : X) → LeanInitPureExtern_X_X_X (lazy α) nat (task α)
  | lean_dbg_sleep              : (α : X) → LeanInitPureExtern_X_X_X uint32 (lazy α) α
  | lean_dbg_trace              : (α : X) → LeanInitPureExtern_X_X_X string (lazy α) α
  | lean_dbg_trace_if_shared    : (α : X) → LeanInitPureExtern_X_X_X string α α
  | lean_array_uget             : (α : X) → LeanInitPureExtern_X_X_X (array α) LeanPrimTy.usize α
  | lean_mk_array               : (α : X) → LeanInitPureExtern_X_X_X nat α (array α)
  -- | lean_state_sharecommon      : (α : X) → LeanInitPureExtern_X_X_X shareCommonState α (prodX α shareCommonState)
  -- Commented out with the `shareCommonState` handle it threads: with the interning
  -- table erased it is `fun s a => (a, s)`, so it has nothing left to do.
  | lean_substring_takewhile    : LeanInitPureExtern_X_X_X substring (fn1 char bool) substring
  | lean_substring_all          : LeanInitPureExtern_X_X_X substring (fn1 char bool) bool
  | lean_string_intercalate     : LeanInitPureExtern_X_X_X string (list string) string
  | lean_string_any             : LeanInitPureExtern_X_X_X string (fn1 char bool) bool
  | lean_string_pos_raw_get_opt : LeanInitPureExtern_X_X_X string stringPos (option char)
  | lean_string_get_opt         : LeanInitPureExtern_X_X_X string stringPos (option char)
  | lean_array_uget_borrowed    : (α : X) → LeanInitPureExtern_X_X_X (array α) LeanPrimTy.usize α

end section

section

variable {X : Type}
  [Coe LeanPrimTy X]
  [Coe (LeanPrimTyCovariant X) X]
  (fn1 : LeanPrimTy → LeanPrimTy → X)
  (fn2 : LeanPrimTy → LeanPrimTy → LeanPrimTy → X)
  (byteArray : X)
  (floatArray : X)

inductive LeanInitPureExtern_X_X_X_X : X → X → X → X → Type where
  | lean_array_set        : (α : X) → LeanInitPureExtern_X_X_X_X (array α) nat α (array α)
  | lean_array_fset       : (α : X) → LeanInitPureExtern_X_X_X_X (array α) nat α (array α)
  | lean_array_fswap      : (α : X) → LeanInitPureExtern_X_X_X_X (array α) nat nat (array α)
  | lean_array_swap       : (α : X) → LeanInitPureExtern_X_X_X_X (array α) nat nat (array α)
  | lean_array_uset       : (α : X) → LeanInitPureExtern_X_X_X_X (array α) LeanPrimTy.usize α (array α)
  | lean_string_foldl     : LeanInitPureExtern_X_X_X_X (fn2 string char string) string string string
  | lean_string_nextwhile : LeanInitPureExtern_X_X_X_X string (fn1 char bool) stringPos stringPos
  | lean_byte_array_set            : LeanInitPureExtern_X_X_X_X byteArray nat uint8 byteArray
  | lean_byte_array_uset           : LeanInitPureExtern_X_X_X_X byteArray LeanPrimTy.usize uint8 byteArray
  | lean_byte_array_fset           : LeanInitPureExtern_X_X_X_X byteArray nat uint8 byteArray
  | lean_float_array_fset          : LeanInitPureExtern_X_X_X_X floatArray nat float floatArray
  | lean_float_array_uset          : LeanInitPureExtern_X_X_X_X floatArray LeanPrimTy.usize float floatArray
  | lean_float_array_set           : LeanInitPureExtern_X_X_X_X floatArray nat float floatArray

end section

section

variable {X : Type}
  [Coe LeanPrimTy X]
  [Coe (LeanPrimTyCovariant X) X]
  (fn1 : X → X → X)

open LeanPrimTy
open LeanPrimTyCovariant

-- inductive LeanInitPureExtern_X_X_X_X_X : X → X → X → X → X → Type where
--   | lean_task_map  : (α : X) → (β : X) → LeanInitPureExtern_X_X_X_X_X (fn1 α β) (task α) nat bool (task β)
--   | lean_task_bind : (α : X) → (β : X) → LeanInitPureExtern_X_X_X_X_X (task α) (fn1 α (task β)) nat bool (task β)

end section

section

variable {X : Type}
  [Coe LeanPrimTy X]
  (byteArray : X)

open LeanPrimTy

inductive LeanInitPureExtern_X_X_X_X_X_X : X → LeanPrimTy → X → LeanPrimTy → LeanPrimTy → LeanPrimTy → X → Type where
  | lean_byte_array_copy_slice : LeanInitPureExtern_X_X_X_X_X_X byteArray nat byteArray nat nat bool byteArray

end section
