module
prelude
-- public import LeanScript.Ty
public import LeanScript.LeanPrimTy
public import LeanScript.LeanPrimTyCovariant
set_option autoImplicit false
@[expose] public section
namespace LeanScript

open LeanPrimTy
open LeanPrimTyCovariant

/-!
# The catalogue of the pure `@[extern]` functions of Lean's `Init`

Every entry of the *terminal* families (`LeanInitPureExternLazy`,
`LeanInitPureExtern1OnlyPrim`, `LeanInitPureExtern2OnlyPrim`,
`LeanInitPureExtern3OnlyPrim`, `LeanInitPureExtern5`) that is listed here has a
meaning as a **total** Lean function of the values of its arguments
(`LeanScript.ExternEval1`, `LeanScript.ExternEval2`, `LeanScript.ExternEvalMisc`), so the
evaluator of `LeanScript.Reduce` can always run it.  The entries that had no such meaning
are commented out rather than deleted, each marked with the reason:

* `(†)` — **the entry's type is not the type its name says.**  `byteArray`,
  `floatArray`, `ordering` and `name` are not constructors of `LeanPrimTy` (a byte
  array is `Array UInt8` at this layer, an `Ordering` is an enum, a `Name` is an
  inductive), so with `autoImplicit` on they were silently read as *type variables*:
  `lean_byte_array_size` had type `LeanInitPureExtern1OnlyPrim ?α .nat` for every
  terminal `?α`, i.e. "the size of a `Nat`, of a `Float`, of anything at all".  Such an
  entry denotes no function of its argument's value.  `set_option autoImplicit false`
  above is what keeps them from coming back.  They belong in the polymorphic families,
  where `byteArray` and `floatArray` are genuine parameters (`Extern3At`, `Extern6At`);
  moving them there is a change to the catalogue *and* to every instantiation of it.
* `(‡)` — **the answer is a fact about the machine the compiled program runs on**, not a
  function of any value: the version of the toolchain, the platform, the width of a
  word, the number of cores.  Reading it off the machine that runs the *compiler* would
  bake the wrong answer into the semantics.  They come back as soon as the backend has a
  target description to read them from; until then `LeanInitPureExternLazy` is empty, and
  `LeanInitPureExternLazy.eval` is total for the vacuous reason.

* `(§)` — **a second name for an entry that is already here.**  `Float.toModel` and
  `Float.toBits` are compiled to the *same* C function (`lean_float_to_bits`), and so
  are `Float.ofModel`/`Float.ofBits` and their `Float32` counterparts; what `toModel`
  answers with is `Float.Model`, the abstract model of a float, which is not a terminal
  type of this language (and is not a type of the current toolchain at all).  At the
  type written here they were a duplicate of `lean_float_to_bits`, so the language would
  have had two names for one function, only one of which was the function its name says.
  Use `lean_float_to_bits`, `lean_float_of_bits`, `lean_float32_to_bits` and
  `lean_float32_of_bits`, which are entries of this family and do run.

See `EXTERN_EVALUATION.md`.
-/

/-- The constants of the runtime.  **Empty**: every entry is a fact about the target
    machine, see `(‡)` above. -/
inductive LeanInitPureExternLazy : LeanPrimTy → Type where
  -- (‡) | lean_system_platform_nbits             : LeanInitPureExternLazy .nat
  -- (‡) | lean_version_get_special_desc          : LeanInitPureExternLazy .string
  -- (‡) | lean_version_get_is_release            : LeanInitPureExternLazy .bool
  -- (‡) | lean_version_get_major                 : LeanInitPureExternLazy .nat
  -- (‡) | lean_version_get_patch                 : LeanInitPureExternLazy .nat
  -- (‡) | lean_internal_is_stage0                : LeanInitPureExternLazy .bool
  -- (‡) | lean_version_get_minor                 : LeanInitPureExternLazy .nat
  -- (‡) | lean_get_githash                       : LeanInitPureExternLazy .string
  -- (‡) | lean_internal_has_llvm_backend         : LeanInitPureExternLazy .bool
  -- (‡) | lean_system_platform_emscripten        : LeanInitPureExternLazy .bool
  -- (‡) | lean_system_platform_target            : LeanInitPureExternLazy .string
  -- (‡) | lean_system_platform_windows           : LeanInitPureExternLazy .bool
  -- (‡) | lean_system_platform_osx               : LeanInitPureExternLazy .bool
  -- (‡) | lean_internal_get_hardware_concurrency : LeanInitPureExternLazy .uint32
  -- (‡) | lean_system_platform_linux             : LeanInitPureExternLazy .bool

inductive LeanInitPureExtern1OnlyPrim : LeanPrimTy → LeanPrimTy → Type where
  | lean_uint32_of_nat_mk           : LeanInitPureExtern1OnlyPrim (bitvec 32) uint32
  -- (†) | lean_byte_array_size            : LeanInitPureExtern1OnlyPrim byteArray nat
  -- (†) | lean_string_to_utf8             : LeanInitPureExtern1OnlyPrim string byteArray
  | lean_uint32_of_nat_lt           : LeanInitPureExtern1OnlyPrim nat uint32
  | lean_char_of_nat_aux            : LeanInitPureExtern1OnlyPrim nat char
  | lean_uint8_to_bitvec            : LeanInitPureExtern1OnlyPrim uint8 (bitvec 8)
  -- (†) | lean_string_from_utf8_unchecked : LeanInitPureExtern1OnlyPrim byteArray string
  | lean_uint8_of_nat               : LeanInitPureExtern1OnlyPrim nat uint8
  | lean_uint8_of_nat_lt            : LeanInitPureExtern1OnlyPrim nat uint8
  | lean_uint16_to_bitvec           : LeanInitPureExtern1OnlyPrim uint16 (bitvec 16)
  | lean_uint16_of_nat_mk           : LeanInitPureExtern1OnlyPrim (bitvec 16) uint16
  | lean_nat_pred                   : LeanInitPureExtern1OnlyPrim nat nat
  | lean_usize_of_nat_lt            : LeanInitPureExtern1OnlyPrim nat usize
  | lean_string_hash                : LeanInitPureExtern1OnlyPrim string uint64
  | lean_uint64_to_bitvec           : LeanInitPureExtern1OnlyPrim uint64 (bitvec 64)
  | lean_uint64_of_nat_mk           : LeanInitPureExtern1OnlyPrim (bitvec 64) uint64
  | lean_uint32_to_nat              : LeanInitPureExtern1OnlyPrim uint32 nat
  | lean_uint32_to_bitvec           : LeanInitPureExtern1OnlyPrim uint32 (bitvec 32)
  | lean_uint16_of_nat_lt           : LeanInitPureExtern1OnlyPrim nat uint16
  | lean_uint8_of_nat_mk            : LeanInitPureExtern1OnlyPrim (bitvec 8) uint8
  -- (†) | lean_mk_empty_byte_array        : LeanInitPureExtern1OnlyPrim nat byteArray
  | lean_usize_of_nat_mk            : LeanInitPureExtern1OnlyPrim (bitvec 64) usize
  | lean_usize_to_bitvec            : LeanInitPureExtern1OnlyPrim usize (bitvec 64)
  | lean_string_utf8_byte_size      : LeanInitPureExtern1OnlyPrim string nat
  | lean_uint64_of_nat_lt           : LeanInitPureExtern1OnlyPrim nat uint64
  | lean_nat_to_int                 : LeanInitPureExtern1OnlyPrim nat int
  | lean_int_to_nat                 : LeanInitPureExtern1OnlyPrim int nat
  | lean_int_dec_nonneg             : LeanInitPureExtern1OnlyPrim int bool
  | lean_int_neg_succ_of_nat        : LeanInitPureExtern1OnlyPrim nat int
  | lean_int_neg                    : LeanInitPureExtern1OnlyPrim int int
  | lean_nat_abs                    : LeanInitPureExtern1OnlyPrim int nat
  | lean_uint64_to_nat              : LeanInitPureExtern1OnlyPrim uint64 nat
  | lean_uint32_to_uint8            : LeanInitPureExtern1OnlyPrim uint32 uint8
  | lean_usize_to_nat               : LeanInitPureExtern1OnlyPrim usize nat
  | lean_uint64_to_uint32           : LeanInitPureExtern1OnlyPrim uint64 uint32
  | lean_uint32_to_uint16           : LeanInitPureExtern1OnlyPrim uint32 uint16
  | lean_uint16_to_uint32           : LeanInitPureExtern1OnlyPrim uint16 uint32
  | lean_uint32_to_uint64           : LeanInitPureExtern1OnlyPrim uint32 uint64
  | lean_uint32_of_nat              : LeanInitPureExtern1OnlyPrim nat uint32
  | lean_uint16_to_nat              : LeanInitPureExtern1OnlyPrim uint16 nat
  | lean_uint16_to_uint8            : LeanInitPureExtern1OnlyPrim uint16 uint8
  | lean_usize_of_nat               : LeanInitPureExtern1OnlyPrim nat usize
  | lean_uint8_to_uint64            : LeanInitPureExtern1OnlyPrim uint8 uint64
  | lean_uint8_to_nat               : LeanInitPureExtern1OnlyPrim uint8 nat
  | lean_uint64_of_nat              : LeanInitPureExtern1OnlyPrim nat uint64
  | lean_uint8_to_uint32            : LeanInitPureExtern1OnlyPrim uint8 uint32
  | lean_uint16_of_nat              : LeanInitPureExtern1OnlyPrim nat uint16
  | lean_uint16_to_uint64           : LeanInitPureExtern1OnlyPrim uint16 uint64
  | lean_uint64_to_uint8            : LeanInitPureExtern1OnlyPrim uint64 uint8
  | lean_uint64_to_uint16           : LeanInitPureExtern1OnlyPrim uint64 uint16
  | lean_uint8_to_uint16            : LeanInitPureExtern1OnlyPrim uint8 uint16
  | lean_string_trim                : LeanInitPureExtern1OnlyPrim string string
  | lean_substring_tostring         : LeanInitPureExtern1OnlyPrim substring string
  | lean_string_isempty             : LeanInitPureExtern1OnlyPrim string bool
  | lean_string_front               : LeanInitPureExtern1OnlyPrim string char
  | lean_string_length              : LeanInitPureExtern1OnlyPrim string nat
  | lean_string_capitalize          : LeanInitPureExtern1OnlyPrim string string
  | lean_substring_front            : LeanInitPureExtern1OnlyPrim substring char
  | lean_substring_isempty          : LeanInitPureExtern1OnlyPrim substring bool
  | lean_string_of_usize            : LeanInitPureExtern1OnlyPrim usize string
  | lean_nat_log2                   : LeanInitPureExtern1OnlyPrim nat nat
  | lean_uint16_neg                 : LeanInitPureExtern1OnlyPrim uint16 uint16
  | lean_uint16_to_usize            : LeanInitPureExtern1OnlyPrim uint16 usize
  | lean_uint64_complement          : LeanInitPureExtern1OnlyPrim uint64 uint64
  | lean_bool_to_uint32             : LeanInitPureExtern1OnlyPrim bool uint32
  | lean_uint8_neg                  : LeanInitPureExtern1OnlyPrim uint8 uint8
  | lean_uint16_complement          : LeanInitPureExtern1OnlyPrim uint16 uint16
  | lean_uint32_neg                 : LeanInitPureExtern1OnlyPrim uint32 uint32
  | lean_usize_neg                  : LeanInitPureExtern1OnlyPrim usize usize
  | lean_usize_to_uint64            : LeanInitPureExtern1OnlyPrim usize uint64
  | lean_bool_to_uint64             : LeanInitPureExtern1OnlyPrim bool uint64
  | lean_usize_of_nat32             : LeanInitPureExtern1OnlyPrim nat usize
  | lean_uint64_neg                 : LeanInitPureExtern1OnlyPrim uint64 uint64
  | lean_uint32_to_usize            : LeanInitPureExtern1OnlyPrim uint32 usize
  | lean_uint8_complement           : LeanInitPureExtern1OnlyPrim uint8 uint8
  | lean_usize_to_uint16            : LeanInitPureExtern1OnlyPrim usize uint16
  | lean_usize_to_uint8             : LeanInitPureExtern1OnlyPrim usize uint8
  | lean_bool_to_uint8              : LeanInitPureExtern1OnlyPrim bool uint8
  | lean_uint32_complement          : LeanInitPureExtern1OnlyPrim uint32 uint32
  | lean_uint8_to_usize             : LeanInitPureExtern1OnlyPrim uint8 usize
  | lean_bool_to_uint16             : LeanInitPureExtern1OnlyPrim bool uint16
  | lean_bool_to_usize              : LeanInitPureExtern1OnlyPrim bool usize
  | lean_uint64_to_usize            : LeanInitPureExtern1OnlyPrim uint64 usize
  | lean_usize_to_uint32            : LeanInitPureExtern1OnlyPrim usize uint32
  | lean_usize_complement           : LeanInitPureExtern1OnlyPrim usize usize
  -- (†) | lean_byte_array_hash            : LeanInitPureExtern1OnlyPrim byteArray uint64
  -- (†) | lean_sarray_size                : LeanInitPureExtern1OnlyPrim byteArray usize
  -- (†) | lean_string_to_utf8_defs        : LeanInitPureExtern1OnlyPrim string byteArray
  -- (†) | lean_string_validate_utf8       : LeanInitPureExtern1OnlyPrim byteArray bool
  | lean_string_length_def          : LeanInitPureExtern1OnlyPrim string nat
  | lean_isize_complement           : LeanInitPureExtern1OnlyPrim isize isize
  | lean_int16_of_nat               : LeanInitPureExtern1OnlyPrim nat int16
  | lean_int32_of_int               : LeanInitPureExtern1OnlyPrim int int32
  | lean_int64_to_isize             : LeanInitPureExtern1OnlyPrim int64 isize
  | lean_isize_to_int8              : LeanInitPureExtern1OnlyPrim isize int8
  | lean_int32_of_nat               : LeanInitPureExtern1OnlyPrim nat int32
  | lean_int64_to_int8              : LeanInitPureExtern1OnlyPrim int64 int8
  | lean_int32_to_int64             : LeanInitPureExtern1OnlyPrim int32 int64
  | lean_int8_to_int16              : LeanInitPureExtern1OnlyPrim int8 int16
  | lean_int64_of_int               : LeanInitPureExtern1OnlyPrim int int64
  | lean_int32_to_isize             : LeanInitPureExtern1OnlyPrim int32 isize
  | lean_int32_neg                  : LeanInitPureExtern1OnlyPrim int32 int32
  | lean_int32_abs                  : LeanInitPureExtern1OnlyPrim int32 int32
  | lean_bool_to_int8               : LeanInitPureExtern1OnlyPrim bool int8
  | lean_isize_to_int16             : LeanInitPureExtern1OnlyPrim isize int16
  | lean_int16_to_int               : LeanInitPureExtern1OnlyPrim int16 int
  | lean_int8_complement            : LeanInitPureExtern1OnlyPrim int8 int8
  | lean_bool_to_int16              : LeanInitPureExtern1OnlyPrim bool int16
  | lean_isize_of_int               : LeanInitPureExtern1OnlyPrim int isize
  | lean_int16_abs                  : LeanInitPureExtern1OnlyPrim int16 int16
  | lean_int16_to_int32             : LeanInitPureExtern1OnlyPrim int16 int32
  | lean_isize_to_int               : LeanInitPureExtern1OnlyPrim isize int
  | lean_isize_of_nat               : LeanInitPureExtern1OnlyPrim nat isize
  | lean_int16_complement           : LeanInitPureExtern1OnlyPrim int16 int16
  | lean_isize_to_int64             : LeanInitPureExtern1OnlyPrim isize int64
  | lean_int64_complement           : LeanInitPureExtern1OnlyPrim int64 int64
  | lean_isize_abs                  : LeanInitPureExtern1OnlyPrim isize isize
  | lean_int16_of_int               : LeanInitPureExtern1OnlyPrim int int16
  | lean_int8_neg                   : LeanInitPureExtern1OnlyPrim int8 int8
  | lean_isize_to_int32             : LeanInitPureExtern1OnlyPrim isize int32
  | lean_int64_to_int32             : LeanInitPureExtern1OnlyPrim int64 int32
  | lean_int64_abs                  : LeanInitPureExtern1OnlyPrim int64 int64
  | lean_int32_complement           : LeanInitPureExtern1OnlyPrim int32 int32
  | lean_bool_to_int64              : LeanInitPureExtern1OnlyPrim bool int64
  | lean_bool_to_isize              : LeanInitPureExtern1OnlyPrim bool isize
  | lean_bool_to_int32              : LeanInitPureExtern1OnlyPrim bool int32
  | lean_int64_of_nat               : LeanInitPureExtern1OnlyPrim nat int64
  | lean_int32_to_int8              : LeanInitPureExtern1OnlyPrim int32 int8
  | lean_int64_to_int_sint          : LeanInitPureExtern1OnlyPrim int64 int
  | lean_int64_neg                  : LeanInitPureExtern1OnlyPrim int64 int64
  | lean_int8_abs                   : LeanInitPureExtern1OnlyPrim int8 int8
  | lean_int8_to_int32              : LeanInitPureExtern1OnlyPrim int8 int32
  | lean_isize_neg                  : LeanInitPureExtern1OnlyPrim isize isize
  | lean_int32_to_int               : LeanInitPureExtern1OnlyPrim int32 int
  | lean_int32_to_int16             : LeanInitPureExtern1OnlyPrim int32 int16
  | lean_int8_to_int64              : LeanInitPureExtern1OnlyPrim int8 int64
  | lean_int8_to_isize              : LeanInitPureExtern1OnlyPrim int8 isize
  | lean_int8_of_nat                : LeanInitPureExtern1OnlyPrim nat int8
  | lean_int16_to_int8              : LeanInitPureExtern1OnlyPrim int16 int8
  | lean_int8_to_int                : LeanInitPureExtern1OnlyPrim int8 int
  | lean_int16_neg                  : LeanInitPureExtern1OnlyPrim int16 int16
  | lean_int64_to_int16             : LeanInitPureExtern1OnlyPrim int64 int16
  | lean_int8_of_int                : LeanInitPureExtern1OnlyPrim int int8
  | lean_int16_to_isize             : LeanInitPureExtern1OnlyPrim int16 isize
  | lean_int16_to_int64             : LeanInitPureExtern1OnlyPrim int16 int64
  | lean_slice_hash                 : LeanInitPureExtern1OnlyPrim stringSlice uint64
  | lean_uint8_to_float             : LeanInitPureExtern1OnlyPrim uint8 float
  | lean_float_to_bits              : LeanInitPureExtern1OnlyPrim float uint64
  | lean_float_of_bits              : LeanInitPureExtern1OnlyPrim uint64 float
  | lean_float_isnan                : LeanInitPureExtern1OnlyPrim float bool
  | log10                           : LeanInitPureExtern1OnlyPrim float float
  | cbrt                            : LeanInitPureExtern1OnlyPrim float float
  | log                             : LeanInitPureExtern1OnlyPrim float float
  | tan                             : LeanInitPureExtern1OnlyPrim float float
  | tanh                            : LeanInitPureExtern1OnlyPrim float float
  | exp2                            : LeanInitPureExtern1OnlyPrim float float
  | lean_float_to_uint16            : LeanInitPureExtern1OnlyPrim float uint16
  | lean_uint32_to_float            : LeanInitPureExtern1OnlyPrim uint32 float
  | lean_float_to_uint64            : LeanInitPureExtern1OnlyPrim float uint64
  | sqrt                            : LeanInitPureExtern1OnlyPrim float float
  | acos                            : LeanInitPureExtern1OnlyPrim float float
  | atan                            : LeanInitPureExtern1OnlyPrim float float
  | acosh                           : LeanInitPureExtern1OnlyPrim float float
  | floor                           : LeanInitPureExtern1OnlyPrim float float
  | fabs                            : LeanInitPureExtern1OnlyPrim float float
  | lean_float_to_uint32            : LeanInitPureExtern1OnlyPrim float uint32
  | lean_float_to_string            : LeanInitPureExtern1OnlyPrim float string
  | lean_uint64_to_float            : LeanInitPureExtern1OnlyPrim uint64 float
  | lean_float_to_uint8             : LeanInitPureExtern1OnlyPrim float uint8
  | sin                             : LeanInitPureExtern1OnlyPrim float float
  | lean_usize_to_float             : LeanInitPureExtern1OnlyPrim usize float
  | cosh                            : LeanInitPureExtern1OnlyPrim float float
  | exp                             : LeanInitPureExtern1OnlyPrim float float
  | ceil                            : LeanInitPureExtern1OnlyPrim float float
  | lean_float_to_usize             : LeanInitPureExtern1OnlyPrim float usize
  | lean_float_isfinite             : LeanInitPureExtern1OnlyPrim float bool
  | round                           : LeanInitPureExtern1OnlyPrim float float
  | cos                             : LeanInitPureExtern1OnlyPrim float float
  | log2                            : LeanInitPureExtern1OnlyPrim float float
  | atanh                           : LeanInitPureExtern1OnlyPrim float float
  | sinh                            : LeanInitPureExtern1OnlyPrim float float
  | asinh                           : LeanInitPureExtern1OnlyPrim float float
  | lean_uint16_to_float            : LeanInitPureExtern1OnlyPrim uint16 float
  | asin                            : LeanInitPureExtern1OnlyPrim float float
  | lean_float_negate               : LeanInitPureExtern1OnlyPrim float float
  | lean_float_isinf                : LeanInitPureExtern1OnlyPrim float bool
  -- (†) | lean_mk_empty_float_array       : LeanInitPureExtern1OnlyPrim nat floatArray
  -- (†) | lean_float_array_usize          : LeanInitPureExtern1OnlyPrim floatArray usize
  -- (†) | lean_float_array_size           : LeanInitPureExtern1OnlyPrim floatArray nat
  | lean_usize_log2                 : LeanInitPureExtern1OnlyPrim usize usize
  | lean_uint16_log2                : LeanInitPureExtern1OnlyPrim uint16 uint16
  | lean_uint64_log2                : LeanInitPureExtern1OnlyPrim uint64 uint64
  | lean_uint8_log2                 : LeanInitPureExtern1OnlyPrim uint8 uint8
  | lean_uint32_log2                : LeanInitPureExtern1OnlyPrim uint32 uint32
  | lean_int32_to_float             : LeanInitPureExtern1OnlyPrim int32 float
  | lean_float_to_int16             : LeanInitPureExtern1OnlyPrim float int16
  | lean_int16_to_float             : LeanInitPureExtern1OnlyPrim int16 float
  | lean_float_to_int32             : LeanInitPureExtern1OnlyPrim float int32
  | lean_isize_to_float             : LeanInitPureExtern1OnlyPrim isize float
  | lean_int8_to_float              : LeanInitPureExtern1OnlyPrim int8 float
  | lean_float_to_int8              : LeanInitPureExtern1OnlyPrim float int8
  | lean_int64_to_float             : LeanInitPureExtern1OnlyPrim int64 float
  | lean_float_to_int64             : LeanInitPureExtern1OnlyPrim float int64
  | lean_float_to_isize             : LeanInitPureExtern1OnlyPrim float isize
  | tanhf                           : LeanInitPureExtern1OnlyPrim float32 float32
  | exp2f                           : LeanInitPureExtern1OnlyPrim float32 float32
  | logf                            : LeanInitPureExtern1OnlyPrim float32 float32
  | lean_float_to_float32           : LeanInitPureExtern1OnlyPrim float float32
  | lean_float32_to_bits            : LeanInitPureExtern1OnlyPrim float32 uint32
  | lean_float32_of_bits            : LeanInitPureExtern1OnlyPrim uint32 float32
  | atanf                           : LeanInitPureExtern1OnlyPrim float32 float32
  | acoshf                          : LeanInitPureExtern1OnlyPrim float32 float32
  | lean_float32_to_uint64          : LeanInitPureExtern1OnlyPrim float32 uint64
  | lean_float32_to_uint16          : LeanInitPureExtern1OnlyPrim float32 uint16
  | lean_usize_to_float32           : LeanInitPureExtern1OnlyPrim usize float32
  | asinf                           : LeanInitPureExtern1OnlyPrim float32 float32
  | lean_uint8_to_float32           : LeanInitPureExtern1OnlyPrim uint8 float32
  | tanf                            : LeanInitPureExtern1OnlyPrim float32 float32
  | lean_float32_to_float           : LeanInitPureExtern1OnlyPrim float32 float
  | lean_float32_isnan              : LeanInitPureExtern1OnlyPrim float32 bool
  | log10f                          : LeanInitPureExtern1OnlyPrim float32 float32
  | cbrtf                           : LeanInitPureExtern1OnlyPrim float32 float32
  | sinhf                           : LeanInitPureExtern1OnlyPrim float32 float32
  | cosf                            : LeanInitPureExtern1OnlyPrim float32 float32
  | lean_uint32_to_float32          : LeanInitPureExtern1OnlyPrim uint32 float32
  | lean_float32_isinf              : LeanInitPureExtern1OnlyPrim float32 bool
  | lean_float32_negate             : LeanInitPureExtern1OnlyPrim float32 float32
  | lean_float32_to_usize           : LeanInitPureExtern1OnlyPrim float32 usize
  | ceilf                           : LeanInitPureExtern1OnlyPrim float32 float32
  | lean_float32_isfinite           : LeanInitPureExtern1OnlyPrim float32 bool
  | sinf                            : LeanInitPureExtern1OnlyPrim float32 float32
  | lean_float32_to_string          : LeanInitPureExtern1OnlyPrim float32 string
  | asinhf                          : LeanInitPureExtern1OnlyPrim float32 float32
  | lean_float32_to_uint32          : LeanInitPureExtern1OnlyPrim float32 uint32
  | log2f                           : LeanInitPureExtern1OnlyPrim float32 float32
  | lean_uint64_to_float32          : LeanInitPureExtern1OnlyPrim uint64 float32
  | atanhf                          : LeanInitPureExtern1OnlyPrim float32 float32
  | floorf                          : LeanInitPureExtern1OnlyPrim float32 float32
  | fabsf                           : LeanInitPureExtern1OnlyPrim float32 float32
  | roundf                          : LeanInitPureExtern1OnlyPrim float32 float32
  | acosf                           : LeanInitPureExtern1OnlyPrim float32 float32
  | sqrtf                           : LeanInitPureExtern1OnlyPrim float32 float32
  | lean_uint16_to_float32          : LeanInitPureExtern1OnlyPrim uint16 float32
  | coshf                           : LeanInitPureExtern1OnlyPrim float32 float32
  | expf                            : LeanInitPureExtern1OnlyPrim float32 float32
  | lean_float32_to_uint8           : LeanInitPureExtern1OnlyPrim float32 uint8
  | lean_float32_to_int64           : LeanInitPureExtern1OnlyPrim float32 int64
  | lean_float32_to_isize           : LeanInitPureExtern1OnlyPrim float32 isize
  | lean_int32_to_float32           : LeanInitPureExtern1OnlyPrim int32 float32
  | lean_float32_to_int8            : LeanInitPureExtern1OnlyPrim float32 int8
  | lean_float32_to_int16           : LeanInitPureExtern1OnlyPrim float32 int16
  | lean_isize_to_float32           : LeanInitPureExtern1OnlyPrim isize float32
  | lean_int8_to_float32            : LeanInitPureExtern1OnlyPrim int8 float32
  | lean_float32_to_int32           : LeanInitPureExtern1OnlyPrim float32 int32
  | lean_int16_to_float32           : LeanInitPureExtern1OnlyPrim int16 float32
  | lean_int64_to_float32           : LeanInitPureExtern1OnlyPrim int64 float32
  -- | lean_io_process_child_pid       : LeanInitPureExtern1OnlyPrim childProcess uint32
  -- Commented out with the `childProcess` handle it reads: see `SHARECOMMON_EMULATION.md`.
  -- | lean_sharecommon_hash           : LeanInitPureExtern1OnlyPrim shareCommonObject uint64
  -- Commented out with the `shareCommonObject` handle it reads: it hashes the *address*
  -- of an object, not its value, so it is not a function of its argument.  See
  -- `SHARECOMMON_EMULATION.md`.
  -- (§) | lean_float_to_model             : LeanInitPureExtern1OnlyPrim float uint64
  -- (§) | lean_float_of_model             : LeanInitPureExtern1OnlyPrim uint64 float
  -- (§) | lean_float32_to_model           : LeanInitPureExtern1OnlyPrim float32 uint32
  -- (§) | lean_float32_of_model           : LeanInitPureExtern1OnlyPrim uint32 float32

inductive LeanInitPureExtern2OnlyPrim : LeanPrimTy → LeanPrimTy → LeanPrimTy → Type where
  | lean_uint32_dec_eq            : LeanInitPureExtern2OnlyPrim uint32 uint32 bool
  | lean_uint32_dec_lt            : LeanInitPureExtern2OnlyPrim uint32 uint32 bool
  | lean_nat_div                  : LeanInitPureExtern2OnlyPrim nat nat nat
  | lean_nat_dec_lt               : LeanInitPureExtern2OnlyPrim nat nat bool
  | lean_nat_mod_core             : LeanInitPureExtern2OnlyPrim nat nat nat
  | lean_nat_mod                  : LeanInitPureExtern2OnlyPrim nat nat nat
  | lean_nat_sub                  : LeanInitPureExtern2OnlyPrim nat nat nat
  | lean_uint8_dec_lt             : LeanInitPureExtern2OnlyPrim uint8 uint8 bool
  | lean_uint32_dec_le            : LeanInitPureExtern2OnlyPrim uint32 uint32 bool
  | lean_nat_dec_eq               : LeanInitPureExtern2OnlyPrim nat nat bool
  | lean_nat_beq                  : LeanInitPureExtern2OnlyPrim nat nat bool
  | lean_uint8_dec_le             : LeanInitPureExtern2OnlyPrim uint8 uint8 bool
  | lean_nat_ble                  : LeanInitPureExtern2OnlyPrim nat nat bool
  | lean_nat_dec_le               : LeanInitPureExtern2OnlyPrim nat nat bool
  | lean_nat_add                  : LeanInitPureExtern2OnlyPrim nat nat nat
  | lean_uint16_dec_eq            : LeanInitPureExtern2OnlyPrim uint16 uint16 bool
  | lean_string_dec_eq            : LeanInitPureExtern2OnlyPrim string string bool
  | lean_uint64_dec_eq            : LeanInitPureExtern2OnlyPrim uint64 uint64 bool
  -- (†) | lean_name_eq                  : LeanInitPureExtern2OnlyPrim name name bool
  | lean_uint8_dec_eq             : LeanInitPureExtern2OnlyPrim uint8 uint8 bool
  | lean_nat_pow                  : LeanInitPureExtern2OnlyPrim nat nat nat
  | lean_usize_dec_eq             : LeanInitPureExtern2OnlyPrim usize usize bool
  | lean_nat_mul                  : LeanInitPureExtern2OnlyPrim nat nat nat
  -- (†) | lean_byte_array_push          : LeanInitPureExtern2OnlyPrim byteArray uint8 byteArray
  | lean_uint64_mix_hash          : LeanInitPureExtern2OnlyPrim uint64 uint64 uint64
  | lean_int_dec_le               : LeanInitPureExtern2OnlyPrim int int bool
  | lean_int_dec_lt               : LeanInitPureExtern2OnlyPrim int int bool
  | lean_int_dec_eq               : LeanInitPureExtern2OnlyPrim int int bool
  | lean_int_mul                  : LeanInitPureExtern2OnlyPrim int int int
  | lean_int_add                  : LeanInitPureExtern2OnlyPrim int int int
  | lean_int_sub                  : LeanInitPureExtern2OnlyPrim int int int
  | lean_nat_div_exact            : LeanInitPureExtern2OnlyPrim nat nat nat
  | lean_nat_lxor                 : LeanInitPureExtern2OnlyPrim nat nat nat
  | lean_nat_shiftl               : LeanInitPureExtern2OnlyPrim nat nat nat
  | lean_nat_shiftr               : LeanInitPureExtern2OnlyPrim nat nat nat
  | lean_nat_land                 : LeanInitPureExtern2OnlyPrim nat nat nat
  | lean_nat_lor                  : LeanInitPureExtern2OnlyPrim nat nat nat
  | lean_usize_add                : LeanInitPureExtern2OnlyPrim usize usize usize
  | lean_uint32_sub               : LeanInitPureExtern2OnlyPrim uint32 uint32 uint32
  | lean_usize_sub                : LeanInitPureExtern2OnlyPrim usize usize usize
  | lean_uint32_add               : LeanInitPureExtern2OnlyPrim uint32 uint32 uint32
  | lean_usize_dec_le             : LeanInitPureExtern2OnlyPrim usize usize bool
  | lean_usize_dec_lt             : LeanInitPureExtern2OnlyPrim usize usize bool
  | lean_string_utf8_get          : LeanInitPureExtern2OnlyPrim string stringPos char
  | lean_substring_drop           : LeanInitPureExtern2OnlyPrim substring nat substring
  | lean_substring_prev           : LeanInitPureExtern2OnlyPrim substring stringPos stringPos
  | lean_string_append            : LeanInitPureExtern2OnlyPrim string string string
  | lean_string_get_byte_fast     : LeanInitPureExtern2OnlyPrim string nat uint8
  | lean_string_push              : LeanInitPureExtern2OnlyPrim string char string
  | lean_string_isprefixof        : LeanInitPureExtern2OnlyPrim string string bool
  | lean_string_dropright         : LeanInitPureExtern2OnlyPrim string nat string
  | lean_substring_get            : LeanInitPureExtern2OnlyPrim substring stringPos char
  | lean_string_contains          : LeanInitPureExtern2OnlyPrim string char bool
  | lean_string_posof             : LeanInitPureExtern2OnlyPrim string char stringPos
  | lean_string_drop              : LeanInitPureExtern2OnlyPrim string nat string
  | lean_string_utf8_at_end       : LeanInitPureExtern2OnlyPrim string stringPos bool
  | lean_substring_beq            : LeanInitPureExtern2OnlyPrim substring substring bool
  | lean_string_utf8_next         : LeanInitPureExtern2OnlyPrim string stringPos stringPos
  | lean_string_pos_min           : LeanInitPureExtern2OnlyPrim stringPos stringPos stringPos
  | lean_string_pos_sub           : LeanInitPureExtern2OnlyPrim stringPos stringPos stringPos
  | lean_string_offsetofpos       : LeanInitPureExtern2OnlyPrim string stringPos nat
  | lean_strict_or                : LeanInitPureExtern2OnlyPrim bool bool bool
  | lean_strict_and               : LeanInitPureExtern2OnlyPrim bool bool bool
  | lean_int_emod                 : LeanInitPureExtern2OnlyPrim int int int
  | lean_int_div_exact            : LeanInitPureExtern2OnlyPrim int int int
  | lean_int_mod                  : LeanInitPureExtern2OnlyPrim int int int
  | lean_int_ediv                 : LeanInitPureExtern2OnlyPrim int int int
  | lean_int_div                  : LeanInitPureExtern2OnlyPrim int int int
  -- | lean_nat_gcd                  : LeanInitPureExtern2OnlyPrim nat nat nat -- TODO: fromLean should ignore the `@[extern "lean_nat_gcd"]` attribute for `Nat.gcd` function and treat it as ordinary well-foundedly recursive function
  | lean_uint64_shift_left        : LeanInitPureExtern2OnlyPrim uint64 uint64 uint64
  | lean_uint32_mod               : LeanInitPureExtern2OnlyPrim uint32 uint32 uint32
  | lean_usize_land               : LeanInitPureExtern2OnlyPrim usize usize usize
  | lean_usize_mul                : LeanInitPureExtern2OnlyPrim usize usize usize
  | lean_uint64_shift_right       : LeanInitPureExtern2OnlyPrim uint64 uint64 uint64
  | lean_usize_shift_left         : LeanInitPureExtern2OnlyPrim usize usize usize
  | lean_uint16_add               : LeanInitPureExtern2OnlyPrim uint16 uint16 uint16
  | lean_usize_xor                : LeanInitPureExtern2OnlyPrim usize usize usize
  | lean_uint16_lor               : LeanInitPureExtern2OnlyPrim uint16 uint16 uint16
  | lean_uint16_mul               : LeanInitPureExtern2OnlyPrim uint16 uint16 uint16
  | lean_uint16_land              : LeanInitPureExtern2OnlyPrim uint16 uint16 uint16
  | lean_uint8_sub                : LeanInitPureExtern2OnlyPrim uint8 uint8 uint8
  | lean_uint32_div               : LeanInitPureExtern2OnlyPrim uint32 uint32 uint32
  | lean_uint64_add               : LeanInitPureExtern2OnlyPrim uint64 uint64 uint64
  | lean_uint64_lor               : LeanInitPureExtern2OnlyPrim uint64 uint64 uint64
  | lean_uint64_mod               : LeanInitPureExtern2OnlyPrim uint64 uint64 uint64
  | lean_uint8_lor                : LeanInitPureExtern2OnlyPrim uint8 uint8 uint8
  | lean_uint32_shift_right       : LeanInitPureExtern2OnlyPrim uint32 uint32 uint32
  | lean_uint16_xor               : LeanInitPureExtern2OnlyPrim uint16 uint16 uint16
  | lean_usize_lor                : LeanInitPureExtern2OnlyPrim usize usize usize
  | lean_uint8_div                : LeanInitPureExtern2OnlyPrim uint8 uint8 uint8
  | lean_uint16_shift_left        : LeanInitPureExtern2OnlyPrim uint16 uint16 uint16
  | lean_uint16_mod               : LeanInitPureExtern2OnlyPrim uint16 uint16 uint16
  | lean_uint64_div               : LeanInitPureExtern2OnlyPrim uint64 uint64 uint64
  | lean_uint16_dec_lt            : LeanInitPureExtern2OnlyPrim uint16 uint16 bool
  | lean_uint8_shift_right        : LeanInitPureExtern2OnlyPrim uint8 uint8 uint8
  | lean_uint32_lor               : LeanInitPureExtern2OnlyPrim uint32 uint32 uint32
  | lean_uint64_mul               : LeanInitPureExtern2OnlyPrim uint64 uint64 uint64
  | lean_usize_shift_right        : LeanInitPureExtern2OnlyPrim usize usize usize
  | lean_uint64_land              : LeanInitPureExtern2OnlyPrim uint64 uint64 uint64
  | lean_uint8_shift_left         : LeanInitPureExtern2OnlyPrim uint8 uint8 uint8
  | lean_uint16_div               : LeanInitPureExtern2OnlyPrim uint16 uint16 uint16
  | lean_uint8_land               : LeanInitPureExtern2OnlyPrim uint8 uint8 uint8
  | lean_uint64_dec_le            : LeanInitPureExtern2OnlyPrim uint64 uint64 bool
  | lean_uint8_mul                : LeanInitPureExtern2OnlyPrim uint8 uint8 uint8
  | lean_uint64_sub               : LeanInitPureExtern2OnlyPrim uint64 uint64 uint64
  | lean_uint8_add                : LeanInitPureExtern2OnlyPrim uint8 uint8 uint8
  | lean_usize_div                : LeanInitPureExtern2OnlyPrim usize usize usize
  | lean_uint32_xor               : LeanInitPureExtern2OnlyPrim uint32 uint32 uint32
  | lean_uint16_dec_le            : LeanInitPureExtern2OnlyPrim uint16 uint16 bool
  | lean_uint32_shift_left        : LeanInitPureExtern2OnlyPrim uint32 uint32 uint32
  | lean_uint16_sub               : LeanInitPureExtern2OnlyPrim uint16 uint16 uint16
  | lean_uint32_mul               : LeanInitPureExtern2OnlyPrim uint32 uint32 uint32
  | lean_uint32_land              : LeanInitPureExtern2OnlyPrim uint32 uint32 uint32
  | lean_usize_mod                : LeanInitPureExtern2OnlyPrim usize usize usize
  | lean_uint8_mod                : LeanInitPureExtern2OnlyPrim uint8 uint8 uint8
  | lean_uint64_dec_lt            : LeanInitPureExtern2OnlyPrim uint64 uint64 bool
  | lean_uint8_xor                : LeanInitPureExtern2OnlyPrim uint8 uint8 uint8
  | lean_uint16_shift_right       : LeanInitPureExtern2OnlyPrim uint16 uint16 uint16
  | lean_uint64_xor               : LeanInitPureExtern2OnlyPrim uint64 uint64 uint64
  -- (†) | lean_byte_array_fget          : LeanInitPureExtern2OnlyPrim byteArray nat uint8
  -- (†) | lean_byte_array_uget          : LeanInitPureExtern2OnlyPrim byteArray usize uint8
  -- (†) | lean_byte_array_get           : LeanInitPureExtern2OnlyPrim byteArray nat uint8
  | lean_string_get_utf8_byte     : LeanInitPureExtern2OnlyPrim string stringPos uint8
  | lean_string_get_byte_fast_raw : LeanInitPureExtern2OnlyPrim string stringPos uint8
  | lean_string_append_defs       : LeanInitPureExtern2OnlyPrim string string string
  | lean_string_utf8_next_basic   : LeanInitPureExtern2OnlyPrim string stringPos stringPos
  | lean_string_pos_raw_next      : LeanInitPureExtern2OnlyPrim string stringPos stringPos
  | lean_string_pos_raw_get       : LeanInitPureExtern2OnlyPrim string stringPos char
  | lean_string_get_basic         : LeanInitPureExtern2OnlyPrim string stringPos char
  | lean_string_pos_raw_prev      : LeanInitPureExtern2OnlyPrim string stringPos stringPos
  | lean_string_prev              : LeanInitPureExtern2OnlyPrim string stringPos stringPos
  | lean_string_next_fast         : LeanInitPureExtern2OnlyPrim string stringPos stringPos
  | lean_string_pos_raw_next_fast : LeanInitPureExtern2OnlyPrim string stringPos stringPos
  | lean_string_pos_next          : LeanInitPureExtern2OnlyPrim string stringPos stringPos
  | lean_string_at_end_basic      : LeanInitPureExtern2OnlyPrim string stringPos bool
  | lean_string_pos_raw_at_end    : LeanInitPureExtern2OnlyPrim string stringPos bool
  | lean_string_pos_raw_get_bang  : LeanInitPureExtern2OnlyPrim string stringPos char
  | lean_string_get_bang          : LeanInitPureExtern2OnlyPrim string stringPos char
  | lean_string_decode_char       : LeanInitPureExtern2OnlyPrim string nat char
  | lean_string_get_fast          : LeanInitPureExtern2OnlyPrim string stringPos char
  | lean_string_pos_raw_get_fast  : LeanInitPureExtern2OnlyPrim string stringPos char
  | lean_string_is_valid_pos      : LeanInitPureExtern2OnlyPrim string stringPos bool
  | lean_string_dec_lt            : LeanInitPureExtern2OnlyPrim string string bool
  | lean_int8_add                 : LeanInitPureExtern2OnlyPrim int8 int8 int8
  | lean_int16_dec_le             : LeanInitPureExtern2OnlyPrim int16 int16 bool
  | lean_int32_land               : LeanInitPureExtern2OnlyPrim int32 int32 int32
  | lean_int8_div                 : LeanInitPureExtern2OnlyPrim int8 int8 int8
  | lean_int32_mul                : LeanInitPureExtern2OnlyPrim int32 int32 int32
  | lean_int64_sub                : LeanInitPureExtern2OnlyPrim int64 int64 int64
  | lean_int16_shift_right        : LeanInitPureExtern2OnlyPrim int16 int16 int16
  | lean_int64_xor                : LeanInitPureExtern2OnlyPrim int64 int64 int64
  | lean_int32_dec_le             : LeanInitPureExtern2OnlyPrim int32 int32 bool
  | lean_isize_xor                : LeanInitPureExtern2OnlyPrim isize isize isize
  | lean_isize_shift_left         : LeanInitPureExtern2OnlyPrim isize isize isize
  | lean_int64_mul                : LeanInitPureExtern2OnlyPrim int64 int64 int64
  | lean_int32_sub                : LeanInitPureExtern2OnlyPrim int32 int32 int32
  | lean_int64_land               : LeanInitPureExtern2OnlyPrim int64 int64 int64
  | lean_int8_shift_right         : LeanInitPureExtern2OnlyPrim int8 int8 int8
  | lean_int64_lor                : LeanInitPureExtern2OnlyPrim int64 int64 int64
  | lean_int16_div                : LeanInitPureExtern2OnlyPrim int16 int16 int16
  | lean_isize_mod                : LeanInitPureExtern2OnlyPrim isize isize isize
  | lean_int8_mod                 : LeanInitPureExtern2OnlyPrim int8 int8 int8
  | lean_isize_shift_right        : LeanInitPureExtern2OnlyPrim isize isize isize
  | lean_int8_shift_left          : LeanInitPureExtern2OnlyPrim int8 int8 int8
  | lean_int16_dec_lt             : LeanInitPureExtern2OnlyPrim int16 int16 bool
  | lean_int8_xor                 : LeanInitPureExtern2OnlyPrim int8 int8 int8
  | lean_int32_dec_eq             : LeanInitPureExtern2OnlyPrim int32 int32 bool
  | lean_int16_mod                : LeanInitPureExtern2OnlyPrim int16 int16 int16
  | lean_isize_div                : LeanInitPureExtern2OnlyPrim isize isize isize
  | lean_int16_dec_eq             : LeanInitPureExtern2OnlyPrim int16 int16 bool
  | lean_isize_add                : LeanInitPureExtern2OnlyPrim isize isize isize
  | lean_int32_dec_lt             : LeanInitPureExtern2OnlyPrim int32 int32 bool
  | lean_isize_lor                : LeanInitPureExtern2OnlyPrim isize isize isize
  | lean_int64_mod                : LeanInitPureExtern2OnlyPrim int64 int64 int64
  | lean_int64_shift_left         : LeanInitPureExtern2OnlyPrim int64 int64 int64
  | lean_isize_land               : LeanInitPureExtern2OnlyPrim isize isize isize
  | lean_isize_mul                : LeanInitPureExtern2OnlyPrim isize isize isize
  | lean_int64_dec_lt             : LeanInitPureExtern2OnlyPrim int64 int64 bool
  | lean_isize_dec_le             : LeanInitPureExtern2OnlyPrim isize isize bool
  | lean_int8_dec_eq              : LeanInitPureExtern2OnlyPrim int8 int8 bool
  | lean_int32_xor                : LeanInitPureExtern2OnlyPrim int32 int32 int32
  | lean_int32_shift_left         : LeanInitPureExtern2OnlyPrim int32 int32 int32
  | lean_isize_sub                : LeanInitPureExtern2OnlyPrim isize isize isize
  | lean_int16_land               : LeanInitPureExtern2OnlyPrim int16 int16 int16
  | lean_int32_shift_right        : LeanInitPureExtern2OnlyPrim int32 int32 int32
  | lean_int16_mul                : LeanInitPureExtern2OnlyPrim int16 int16 int16
  | lean_int16_shift_left         : LeanInitPureExtern2OnlyPrim int16 int16 int16
  | lean_int16_xor                : LeanInitPureExtern2OnlyPrim int16 int16 int16
  | lean_int8_dec_lt              : LeanInitPureExtern2OnlyPrim int8 int8 bool
  | lean_int64_dec_eq             : LeanInitPureExtern2OnlyPrim int64 int64 bool
  | lean_int64_dec_le             : LeanInitPureExtern2OnlyPrim int64 int64 bool
  | lean_int32_add                : LeanInitPureExtern2OnlyPrim int32 int32 int32
  | lean_isize_dec_lt             : LeanInitPureExtern2OnlyPrim isize isize bool
  | lean_int32_lor                : LeanInitPureExtern2OnlyPrim int32 int32 int32
  | lean_int32_mod                : LeanInitPureExtern2OnlyPrim int32 int32 int32
  | lean_int64_add                : LeanInitPureExtern2OnlyPrim int64 int64 int64
  | lean_int8_sub                 : LeanInitPureExtern2OnlyPrim int8 int8 int8
  | lean_int16_lor                : LeanInitPureExtern2OnlyPrim int16 int16 int16
  | lean_int64_div                : LeanInitPureExtern2OnlyPrim int64 int64 int64
  | lean_isize_dec_eq             : LeanInitPureExtern2OnlyPrim isize isize bool
  | lean_int16_add                : LeanInitPureExtern2OnlyPrim int16 int16 int16
  | lean_int8_dec_le              : LeanInitPureExtern2OnlyPrim int8 int8 bool
  | lean_int8_mul                 : LeanInitPureExtern2OnlyPrim int8 int8 int8
  | lean_int8_land                : LeanInitPureExtern2OnlyPrim int8 int8 int8
  | lean_int32_div                : LeanInitPureExtern2OnlyPrim int32 int32 int32
  | lean_int16_sub                : LeanInitPureExtern2OnlyPrim int16 int16 int16
  | lean_int8_lor                 : LeanInitPureExtern2OnlyPrim int8 int8 int8
  | lean_int64_shift_right        : LeanInitPureExtern2OnlyPrim int64 int64 int64
  | lean_slice_dec_lt             : LeanInitPureExtern2OnlyPrim stringSlice stringSlice bool
  | lean_float_div                : LeanInitPureExtern2OnlyPrim float float float
  | lean_float_beq                : LeanInitPureExtern2OnlyPrim float float bool
  | lean_float_decLe              : LeanInitPureExtern2OnlyPrim float float bool
  | lean_float_le                 : LeanInitPureExtern2OnlyPrim float float bool
  | lean_float_decLt              : LeanInitPureExtern2OnlyPrim float float bool
  | lean_float_lt                 : LeanInitPureExtern2OnlyPrim float float bool
  | atan2                         : LeanInitPureExtern2OnlyPrim float float float
  | lean_float_mul                : LeanInitPureExtern2OnlyPrim float float float
  | pow                           : LeanInitPureExtern2OnlyPrim float float float
  | lean_float_scaleb             : LeanInitPureExtern2OnlyPrim float int64 float
  | lean_float_add                : LeanInitPureExtern2OnlyPrim float float float
  | lean_float_sub                : LeanInitPureExtern2OnlyPrim float float float
  -- (†) | lean_float_array_get          : LeanInitPureExtern2OnlyPrim floatArray nat float
  -- (†) | lean_float_array_uget         : LeanInitPureExtern2OnlyPrim floatArray usize float
  -- (†) | lean_float_array_fget         : LeanInitPureExtern2OnlyPrim floatArray nat float
  -- (†) | lean_float_array_push         : LeanInitPureExtern2OnlyPrim floatArray float floatArray
  | lean_float32_div              : LeanInitPureExtern2OnlyPrim float32 float32 float32
  | lean_float32_le               : LeanInitPureExtern2OnlyPrim float32 float32 bool
  | lean_float32_decLe            : LeanInitPureExtern2OnlyPrim float32 float32 bool
  | lean_float32_sub              : LeanInitPureExtern2OnlyPrim float32 float32 float32
  | powf                          : LeanInitPureExtern2OnlyPrim float32 float32 float32
  | lean_float32_beq              : LeanInitPureExtern2OnlyPrim float32 float32 bool
  | atan2f                        : LeanInitPureExtern2OnlyPrim float32 float32 float32
  | lean_float32_add              : LeanInitPureExtern2OnlyPrim float32 float32 float32
  | lean_float32_scaleb           : LeanInitPureExtern2OnlyPrim float32 int64 float32
  | lean_float32_mul              : LeanInitPureExtern2OnlyPrim float32 float32 float32
  | lean_float32_lt               : LeanInitPureExtern2OnlyPrim float32 float32 bool
  | lean_float32_decLt            : LeanInitPureExtern2OnlyPrim float32 float32 bool
  -- | lean_sharecommon_eq           : LeanInitPureExtern2OnlyPrim shareCommonObject shareCommonObject bool
  -- Commented out with the `shareCommonObject` handle it reads: it is pointer equality,
  -- not a function of the values.  See `SHARECOMMON_EMULATION.md`.
  | lean_string_uget_byte_fast    : LeanInitPureExtern2OnlyPrim string usize uint8
  -- (†) | lean_sarray_beq               : LeanInitPureExtern2OnlyPrim byteArray byteArray bool
  -- (†) | lean_sarray_dec_eq            : LeanInitPureExtern2OnlyPrim byteArray byteArray bool
  -- (†) | lean_string_compare           : LeanInitPureExtern2OnlyPrim string string ordering

inductive LeanInitPureExtern3OnlyPrim : LeanPrimTy → LeanPrimTy → LeanPrimTy → LeanPrimTy → Type where
  | lean_substring_extract         : LeanInitPureExtern3OnlyPrim substring stringPos stringPos substring
  | lean_string_pushn              : LeanInitPureExtern3OnlyPrim string char nat string
  | lean_string_utf8_extract       : LeanInitPureExtern3OnlyPrim string stringPos stringPos string
  | lean_string_utf8_extract_fast  : LeanInitPureExtern3OnlyPrim string stringPos stringPos string
  | lean_string_utf8_extract_basic : LeanInitPureExtern3OnlyPrim string stringPos stringPos string
  | lean_string_pos_raw_set        : LeanInitPureExtern3OnlyPrim string stringPos char string
  | lean_string_pos_set            : LeanInitPureExtern3OnlyPrim string stringPos char string
  | lean_string_set                : LeanInitPureExtern3OnlyPrim string stringPos char string

inductive LeanInitPureExtern5 : LeanPrimTy → LeanPrimTy → LeanPrimTy → LeanPrimTy → LeanPrimTy → LeanPrimTy → Type where
  | lean_string_memcmp : LeanInitPureExtern5 string string stringPos stringPos stringPos bool

---- Now only complex

section

variable {X : Type}
  [Coe LeanPrimTy X]
  [Coe (LeanPrimTyCovariant LeanPrimTy) X]
  [Coe (LeanPrimTyCovariant X) X]
  (option : X → X)
  (fn1 : LeanPrimTy → LeanPrimTy → X)
  (prod : LeanPrimTy → LeanPrimTy → X)

inductive LeanInitPureExtern1 : X → X → Type where
  | lean_sorry                     : (α : X) → LeanInitPureExtern1 bool α
  | lean_array_get_size            : (α : X) → LeanInitPureExtern1 (array α) nat
  | lean_array_to_list             : (α : X) → LeanInitPureExtern1 (array α) (list α)
  | lean_empty_array_with_capacity : (α : X) → LeanInitPureExtern1 nat (array α)
  | lean_array_mk_empty            : (α : X) → LeanInitPureExtern1 nat (array α)
  | lean_panic_fn_borrowed         : (α : X) → LeanInitPureExtern1 string α
  | lean_array_mk                  : (α : X) → LeanInitPureExtern1 (list α) (array α)
  | lean_thunk_pure                : (α : X) → LeanInitPureExtern1 α (thunk α)
  | lean_mk_thunk                  : (α : X) → LeanInitPureExtern1 (lazy α) (thunk α)
  | lean_task_get_own              : (α : X) → LeanInitPureExtern1 (task α) α
  | lean_task_pure                 : (α : X) → LeanInitPureExtern1 α (task α)
  | lean_thunk_get_own             : (α : X) → LeanInitPureExtern1 (thunk α) α
  | lean_ptr_addr                  : (α : X) → LeanInitPureExtern1 α usize
  | lean_dbg_stack_trace           : (α : X) → LeanInitPureExtern1 (lazy α) α
  | lean_is_exclusive_obj          : (α : X) → LeanInitPureExtern1 α bool
  | lean_array_pop                 : (α : X) → LeanInitPureExtern1 (array α) (array α)
  | lean_array_size                : (α : X) → LeanInitPureExtern1 (array α) usize
  | lean_io_promise_result_opt     : (α : X) → LeanInitPureExtern1 (promise α) (task (option α))
  | lean_option_get_or_block       : (α : X) → LeanInitPureExtern1 (option α) α
  | lean_sharecommon_quick         : (α : X) → LeanInitPureExtern1 α α
  -- (†) | lean_byte_array_mk             : LeanInitPureExtern1 (array uint8) byteArray
  -- (†) | lean_byte_array_data           : LeanInitPureExtern1 byteArray (array uint8)
  | lean_string_mk                 : LeanInitPureExtern1 (list char) string
  | lean_string_mk_def             : LeanInitPureExtern1 (list char) string
  | lean_string_data               : LeanInitPureExtern1 string (list char)
  | lean_string_to_list            : LeanInitPureExtern1 string (list char)
  | lean_float_frexp               : LeanInitPureExtern1 float (prod float int64)
  -- (†) | lean_float_array_data          : LeanInitPureExtern1 floatArray (array float)
  -- (†) | lean_float_array_mk            : LeanInitPureExtern1 (array float) floatArray
  | lean_float32_frexp             : LeanInitPureExtern1 float32 (prod float32 int64)
  | lean_is_scalar                 : (α : X) → LeanInitPureExtern1 α bool

end

section

variable {X : Type}
  [Coe LeanPrimTy X]
  [Coe (LeanPrimTyCovariant LeanPrimTy) X]
  [Coe (LeanPrimTyCovariant X) X]
  (option : X → X)
  (fn1 : LeanPrimTy → LeanPrimTy → X)
  (prodX : X → LeanPrimTy → X)

inductive LeanInitPureExtern2 : X → X → X → Type where
  | lean_array_get_borrowed     : (α : X) → LeanInitPureExtern2 (array α) nat α
  | lean_array_push             : (α : X) → LeanInitPureExtern2 (array α) α (array α)
  | lean_array_fget_borrowed    : (α : X) → LeanInitPureExtern2 (array α) nat α
  | lean_array_get              : (α : X) → LeanInitPureExtern2 (array α) nat α
  | lean_array_fget             : (α : X) → LeanInitPureExtern2 (array α) nat α
  | lean_task_spawn             : (α : X) → LeanInitPureExtern2 (lazy α) nat (task α)
  | lean_dbg_sleep              : (α : X) → LeanInitPureExtern2 uint32 (lazy α) α
  | lean_dbg_trace              : (α : X) → LeanInitPureExtern2 string (lazy α) α
  | lean_dbg_trace_if_shared    : (α : X) → LeanInitPureExtern2 string α α
  | lean_array_uget             : (α : X) → LeanInitPureExtern2 (array α) usize α
  | lean_mk_array               : (α : X) → LeanInitPureExtern2 nat α (array α)
  -- | lean_state_sharecommon      : (α : X) → LeanInitPureExtern2 shareCommonState α (prodX α shareCommonState)
  -- Commented out with the `shareCommonState` handle it threads: with the interning
  -- table erased it is `fun s a => (a, s)`, so it has nothing left to do.  See
  -- `SHARECOMMON_EMULATION.md`.
  | lean_substring_takewhile    : LeanInitPureExtern2 substring (fn1 char bool) substring
  | lean_substring_all          : LeanInitPureExtern2 substring (fn1 char bool) bool
  | lean_string_intercalate     : LeanInitPureExtern2 string (list string) string
  | lean_string_any             : LeanInitPureExtern2 string (fn1 char bool) bool
  | lean_string_pos_raw_get_opt : LeanInitPureExtern2 string stringPos (option char)
  | lean_string_get_opt         : LeanInitPureExtern2 string stringPos (option char)
  | lean_array_uget_borrowed    : (α : X) → LeanInitPureExtern2 (array α) usize α

end section

section

variable {X : Type}
  [Coe LeanPrimTy X]
  [Coe (LeanPrimTyCovariant X) X]
  (fn1 : LeanPrimTy → LeanPrimTy → X)
  (fn2 : LeanPrimTy → LeanPrimTy → LeanPrimTy → X)
  (byteArray : X)
  (floatArray : X)

inductive LeanInitPureExtern3 : X → X → X → X → Type where
  | lean_array_set        : (α : X) → LeanInitPureExtern3 (array α) nat α (array α)
  | lean_array_fset       : (α : X) → LeanInitPureExtern3 (array α) nat α (array α)
  | lean_array_fswap      : (α : X) → LeanInitPureExtern3 (array α) nat nat (array α)
  | lean_array_swap       : (α : X) → LeanInitPureExtern3 (array α) nat nat (array α)
  | lean_array_uset       : (α : X) → LeanInitPureExtern3 (array α) usize α (array α)
  | lean_string_foldl     : LeanInitPureExtern3 (fn2 string char string) string string string
  | lean_string_nextwhile : LeanInitPureExtern3 string (fn1 char bool) stringPos stringPos
  | lean_byte_array_set            : LeanInitPureExtern3 byteArray nat uint8 byteArray
  | lean_byte_array_uset           : LeanInitPureExtern3 byteArray usize uint8 byteArray
  | lean_byte_array_fset           : LeanInitPureExtern3 byteArray nat uint8 byteArray
  | lean_float_array_fset          : LeanInitPureExtern3 floatArray nat float floatArray
  | lean_float_array_uset          : LeanInitPureExtern3 floatArray usize float floatArray
  | lean_float_array_set           : LeanInitPureExtern3 floatArray nat float floatArray

end section

section

variable {X : Type}
  [Coe LeanPrimTy X]
  [Coe (LeanPrimTyCovariant X) X]
  (fn1 : X → X → X)

open LeanPrimTy
open LeanPrimTyCovariant

inductive LeanInitPureExtern4 : X → X → X → X → X → Type where
  | lean_task_map  : (α : X) → (β : X) → LeanInitPureExtern4 (fn1 α β) (task α) nat bool (task β)
  | lean_task_bind : (α : X) → (β : X) → LeanInitPureExtern4 (task α) (fn1 α (task β)) nat bool (task β)

end section

section

variable {X : Type}
  [Coe LeanPrimTy X]
  (byteArray : X)

open LeanPrimTy

inductive LeanInitPureExtern6 : X → LeanPrimTy → X → LeanPrimTy → LeanPrimTy → LeanPrimTy → X → Type where
  | lean_byte_array_copy_slice : LeanInitPureExtern6 byteArray nat byteArray nat nat bool byteArray

end section
