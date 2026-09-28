module

public import JsTerm.Ops.Op

@[expose] public section

set_option autoImplicit false

/-!
# The operations of the externs of the floating-point numbers

**Generated** by `scripts/gen_js_ops.py`; do not edit.

The candidates (`JsOp.Cand`) of every extern of the floating-point numbers (`lean_float_*`, `lean_float32_*` and the C functions of `math.h`: `sin`, `sinf`, …): its
operations at their signatures, for the lookup (`JsOp.lookup`, `JsTerm.Ops.Lookup`).
-/

namespace MoreJs

namespace JsOp

/-- The operations of `acos`. -/
def «cands_acos» : List Cand :=
  [⟨_, _, _, _, .inlined .float__acos⟩]

/-- The operations of `acosf`. -/
def «cands_acosf» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__acosf⟩]

/-- The operations of `acosh`. -/
def «cands_acosh» : List Cand :=
  [⟨_, _, _, _, .inlined .float__acosh⟩]

/-- The operations of `acoshf`. -/
def «cands_acoshf» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__acoshf⟩]

/-- The operations of `asin`. -/
def «cands_asin» : List Cand :=
  [⟨_, _, _, _, .inlined .float__asin⟩]

/-- The operations of `asinf`. -/
def «cands_asinf» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__asinf⟩]

/-- The operations of `asinh`. -/
def «cands_asinh» : List Cand :=
  [⟨_, _, _, _, .inlined .float__asinh⟩]

/-- The operations of `asinhf`. -/
def «cands_asinhf» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__asinhf⟩]

/-- The operations of `atan`. -/
def «cands_atan» : List Cand :=
  [⟨_, _, _, _, .inlined .float__atan⟩]

/-- The operations of `atan2`. -/
def «cands_atan2» : List Cand :=
  [⟨_, _, _, _, .inlined .float__atan2⟩]

/-- The operations of `atan2f`. -/
def «cands_atan2f» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__atan2f⟩]

/-- The operations of `atanf`. -/
def «cands_atanf» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__atanf⟩]

/-- The operations of `atanh`. -/
def «cands_atanh» : List Cand :=
  [⟨_, _, _, _, .inlined .float__atanh⟩]

/-- The operations of `atanhf`. -/
def «cands_atanhf» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__atanhf⟩]

/-- The operations of `cbrt`. -/
def «cands_cbrt» : List Cand :=
  [⟨_, _, _, _, .inlined .float__cbrt⟩]

/-- The operations of `cbrtf`. -/
def «cands_cbrtf» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__cbrtf⟩]

/-- The operations of `ceil`. -/
def «cands_ceil» : List Cand :=
  [⟨_, _, _, _, .inlined .float__ceil⟩]

/-- The operations of `ceilf`. -/
def «cands_ceilf» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__ceilf⟩]

/-- The operations of `cos`. -/
def «cands_cos» : List Cand :=
  [⟨_, _, _, _, .inlined .float__cos⟩]

/-- The operations of `cosf`. -/
def «cands_cosf» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__cosf⟩]

/-- The operations of `cosh`. -/
def «cands_cosh» : List Cand :=
  [⟨_, _, _, _, .inlined .float__cosh⟩]

/-- The operations of `coshf`. -/
def «cands_coshf» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__coshf⟩]

/-- The operations of `exp`. -/
def «cands_exp» : List Cand :=
  [⟨_, _, _, _, .inlined .float__exp⟩]

/-- The operations of `exp2`. -/
def «cands_exp2» : List Cand :=
  [⟨_, _, _, _, .inlined .float__exp2⟩]

/-- The operations of `exp2f`. -/
def «cands_exp2f» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__exp2f⟩]

/-- The operations of `expf`. -/
def «cands_expf» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__expf⟩]

/-- The operations of `fabs`. -/
def «cands_fabs» : List Cand :=
  [⟨_, _, _, _, .inlined .float__fabs⟩]

/-- The operations of `fabsf`. -/
def «cands_fabsf» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__fabsf⟩]

/-- The operations of `floor`. -/
def «cands_floor» : List Cand :=
  [⟨_, _, _, _, .inlined .float__floor⟩]

/-- The operations of `floorf`. -/
def «cands_floorf» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__floorf⟩]

/-- The operations of `lean_float32_add`. -/
def «cands_lean_float32_add» : List Cand :=
  [⟨_, _, _, _, .imported .float32__lean_float32_add⟩]

/-- The operations of `lean_float32_beq`. -/
def «cands_lean_float32_beq» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__lean_float32_beq⟩]

/-- The operations of `lean_float32_decLe__Float32_decLe`. -/
def «cands_lean_float32_decLe__Float32_decLe» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__lean_float32_decLe__Float32_decLe⟩]

/-- The operations of `lean_float32_decLe__Float32_le`. -/
def «cands_lean_float32_decLe__Float32_le» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__lean_float32_decLe__Float32_le⟩]

/-- The operations of `lean_float32_decLt__Float32_decLt`. -/
def «cands_lean_float32_decLt__Float32_decLt» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__lean_float32_decLt__Float32_decLt⟩]

/-- The operations of `lean_float32_decLt__Float32_lt`. -/
def «cands_lean_float32_decLt__Float32_lt» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__lean_float32_decLt__Float32_lt⟩]

/-- The operations of `lean_float32_div`. -/
def «cands_lean_float32_div» : List Cand :=
  [⟨_, _, _, _, .imported .float32__lean_float32_div⟩]

/-- The operations of `lean_float32_frexp`. -/
def «cands_lean_float32_frexp» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_float32_frexp⟩, ⟨_, _, _, _, .imported .int53__lean_float32_frexp⟩]

/-- The operations of `lean_float32_isfinite`. -/
def «cands_lean_float32_isfinite» : List Cand :=
  [⟨_, _, _, _, .imported .float32__lean_float32_isfinite⟩]

/-- The operations of `lean_float32_isinf`. -/
def «cands_lean_float32_isinf» : List Cand :=
  [⟨_, _, _, _, .imported .float32__lean_float32_isinf⟩]

/-- The operations of `lean_float32_isnan`. -/
def «cands_lean_float32_isnan» : List Cand :=
  [⟨_, _, _, _, .imported .float32__lean_float32_isnan⟩]

/-- The operations of `lean_float32_mul`. -/
def «cands_lean_float32_mul» : List Cand :=
  [⟨_, _, _, _, .imported .float32__lean_float32_mul⟩]

/-- The operations of `lean_float32_negate`. -/
def «cands_lean_float32_negate» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__lean_float32_negate⟩]

/-- The operations of `lean_float32_of_bits__Float32_ofBits`. -/
def «cands_lean_float32_of_bits__Float32_ofBits» : List Cand :=
  [⟨_, _, _, _, .imported .uint32__lean_float32_of_bits__Float32_ofBits⟩]

/-- The operations of `lean_float32_of_bits__Float32_ofModel`. -/
def «cands_lean_float32_of_bits__Float32_ofModel» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__lean_float32_of_bits__Float32_ofModel⟩]

/-- The operations of `lean_float32_scaleb`. -/
def «cands_lean_float32_scaleb» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_float32_scaleb⟩, ⟨_, _, _, _, .imported .int53__lean_float32_scaleb⟩]

/-- The operations of `lean_float32_sub`. -/
def «cands_lean_float32_sub» : List Cand :=
  [⟨_, _, _, _, .imported .float32__lean_float32_sub⟩]

/-- The operations of `lean_float32_to_bits__Float32_toBits`. -/
def «cands_lean_float32_to_bits__Float32_toBits» : List Cand :=
  [⟨_, _, _, _, .imported .float32__lean_float32_to_bits__Float32_toBits⟩]

/-- The operations of `lean_float32_to_bits__Float32_toModel`. -/
def «cands_lean_float32_to_bits__Float32_toModel» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__lean_float32_to_bits__Float32_toModel⟩]

/-- The operations of `lean_float32_to_float`. -/
def «cands_lean_float32_to_float» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__lean_float32_to_float⟩]

/-- The operations of `lean_float32_to_int16`. -/
def «cands_lean_float32_to_int16» : List Cand :=
  [⟨_, _, _, _, .imported .float32__lean_float32_to_int16⟩]

/-- The operations of `lean_float32_to_int32`. -/
def «cands_lean_float32_to_int32» : List Cand :=
  [⟨_, _, _, _, .imported .float32__lean_float32_to_int32⟩]

/-- The operations of `lean_float32_to_int64`. -/
def «cands_lean_float32_to_int64» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_float32_to_int64⟩, ⟨_, _, _, _, .imported .int53__lean_float32_to_int64⟩]

/-- The operations of `lean_float32_to_int8`. -/
def «cands_lean_float32_to_int8» : List Cand :=
  [⟨_, _, _, _, .imported .float32__lean_float32_to_int8⟩]

/-- The operations of `lean_float32_to_string`. -/
def «cands_lean_float32_to_string» : List Cand :=
  [⟨_, _, _, _, .imported .float32__lean_float32_to_string⟩]

/-- The operations of `lean_float32_to_uint16`. -/
def «cands_lean_float32_to_uint16» : List Cand :=
  [⟨_, _, _, _, .imported .float32__lean_float32_to_uint16⟩]

/-- The operations of `lean_float32_to_uint32`. -/
def «cands_lean_float32_to_uint32» : List Cand :=
  [⟨_, _, _, _, .imported .float32__lean_float32_to_uint32⟩]

/-- The operations of `lean_float32_to_uint64`. -/
def «cands_lean_float32_to_uint64» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_float32_to_uint64⟩, ⟨_, _, _, _, .imported .uint53__lean_float32_to_uint64⟩]

/-- The operations of `lean_float32_to_uint8`. -/
def «cands_lean_float32_to_uint8» : List Cand :=
  [⟨_, _, _, _, .imported .float32__lean_float32_to_uint8⟩]

/-- The operations of `lean_float_add`. -/
def «cands_lean_float_add» : List Cand :=
  [⟨_, _, _, _, .inlined .float__lean_float_add⟩]

/-- The operations of `lean_float_beq`. -/
def «cands_lean_float_beq» : List Cand :=
  [⟨_, _, _, _, .inlined .float__lean_float_beq⟩]

/-- The operations of `lean_float_decLe__Float_decLe`. -/
def «cands_lean_float_decLe__Float_decLe» : List Cand :=
  [⟨_, _, _, _, .inlined .float__lean_float_decLe__Float_decLe⟩]

/-- The operations of `lean_float_decLe__Float_le`. -/
def «cands_lean_float_decLe__Float_le» : List Cand :=
  [⟨_, _, _, _, .inlined .float__lean_float_decLe__Float_le⟩]

/-- The operations of `lean_float_decLt__Float_decLt`. -/
def «cands_lean_float_decLt__Float_decLt» : List Cand :=
  [⟨_, _, _, _, .inlined .float__lean_float_decLt__Float_decLt⟩]

/-- The operations of `lean_float_decLt__Float_lt`. -/
def «cands_lean_float_decLt__Float_lt» : List Cand :=
  [⟨_, _, _, _, .inlined .float__lean_float_decLt__Float_lt⟩]

/-- The operations of `lean_float_div`. -/
def «cands_lean_float_div» : List Cand :=
  [⟨_, _, _, _, .inlined .float__lean_float_div⟩]

/-- The operations of `lean_float_frexp`. -/
def «cands_lean_float_frexp» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_float_frexp⟩, ⟨_, _, _, _, .imported .int53__lean_float_frexp⟩]

/-- The operations of `lean_float_isfinite`. -/
def «cands_lean_float_isfinite» : List Cand :=
  [⟨_, _, _, _, .imported .float__lean_float_isfinite⟩]

/-- The operations of `lean_float_isinf`. -/
def «cands_lean_float_isinf» : List Cand :=
  [⟨_, _, _, _, .imported .float__lean_float_isinf⟩]

/-- The operations of `lean_float_isnan`. -/
def «cands_lean_float_isnan» : List Cand :=
  [⟨_, _, _, _, .imported .float__lean_float_isnan⟩]

/-- The operations of `lean_float_mul`. -/
def «cands_lean_float_mul» : List Cand :=
  [⟨_, _, _, _, .inlined .float__lean_float_mul⟩]

/-- The operations of `lean_float_negate`. -/
def «cands_lean_float_negate» : List Cand :=
  [⟨_, _, _, _, .inlined .float__lean_float_negate⟩]

/-- The operations of `lean_float_of_bits__Float_ofBits`. -/
def «cands_lean_float_of_bits__Float_ofBits» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_float_of_bits__Float_ofBits⟩, ⟨_, _, _, _, .imported .uint53__lean_float_of_bits__Float_ofBits⟩]

/-- The operations of `lean_float_of_bits__Float_ofModel`. -/
def «cands_lean_float_of_bits__Float_ofModel» : List Cand :=
  [⟨_, _, _, _, .inlined .float__lean_float_of_bits__Float_ofModel⟩]

/-- The operations of `lean_float_scaleb`. -/
def «cands_lean_float_scaleb» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_float_scaleb⟩, ⟨_, _, _, _, .imported .int53__lean_float_scaleb⟩]

/-- The operations of `lean_float_sub`. -/
def «cands_lean_float_sub» : List Cand :=
  [⟨_, _, _, _, .inlined .float__lean_float_sub⟩]

/-- The operations of `lean_float_to_bits__Float_toBits`. -/
def «cands_lean_float_to_bits__Float_toBits» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_float_to_bits__Float_toBits⟩, ⟨_, _, _, _, .imported .uint53__lean_float_to_bits__Float_toBits⟩]

/-- The operations of `lean_float_to_bits__Float_toModel`. -/
def «cands_lean_float_to_bits__Float_toModel» : List Cand :=
  [⟨_, _, _, _, .inlined .float__lean_float_to_bits__Float_toModel⟩]

/-- The operations of `lean_float_to_float32`. -/
def «cands_lean_float_to_float32» : List Cand :=
  [⟨_, _, _, _, .imported .float__lean_float_to_float32⟩]

/-- The operations of `lean_float_to_int16`. -/
def «cands_lean_float_to_int16» : List Cand :=
  [⟨_, _, _, _, .imported .float__lean_float_to_int16⟩]

/-- The operations of `lean_float_to_int32`. -/
def «cands_lean_float_to_int32» : List Cand :=
  [⟨_, _, _, _, .imported .float__lean_float_to_int32⟩]

/-- The operations of `lean_float_to_int64`. -/
def «cands_lean_float_to_int64» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_float_to_int64⟩, ⟨_, _, _, _, .imported .int53__lean_float_to_int64⟩]

/-- The operations of `lean_float_to_int8`. -/
def «cands_lean_float_to_int8» : List Cand :=
  [⟨_, _, _, _, .imported .float__lean_float_to_int8⟩]

/-- The operations of `lean_float_to_string`. -/
def «cands_lean_float_to_string» : List Cand :=
  [⟨_, _, _, _, .imported .float__lean_float_to_string⟩]

/-- The operations of `lean_float_to_uint16`. -/
def «cands_lean_float_to_uint16» : List Cand :=
  [⟨_, _, _, _, .imported .float__lean_float_to_uint16⟩]

/-- The operations of `lean_float_to_uint32`. -/
def «cands_lean_float_to_uint32» : List Cand :=
  [⟨_, _, _, _, .imported .float__lean_float_to_uint32⟩]

/-- The operations of `lean_float_to_uint64`. -/
def «cands_lean_float_to_uint64» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_float_to_uint64⟩, ⟨_, _, _, _, .imported .uint53__lean_float_to_uint64⟩]

/-- The operations of `lean_float_to_uint8`. -/
def «cands_lean_float_to_uint8» : List Cand :=
  [⟨_, _, _, _, .imported .float__lean_float_to_uint8⟩]

/-- The operations of `log`. -/
def «cands_log» : List Cand :=
  [⟨_, _, _, _, .inlined .float__log⟩]

/-- The operations of `log10`. -/
def «cands_log10» : List Cand :=
  [⟨_, _, _, _, .inlined .float__log10⟩]

/-- The operations of `log10f`. -/
def «cands_log10f» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__log10f⟩]

/-- The operations of `log2`. -/
def «cands_log2» : List Cand :=
  [⟨_, _, _, _, .inlined .float__log2⟩]

/-- The operations of `log2f`. -/
def «cands_log2f» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__log2f⟩]

/-- The operations of `logf`. -/
def «cands_logf» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__logf⟩]

/-- The operations of `pow`. -/
def «cands_pow» : List Cand :=
  [⟨_, _, _, _, .inlined .float__pow⟩]

/-- The operations of `powf`. -/
def «cands_powf» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__powf⟩]

/-- The operations of `round`. -/
def «cands_round» : List Cand :=
  [⟨_, _, _, _, .imported .float__round⟩]

/-- The operations of `roundf`. -/
def «cands_roundf» : List Cand :=
  [⟨_, _, _, _, .imported .float32__roundf⟩]

/-- The operations of `sin`. -/
def «cands_sin» : List Cand :=
  [⟨_, _, _, _, .inlined .float__sin⟩]

/-- The operations of `sinf`. -/
def «cands_sinf» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__sinf⟩]

/-- The operations of `sinh`. -/
def «cands_sinh» : List Cand :=
  [⟨_, _, _, _, .inlined .float__sinh⟩]

/-- The operations of `sinhf`. -/
def «cands_sinhf» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__sinhf⟩]

/-- The operations of `sqrt`. -/
def «cands_sqrt» : List Cand :=
  [⟨_, _, _, _, .inlined .float__sqrt⟩]

/-- The operations of `sqrtf`. -/
def «cands_sqrtf» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__sqrtf⟩]

/-- The operations of `tan`. -/
def «cands_tan» : List Cand :=
  [⟨_, _, _, _, .inlined .float__tan⟩]

/-- The operations of `tanf`. -/
def «cands_tanf» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__tanf⟩]

/-- The operations of `tanh`. -/
def «cands_tanh» : List Cand :=
  [⟨_, _, _, _, .inlined .float__tanh⟩]

/-- The operations of `tanhf`. -/
def «cands_tanhf» : List Cand :=
  [⟨_, _, _, _, .inlined .float32__tanhf⟩]

/-- The candidates of the extern `name`, when it is one of the floating-point numbers. -/
def candsFloat? (name : String) : Option (List Cand) :=
  match name with
  | "acos" => some «cands_acos»
  | "acosf" => some «cands_acosf»
  | "acosh" => some «cands_acosh»
  | "acoshf" => some «cands_acoshf»
  | "asin" => some «cands_asin»
  | "asinf" => some «cands_asinf»
  | "asinh" => some «cands_asinh»
  | "asinhf" => some «cands_asinhf»
  | "atan" => some «cands_atan»
  | "atan2" => some «cands_atan2»
  | "atan2f" => some «cands_atan2f»
  | "atanf" => some «cands_atanf»
  | "atanh" => some «cands_atanh»
  | "atanhf" => some «cands_atanhf»
  | "cbrt" => some «cands_cbrt»
  | "cbrtf" => some «cands_cbrtf»
  | "ceil" => some «cands_ceil»
  | "ceilf" => some «cands_ceilf»
  | "cos" => some «cands_cos»
  | "cosf" => some «cands_cosf»
  | "cosh" => some «cands_cosh»
  | "coshf" => some «cands_coshf»
  | "exp" => some «cands_exp»
  | "exp2" => some «cands_exp2»
  | "exp2f" => some «cands_exp2f»
  | "expf" => some «cands_expf»
  | "fabs" => some «cands_fabs»
  | "fabsf" => some «cands_fabsf»
  | "floor" => some «cands_floor»
  | "floorf" => some «cands_floorf»
  | "lean_float32_add" => some «cands_lean_float32_add»
  | "lean_float32_beq" => some «cands_lean_float32_beq»
  | "lean_float32_decLe__Float32_decLe" => some «cands_lean_float32_decLe__Float32_decLe»
  | "lean_float32_decLe__Float32_le" => some «cands_lean_float32_decLe__Float32_le»
  | "lean_float32_decLt__Float32_decLt" => some «cands_lean_float32_decLt__Float32_decLt»
  | "lean_float32_decLt__Float32_lt" => some «cands_lean_float32_decLt__Float32_lt»
  | "lean_float32_div" => some «cands_lean_float32_div»
  | "lean_float32_frexp" => some «cands_lean_float32_frexp»
  | "lean_float32_isfinite" => some «cands_lean_float32_isfinite»
  | "lean_float32_isinf" => some «cands_lean_float32_isinf»
  | "lean_float32_isnan" => some «cands_lean_float32_isnan»
  | "lean_float32_mul" => some «cands_lean_float32_mul»
  | "lean_float32_negate" => some «cands_lean_float32_negate»
  | "lean_float32_of_bits__Float32_ofBits" => some «cands_lean_float32_of_bits__Float32_ofBits»
  | "lean_float32_of_bits__Float32_ofModel" => some «cands_lean_float32_of_bits__Float32_ofModel»
  | "lean_float32_scaleb" => some «cands_lean_float32_scaleb»
  | "lean_float32_sub" => some «cands_lean_float32_sub»
  | "lean_float32_to_bits__Float32_toBits" => some «cands_lean_float32_to_bits__Float32_toBits»
  | "lean_float32_to_bits__Float32_toModel" => some «cands_lean_float32_to_bits__Float32_toModel»
  | "lean_float32_to_float" => some «cands_lean_float32_to_float»
  | "lean_float32_to_int16" => some «cands_lean_float32_to_int16»
  | "lean_float32_to_int32" => some «cands_lean_float32_to_int32»
  | "lean_float32_to_int64" => some «cands_lean_float32_to_int64»
  | "lean_float32_to_int8" => some «cands_lean_float32_to_int8»
  | "lean_float32_to_string" => some «cands_lean_float32_to_string»
  | "lean_float32_to_uint16" => some «cands_lean_float32_to_uint16»
  | "lean_float32_to_uint32" => some «cands_lean_float32_to_uint32»
  | "lean_float32_to_uint64" => some «cands_lean_float32_to_uint64»
  | "lean_float32_to_uint8" => some «cands_lean_float32_to_uint8»
  | "lean_float_add" => some «cands_lean_float_add»
  | "lean_float_beq" => some «cands_lean_float_beq»
  | "lean_float_decLe__Float_decLe" => some «cands_lean_float_decLe__Float_decLe»
  | "lean_float_decLe__Float_le" => some «cands_lean_float_decLe__Float_le»
  | "lean_float_decLt__Float_decLt" => some «cands_lean_float_decLt__Float_decLt»
  | "lean_float_decLt__Float_lt" => some «cands_lean_float_decLt__Float_lt»
  | "lean_float_div" => some «cands_lean_float_div»
  | "lean_float_frexp" => some «cands_lean_float_frexp»
  | "lean_float_isfinite" => some «cands_lean_float_isfinite»
  | "lean_float_isinf" => some «cands_lean_float_isinf»
  | "lean_float_isnan" => some «cands_lean_float_isnan»
  | "lean_float_mul" => some «cands_lean_float_mul»
  | "lean_float_negate" => some «cands_lean_float_negate»
  | "lean_float_of_bits__Float_ofBits" => some «cands_lean_float_of_bits__Float_ofBits»
  | "lean_float_of_bits__Float_ofModel" => some «cands_lean_float_of_bits__Float_ofModel»
  | "lean_float_scaleb" => some «cands_lean_float_scaleb»
  | "lean_float_sub" => some «cands_lean_float_sub»
  | "lean_float_to_bits__Float_toBits" => some «cands_lean_float_to_bits__Float_toBits»
  | "lean_float_to_bits__Float_toModel" => some «cands_lean_float_to_bits__Float_toModel»
  | "lean_float_to_float32" => some «cands_lean_float_to_float32»
  | "lean_float_to_int16" => some «cands_lean_float_to_int16»
  | "lean_float_to_int32" => some «cands_lean_float_to_int32»
  | "lean_float_to_int64" => some «cands_lean_float_to_int64»
  | "lean_float_to_int8" => some «cands_lean_float_to_int8»
  | "lean_float_to_string" => some «cands_lean_float_to_string»
  | "lean_float_to_uint16" => some «cands_lean_float_to_uint16»
  | "lean_float_to_uint32" => some «cands_lean_float_to_uint32»
  | "lean_float_to_uint64" => some «cands_lean_float_to_uint64»
  | "lean_float_to_uint8" => some «cands_lean_float_to_uint8»
  | "log" => some «cands_log»
  | "log10" => some «cands_log10»
  | "log10f" => some «cands_log10f»
  | "log2" => some «cands_log2»
  | "log2f" => some «cands_log2f»
  | "logf" => some «cands_logf»
  | "pow" => some «cands_pow»
  | "powf" => some «cands_powf»
  | "round" => some «cands_round»
  | "roundf" => some «cands_roundf»
  | "sin" => some «cands_sin»
  | "sinf" => some «cands_sinf»
  | "sinh" => some «cands_sinh»
  | "sinhf" => some «cands_sinhf»
  | "sqrt" => some «cands_sqrt»
  | "sqrtf" => some «cands_sqrtf»
  | "tan" => some «cands_tan»
  | "tanf" => some «cands_tanf»
  | "tanh" => some «cands_tanh»
  | "tanhf" => some «cands_tanhf»
  | _ => none

end JsOp

end MoreJs

end
