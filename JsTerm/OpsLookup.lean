module

public import JsTerm.Ops

@[expose] public section

set_option autoImplicit false

/-!
# Finding the operation of an extern call

**Generated** by `scripts/gen_js_ops.py`; do not edit.

`JsOp.lookup name σs τ` is the operation of the extern `name` (as the catalogue spells it,
`lean_nat_div`) at the argument types `σs` and the result type `τ`, if there is one: the
constructor of `JsOpImported` or `JsOpInlinable` whose signature is exactly `σs → τ` (a
polymorphic one instantiated from the types), with its effects.
-/

namespace MoreJs

/-- An operation: one that calls the runtime, or one written inline. -/
inductive JsOp : Effectfulness → MayThrow → List JsTy → JsTy → Type where
  | imported {e : Effectfulness} {t : MayThrow} {σs : List JsTy} {τ : JsTy}
      (op : JsOpImported e t σs τ) : JsOp e t σs τ
  | inlined {e : Effectfulness} {t : MayThrow} {σs : List JsTy} {τ : JsTy}
      (op : JsOpInlinable e t σs τ) : JsOp e t σs τ

/-- An operation of some effects. -/
abbrev JsSomeOp (σs : List JsTy) (τ : JsTy) : Type := Σ e t, JsOp e t σs τ

namespace JsOp

/-- The name of the operation. -/
def name {e : Effectfulness} {t : MayThrow} {σs : List JsTy} {τ : JsTy} : JsOp e t σs τ → String
  | .imported op => op.name
  | .inlined op => op.name

/-- A candidate: an operation at some signature. -/
abbrev Cand : Type := Σ (σs : List JsTy) (τ : JsTy) (e : Effectfulness) (t : MayThrow), JsOp e t σs τ

/-- The first candidate that has the signature `σs → τ`. -/
def firstOf (σs : List JsTy) (τ : JsTy) : List Cand → Option (JsSomeOp σs τ)
  | [] => none
  | ⟨σs', τ', e, t, op⟩ :: rest =>
    if h : σs' = σs ∧ τ' = τ then some ⟨e, t, h.1 ▸ h.2 ▸ op⟩ else firstOf σs τ rest

/-- The type a thunk operation delays (the first delay among the types). -/
def elemOf? : List JsTy → JsTy
  | [] => .terminal .bool
  | .thunk t :: _ => t
  | .fn [] t :: _ => t
  | _ :: ts => elemOf? ts

/-- The layout of the array among the argument types (the first one that is an array). -/
def layoutOf? : List JsTy → Option (Σ a e, JsArrayLayout a e)
  | [] => none
  | t :: ts => match JsArrayLayout.of? t with
    | some ⟨e, l⟩ => some ⟨t, e, l⟩
    | none => layoutOf? ts

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

/-- The operations of `lean_array_fset`. -/
def «cands_lean_array_fset» (σs : List JsTy) (τ : JsTy) : List Cand :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.bigint_nat__lean_array_set_immutable l)⟩] | none => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.uint53__lean_array_set_immutable l)⟩] | none => [])

/-- The operations of `lean_array_fswap`. -/
def «cands_lean_array_fswap» (σs : List JsTy) (τ : JsTy) : List Cand :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.bigint_nat__lean_array_swap_immutable l)⟩] | none => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.uint53__lean_array_swap_immutable l)⟩] | none => [])

/-- The operations of `lean_array_get`. -/
def «cands_lean_array_get» (σs : List JsTy) (τ : JsTy) : List Cand :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.bigint_nat__lean_array_get l)⟩] | none => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.uint53__lean_array_get l)⟩] | none => [])

/-- The operations of `lean_array_get_borrowed`. -/
def «cands_lean_array_get_borrowed» (σs : List JsTy) (τ : JsTy) : List Cand :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.bigint_nat__lean_array_get l)⟩] | none => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.uint53__lean_array_get l)⟩] | none => [])

/-- The operations of `lean_array_get_size`. -/
def «cands_lean_array_get_size» (σs : List JsTy) (τ : JsTy) : List Cand :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, _, _, .inlined (.bigint_nat__lean_array_get_size l)⟩] | none => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, _, _, .inlined (.uint53__lean_array_get_size l)⟩] | none => [])

/-- The operations of `lean_array_mk`. -/
def «cands_lean_array_mk» (σs : List JsTy) (τ : JsTy) : List Cand :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .generic α⟩ => [⟨_, _, _, _, .inlined (.array__lean_array_mk α)⟩] | _ => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .typed t⟩ => [⟨_, _, _, _, .inlined (.typedArray__lean_array_mk t)⟩] | _ => [])

/-- The operations of `lean_array_pop`. -/
def «cands_lean_array_pop» (σs : List JsTy) (τ : JsTy) : List Cand :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.array__lean_array_pop_immutable l)⟩] | none => [])

/-- The operations of `lean_array_push`. -/
def «cands_lean_array_push» (σs : List JsTy) (τ : JsTy) : List Cand :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.array__lean_array_push_immutable l)⟩] | none => [])

/-- The operations of `lean_array_set`. -/
def «cands_lean_array_set» (σs : List JsTy) (τ : JsTy) : List Cand :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.bigint_nat__lean_array_set_immutable l)⟩] | none => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.uint53__lean_array_set_immutable l)⟩] | none => [])

/-- The operations of `lean_array_swap`. -/
def «cands_lean_array_swap» (σs : List JsTy) (τ : JsTy) : List Cand :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.bigint_nat__lean_array_swap_immutable l)⟩] | none => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.uint53__lean_array_swap_immutable l)⟩] | none => [])

/-- The operations of `lean_array_to_list`. -/
def «cands_lean_array_to_list» (σs : List JsTy) (τ : JsTy) : List Cand :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .generic α⟩ => [⟨_, _, _, _, .inlined (.array__lean_array_to_list α)⟩] | _ => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .typed t⟩ => [⟨_, _, _, _, .imported (.typedArray__lean_array_to_list t)⟩] | _ => [])

/-- The operations of `lean_bool_to_int16`. -/
def «cands_lean_bool_to_int16» : List Cand :=
  [⟨_, _, _, _, .imported .bool__lean_bool_to_int16⟩]

/-- The operations of `lean_bool_to_int32`. -/
def «cands_lean_bool_to_int32» : List Cand :=
  [⟨_, _, _, _, .imported .bool__lean_bool_to_int32⟩]

/-- The operations of `lean_bool_to_int64`. -/
def «cands_lean_bool_to_int64» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_bool_to_int64⟩, ⟨_, _, _, _, .imported .int53__lean_bool_to_int64⟩]

/-- The operations of `lean_bool_to_int8`. -/
def «cands_lean_bool_to_int8» : List Cand :=
  [⟨_, _, _, _, .imported .bool__lean_bool_to_int8⟩]

/-- The operations of `lean_bool_to_uint16`. -/
def «cands_lean_bool_to_uint16» : List Cand :=
  [⟨_, _, _, _, .imported .bool__lean_bool_to_uint16⟩]

/-- The operations of `lean_bool_to_uint32`. -/
def «cands_lean_bool_to_uint32» : List Cand :=
  [⟨_, _, _, _, .imported .bool__lean_bool_to_uint32⟩]

/-- The operations of `lean_bool_to_uint64`. -/
def «cands_lean_bool_to_uint64» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_bool_to_uint64⟩, ⟨_, _, _, _, .imported .uint53__lean_bool_to_uint64⟩]

/-- The operations of `lean_bool_to_uint8`. -/
def «cands_lean_bool_to_uint8» : List Cand :=
  [⟨_, _, _, _, .imported .bool__lean_bool_to_uint8⟩]

/-- The operations of `lean_dbg_trace_if_shared`. -/
def «cands_lean_dbg_trace_if_shared» (σs : List JsTy) (τ : JsTy) : List Cand :=
  [⟨_, _, _, _, .imported (.string__lean_dbg_trace_if_shared (elemOf? (σs ++ [τ])))⟩]

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

/-- The operations of `lean_get_githash`. -/
def «cands_lean_get_githash» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_get_githash⟩]

/-- The operations of `lean_int16_abs`. -/
def «cands_lean_int16_abs» : List Cand :=
  [⟨_, _, _, _, .imported .int16__lean_int16_abs⟩]

/-- The operations of `lean_int16_add`. -/
def «cands_lean_int16_add» : List Cand :=
  [⟨_, _, _, _, .imported .int16__lean_int16_add⟩]

/-- The operations of `lean_int16_complement`. -/
def «cands_lean_int16_complement» : List Cand :=
  [⟨_, _, _, _, .imported .int16__lean_int16_complement⟩]

/-- The operations of `lean_int16_dec_eq`. -/
def «cands_lean_int16_dec_eq» : List Cand :=
  [⟨_, _, _, _, .inlined .int16__lean_int16_dec_eq⟩]

/-- The operations of `lean_int16_dec_le`. -/
def «cands_lean_int16_dec_le» : List Cand :=
  [⟨_, _, _, _, .inlined .int16__lean_int16_dec_le⟩]

/-- The operations of `lean_int16_dec_lt`. -/
def «cands_lean_int16_dec_lt» : List Cand :=
  [⟨_, _, _, _, .inlined .int16__lean_int16_dec_lt⟩]

/-- The operations of `lean_int16_div`. -/
def «cands_lean_int16_div» : List Cand :=
  [⟨_, _, _, _, .imported .int16__lean_int16_div⟩]

/-- The operations of `lean_int16_land`. -/
def «cands_lean_int16_land» : List Cand :=
  [⟨_, _, _, _, .imported .int16__lean_int16_land⟩]

/-- The operations of `lean_int16_lor`. -/
def «cands_lean_int16_lor» : List Cand :=
  [⟨_, _, _, _, .imported .int16__lean_int16_lor⟩]

/-- The operations of `lean_int16_mod`. -/
def «cands_lean_int16_mod» : List Cand :=
  [⟨_, _, _, _, .imported .int16__lean_int16_mod⟩]

/-- The operations of `lean_int16_mul`. -/
def «cands_lean_int16_mul» : List Cand :=
  [⟨_, _, _, _, .imported .int16__lean_int16_mul⟩]

/-- The operations of `lean_int16_neg`. -/
def «cands_lean_int16_neg» : List Cand :=
  [⟨_, _, _, _, .imported .int16__lean_int16_neg⟩]

/-- The operations of `lean_int16_of_int`. -/
def «cands_lean_int16_of_int» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_int16_of_int⟩, ⟨_, _, _, _, .imported .int53__lean_int16_of_int⟩]

/-- The operations of `lean_int16_of_nat`. -/
def «cands_lean_int16_of_nat» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_int16_of_nat⟩, ⟨_, _, _, _, .imported .uint53__lean_int16_of_nat⟩]

/-- The operations of `lean_int16_shift_left`. -/
def «cands_lean_int16_shift_left» : List Cand :=
  [⟨_, _, _, _, .imported .int16__lean_int16_shift_left⟩]

/-- The operations of `lean_int16_shift_right`. -/
def «cands_lean_int16_shift_right» : List Cand :=
  [⟨_, _, _, _, .imported .int16__lean_int16_shift_right⟩]

/-- The operations of `lean_int16_sub`. -/
def «cands_lean_int16_sub» : List Cand :=
  [⟨_, _, _, _, .imported .int16__lean_int16_sub⟩]

/-- The operations of `lean_int16_to_float`. -/
def «cands_lean_int16_to_float» : List Cand :=
  [⟨_, _, _, _, .inlined .int16__lean_int16_to_float⟩]

/-- The operations of `lean_int16_to_float32`. -/
def «cands_lean_int16_to_float32» : List Cand :=
  [⟨_, _, _, _, .inlined .int16__lean_int16_to_float32⟩]

/-- The operations of `lean_int16_to_int`. -/
def «cands_lean_int16_to_int» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_int__lean_int16_to_int⟩, ⟨_, _, _, _, .inlined .int53__lean_int16_to_int⟩]

/-- The operations of `lean_int16_to_int32`. -/
def «cands_lean_int16_to_int32» : List Cand :=
  [⟨_, _, _, _, .inlined .int16__lean_int16_to_int32⟩]

/-- The operations of `lean_int16_to_int64`. -/
def «cands_lean_int16_to_int64» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_int__lean_int16_to_int64⟩, ⟨_, _, _, _, .inlined .int53__lean_int16_to_int64⟩]

/-- The operations of `lean_int16_to_int8`. -/
def «cands_lean_int16_to_int8» : List Cand :=
  [⟨_, _, _, _, .imported .int16__lean_int16_to_int8⟩]

/-- The operations of `lean_int16_xor`. -/
def «cands_lean_int16_xor» : List Cand :=
  [⟨_, _, _, _, .imported .int16__lean_int16_xor⟩]

/-- The operations of `lean_int32_abs`. -/
def «cands_lean_int32_abs» : List Cand :=
  [⟨_, _, _, _, .imported .int32__lean_int32_abs⟩]

/-- The operations of `lean_int32_add`. -/
def «cands_lean_int32_add» : List Cand :=
  [⟨_, _, _, _, .imported .int32__lean_int32_add⟩]

/-- The operations of `lean_int32_complement`. -/
def «cands_lean_int32_complement» : List Cand :=
  [⟨_, _, _, _, .imported .int32__lean_int32_complement⟩]

/-- The operations of `lean_int32_dec_eq`. -/
def «cands_lean_int32_dec_eq» : List Cand :=
  [⟨_, _, _, _, .inlined .int32__lean_int32_dec_eq⟩]

/-- The operations of `lean_int32_dec_le`. -/
def «cands_lean_int32_dec_le» : List Cand :=
  [⟨_, _, _, _, .inlined .int32__lean_int32_dec_le⟩]

/-- The operations of `lean_int32_dec_lt`. -/
def «cands_lean_int32_dec_lt» : List Cand :=
  [⟨_, _, _, _, .inlined .int32__lean_int32_dec_lt⟩]

/-- The operations of `lean_int32_div`. -/
def «cands_lean_int32_div» : List Cand :=
  [⟨_, _, _, _, .imported .int32__lean_int32_div⟩]

/-- The operations of `lean_int32_land`. -/
def «cands_lean_int32_land» : List Cand :=
  [⟨_, _, _, _, .imported .int32__lean_int32_land⟩]

/-- The operations of `lean_int32_lor`. -/
def «cands_lean_int32_lor» : List Cand :=
  [⟨_, _, _, _, .imported .int32__lean_int32_lor⟩]

/-- The operations of `lean_int32_mod`. -/
def «cands_lean_int32_mod» : List Cand :=
  [⟨_, _, _, _, .imported .int32__lean_int32_mod⟩]

/-- The operations of `lean_int32_mul`. -/
def «cands_lean_int32_mul» : List Cand :=
  [⟨_, _, _, _, .imported .int32__lean_int32_mul⟩]

/-- The operations of `lean_int32_neg`. -/
def «cands_lean_int32_neg» : List Cand :=
  [⟨_, _, _, _, .imported .int32__lean_int32_neg⟩]

/-- The operations of `lean_int32_of_int`. -/
def «cands_lean_int32_of_int» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_int32_of_int⟩, ⟨_, _, _, _, .imported .int53__lean_int32_of_int⟩]

/-- The operations of `lean_int32_of_nat`. -/
def «cands_lean_int32_of_nat» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_int32_of_nat⟩, ⟨_, _, _, _, .imported .uint53__lean_int32_of_nat⟩]

/-- The operations of `lean_int32_shift_left`. -/
def «cands_lean_int32_shift_left» : List Cand :=
  [⟨_, _, _, _, .imported .int32__lean_int32_shift_left⟩]

/-- The operations of `lean_int32_shift_right`. -/
def «cands_lean_int32_shift_right» : List Cand :=
  [⟨_, _, _, _, .imported .int32__lean_int32_shift_right⟩]

/-- The operations of `lean_int32_sub`. -/
def «cands_lean_int32_sub» : List Cand :=
  [⟨_, _, _, _, .imported .int32__lean_int32_sub⟩]

/-- The operations of `lean_int32_to_float`. -/
def «cands_lean_int32_to_float» : List Cand :=
  [⟨_, _, _, _, .inlined .int32__lean_int32_to_float⟩]

/-- The operations of `lean_int32_to_float32`. -/
def «cands_lean_int32_to_float32» : List Cand :=
  [⟨_, _, _, _, .inlined .int32__lean_int32_to_float32⟩]

/-- The operations of `lean_int32_to_int`. -/
def «cands_lean_int32_to_int» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_int__lean_int32_to_int⟩, ⟨_, _, _, _, .inlined .int53__lean_int32_to_int⟩]

/-- The operations of `lean_int32_to_int16`. -/
def «cands_lean_int32_to_int16» : List Cand :=
  [⟨_, _, _, _, .imported .int32__lean_int32_to_int16⟩]

/-- The operations of `lean_int32_to_int64`. -/
def «cands_lean_int32_to_int64» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_int__lean_int32_to_int64⟩, ⟨_, _, _, _, .inlined .int53__lean_int32_to_int64⟩]

/-- The operations of `lean_int32_to_int8`. -/
def «cands_lean_int32_to_int8» : List Cand :=
  [⟨_, _, _, _, .imported .int32__lean_int32_to_int8⟩]

/-- The operations of `lean_int32_xor`. -/
def «cands_lean_int32_xor» : List Cand :=
  [⟨_, _, _, _, .imported .int32__lean_int32_xor⟩]

/-- The operations of `lean_int64_abs`. -/
def «cands_lean_int64_abs» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_int64_abs⟩, ⟨_, _, _, _, .imported .int53__lean_int64_abs⟩]

/-- The operations of `lean_int64_add`. -/
def «cands_lean_int64_add» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_int64_add⟩, ⟨_, _, _, _, .imported .int53__lean_int64_add⟩]

/-- The operations of `lean_int64_complement`. -/
def «cands_lean_int64_complement» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_int64_complement⟩, ⟨_, _, _, _, .imported .int53__lean_int64_complement⟩]

/-- The operations of `lean_int64_dec_eq`. -/
def «cands_lean_int64_dec_eq» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_int__lean_int64_dec_eq⟩, ⟨_, _, _, _, .inlined .int53__lean_int64_dec_eq⟩]

/-- The operations of `lean_int64_dec_le`. -/
def «cands_lean_int64_dec_le» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_int__lean_int64_dec_le⟩, ⟨_, _, _, _, .inlined .int53__lean_int64_dec_le⟩]

/-- The operations of `lean_int64_dec_lt`. -/
def «cands_lean_int64_dec_lt» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_int__lean_int64_dec_lt⟩, ⟨_, _, _, _, .inlined .int53__lean_int64_dec_lt⟩]

/-- The operations of `lean_int64_div`. -/
def «cands_lean_int64_div» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_int64_div⟩, ⟨_, _, _, _, .imported .int53__lean_int64_div⟩]

/-- The operations of `lean_int64_land`. -/
def «cands_lean_int64_land» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_int64_land⟩, ⟨_, _, _, _, .imported .int53__lean_int64_land⟩]

/-- The operations of `lean_int64_lor`. -/
def «cands_lean_int64_lor» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_int64_lor⟩, ⟨_, _, _, _, .imported .int53__lean_int64_lor⟩]

/-- The operations of `lean_int64_mod`. -/
def «cands_lean_int64_mod» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_int64_mod⟩, ⟨_, _, _, _, .imported .int53__lean_int64_mod⟩]

/-- The operations of `lean_int64_mul`. -/
def «cands_lean_int64_mul» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_int64_mul⟩, ⟨_, _, _, _, .imported .int53__lean_int64_mul⟩]

/-- The operations of `lean_int64_neg`. -/
def «cands_lean_int64_neg» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_int64_neg⟩, ⟨_, _, _, _, .imported .int53__lean_int64_neg⟩]

/-- The operations of `lean_int64_of_int`. -/
def «cands_lean_int64_of_int» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_int64_of_int⟩, ⟨_, _, _, _, .imported .bigint_int__int53__lean_int64_of_int⟩, ⟨_, _, _, _, .imported .int53__bigint_int__lean_int64_of_int⟩, ⟨_, _, _, _, .imported .int53__lean_int64_of_int⟩]

/-- The operations of `lean_int64_of_nat`. -/
def «cands_lean_int64_of_nat» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__bigint_int__lean_int64_of_nat⟩, ⟨_, _, _, _, .imported .bigint_nat__int53__lean_int64_of_nat⟩, ⟨_, _, _, _, .imported .uint53__bigint_int__lean_int64_of_nat⟩, ⟨_, _, _, _, .imported .uint53__int53__lean_int64_of_nat⟩]

/-- The operations of `lean_int64_shift_left`. -/
def «cands_lean_int64_shift_left» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_int64_shift_left⟩, ⟨_, _, _, _, .imported .int53__lean_int64_shift_left⟩]

/-- The operations of `lean_int64_shift_right`. -/
def «cands_lean_int64_shift_right» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_int64_shift_right⟩, ⟨_, _, _, _, .imported .int53__lean_int64_shift_right⟩]

/-- The operations of `lean_int64_sub`. -/
def «cands_lean_int64_sub» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_int64_sub⟩, ⟨_, _, _, _, .imported .int53__lean_int64_sub⟩]

/-- The operations of `lean_int64_to_float`. -/
def «cands_lean_int64_to_float» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_int__lean_int64_to_float⟩, ⟨_, _, _, _, .inlined .int53__lean_int64_to_float⟩]

/-- The operations of `lean_int64_to_float32`. -/
def «cands_lean_int64_to_float32» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_int__lean_int64_to_float32⟩, ⟨_, _, _, _, .inlined .int53__lean_int64_to_float32⟩]

/-- The operations of `lean_int64_to_int16`. -/
def «cands_lean_int64_to_int16» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_int64_to_int16⟩, ⟨_, _, _, _, .imported .int53__lean_int64_to_int16⟩]

/-- The operations of `lean_int64_to_int32`. -/
def «cands_lean_int64_to_int32» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_int64_to_int32⟩, ⟨_, _, _, _, .imported .int53__lean_int64_to_int32⟩]

/-- The operations of `lean_int64_to_int8`. -/
def «cands_lean_int64_to_int8» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_int64_to_int8⟩, ⟨_, _, _, _, .imported .int53__lean_int64_to_int8⟩]

/-- The operations of `lean_int64_to_int_sint`. -/
def «cands_lean_int64_to_int_sint» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_int__lean_int64_to_int_sint⟩, ⟨_, _, _, _, .imported .bigint_int__int53__lean_int64_to_int_sint⟩, ⟨_, _, _, _, .inlined .int53__bigint_int__lean_int64_to_int_sint⟩, ⟨_, _, _, _, .inlined .int53__lean_int64_to_int_sint⟩]

/-- The operations of `lean_int64_xor`. -/
def «cands_lean_int64_xor» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_int64_xor⟩, ⟨_, _, _, _, .imported .int53__lean_int64_xor⟩]

/-- The operations of `lean_int8_abs`. -/
def «cands_lean_int8_abs» : List Cand :=
  [⟨_, _, _, _, .imported .int8__lean_int8_abs⟩]

/-- The operations of `lean_int8_add`. -/
def «cands_lean_int8_add» : List Cand :=
  [⟨_, _, _, _, .imported .int8__lean_int8_add⟩]

/-- The operations of `lean_int8_complement`. -/
def «cands_lean_int8_complement» : List Cand :=
  [⟨_, _, _, _, .imported .int8__lean_int8_complement⟩]

/-- The operations of `lean_int8_dec_eq`. -/
def «cands_lean_int8_dec_eq» : List Cand :=
  [⟨_, _, _, _, .inlined .int8__lean_int8_dec_eq⟩]

/-- The operations of `lean_int8_dec_le`. -/
def «cands_lean_int8_dec_le» : List Cand :=
  [⟨_, _, _, _, .inlined .int8__lean_int8_dec_le⟩]

/-- The operations of `lean_int8_dec_lt`. -/
def «cands_lean_int8_dec_lt» : List Cand :=
  [⟨_, _, _, _, .inlined .int8__lean_int8_dec_lt⟩]

/-- The operations of `lean_int8_div`. -/
def «cands_lean_int8_div» : List Cand :=
  [⟨_, _, _, _, .imported .int8__lean_int8_div⟩]

/-- The operations of `lean_int8_land`. -/
def «cands_lean_int8_land» : List Cand :=
  [⟨_, _, _, _, .imported .int8__lean_int8_land⟩]

/-- The operations of `lean_int8_lor`. -/
def «cands_lean_int8_lor» : List Cand :=
  [⟨_, _, _, _, .imported .int8__lean_int8_lor⟩]

/-- The operations of `lean_int8_mod`. -/
def «cands_lean_int8_mod» : List Cand :=
  [⟨_, _, _, _, .imported .int8__lean_int8_mod⟩]

/-- The operations of `lean_int8_mul`. -/
def «cands_lean_int8_mul» : List Cand :=
  [⟨_, _, _, _, .imported .int8__lean_int8_mul⟩]

/-- The operations of `lean_int8_neg`. -/
def «cands_lean_int8_neg» : List Cand :=
  [⟨_, _, _, _, .imported .int8__lean_int8_neg⟩]

/-- The operations of `lean_int8_of_int`. -/
def «cands_lean_int8_of_int» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_int8_of_int⟩, ⟨_, _, _, _, .imported .int53__lean_int8_of_int⟩]

/-- The operations of `lean_int8_of_nat`. -/
def «cands_lean_int8_of_nat» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_int8_of_nat⟩, ⟨_, _, _, _, .imported .uint53__lean_int8_of_nat⟩]

/-- The operations of `lean_int8_shift_left`. -/
def «cands_lean_int8_shift_left» : List Cand :=
  [⟨_, _, _, _, .imported .int8__lean_int8_shift_left⟩]

/-- The operations of `lean_int8_shift_right`. -/
def «cands_lean_int8_shift_right» : List Cand :=
  [⟨_, _, _, _, .imported .int8__lean_int8_shift_right⟩]

/-- The operations of `lean_int8_sub`. -/
def «cands_lean_int8_sub» : List Cand :=
  [⟨_, _, _, _, .imported .int8__lean_int8_sub⟩]

/-- The operations of `lean_int8_to_float`. -/
def «cands_lean_int8_to_float» : List Cand :=
  [⟨_, _, _, _, .inlined .int8__lean_int8_to_float⟩]

/-- The operations of `lean_int8_to_float32`. -/
def «cands_lean_int8_to_float32» : List Cand :=
  [⟨_, _, _, _, .inlined .int8__lean_int8_to_float32⟩]

/-- The operations of `lean_int8_to_int`. -/
def «cands_lean_int8_to_int» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_int__lean_int8_to_int⟩, ⟨_, _, _, _, .inlined .int53__lean_int8_to_int⟩]

/-- The operations of `lean_int8_to_int16`. -/
def «cands_lean_int8_to_int16» : List Cand :=
  [⟨_, _, _, _, .inlined .int8__lean_int8_to_int16⟩]

/-- The operations of `lean_int8_to_int32`. -/
def «cands_lean_int8_to_int32» : List Cand :=
  [⟨_, _, _, _, .inlined .int8__lean_int8_to_int32⟩]

/-- The operations of `lean_int8_to_int64`. -/
def «cands_lean_int8_to_int64» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_int__lean_int8_to_int64⟩, ⟨_, _, _, _, .inlined .int53__lean_int8_to_int64⟩]

/-- The operations of `lean_int8_xor`. -/
def «cands_lean_int8_xor» : List Cand :=
  [⟨_, _, _, _, .imported .int8__lean_int8_xor⟩]

/-- The operations of `lean_int_add`. -/
def «cands_lean_int_add» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_int__lean_int_add⟩, ⟨_, _, _, _, .imported .int53__lean_int_add⟩]

/-- The operations of `lean_int_dec_eq`. -/
def «cands_lean_int_dec_eq» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_int__lean_int_dec_eq⟩, ⟨_, _, _, _, .inlined .int53__lean_int_dec_eq⟩]

/-- The operations of `lean_int_dec_le`. -/
def «cands_lean_int_dec_le» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_int__lean_int_dec_le⟩, ⟨_, _, _, _, .inlined .int53__lean_int_dec_le⟩]

/-- The operations of `lean_int_dec_lt`. -/
def «cands_lean_int_dec_lt» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_int__lean_int_dec_lt⟩, ⟨_, _, _, _, .inlined .int53__lean_int_dec_lt⟩]

/-- The operations of `lean_int_dec_nonneg`. -/
def «cands_lean_int_dec_nonneg» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_int__lean_int_dec_nonneg⟩, ⟨_, _, _, _, .inlined .int53__lean_int_dec_nonneg⟩]

/-- The operations of `lean_int_div`. -/
def «cands_lean_int_div» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_int_div⟩, ⟨_, _, _, _, .imported .int53__lean_int_div⟩]

/-- The operations of `lean_int_div_exact`. -/
def «cands_lean_int_div_exact» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_int_div_exact⟩, ⟨_, _, _, _, .imported .int53__lean_int_div_exact⟩]

/-- The operations of `lean_int_ediv`. -/
def «cands_lean_int_ediv» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_int_ediv⟩, ⟨_, _, _, _, .imported .int53__lean_int_ediv⟩]

/-- The operations of `lean_int_emod`. -/
def «cands_lean_int_emod» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_int_emod⟩, ⟨_, _, _, _, .imported .int53__lean_int_emod⟩]

/-- The operations of `lean_int_mod`. -/
def «cands_lean_int_mod» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_int_mod⟩, ⟨_, _, _, _, .imported .int53__lean_int_mod⟩]

/-- The operations of `lean_int_mul`. -/
def «cands_lean_int_mul» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_int__lean_int_mul⟩, ⟨_, _, _, _, .imported .int53__lean_int_mul⟩]

/-- The operations of `lean_int_neg`. -/
def «cands_lean_int_neg» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_int__lean_int_neg⟩, ⟨_, _, _, _, .imported .int53__lean_int_neg⟩]

/-- The operations of `lean_int_neg_succ_of_nat`. -/
def «cands_lean_int_neg_succ_of_nat» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__bigint_int__lean_int_neg_succ_of_nat⟩, ⟨_, _, _, _, .imported .bigint_nat__int53__lean_int_neg_succ_of_nat⟩, ⟨_, _, _, _, .imported .uint53__bigint_int__lean_int_neg_succ_of_nat⟩, ⟨_, _, _, _, .imported .uint53__int53__lean_int_neg_succ_of_nat⟩]

/-- The operations of `lean_int_sub`. -/
def «cands_lean_int_sub» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_int__lean_int_sub⟩, ⟨_, _, _, _, .imported .int53__lean_int_sub⟩]

/-- The operations of `lean_internal_has_llvm_backend`. -/
def «cands_lean_internal_has_llvm_backend» : List Cand :=
  [⟨_, _, _, _, .imported .bool__lean_internal_has_llvm_backend⟩]

/-- The operations of `lean_internal_is_stage0`. -/
def «cands_lean_internal_is_stage0» : List Cand :=
  [⟨_, _, _, _, .imported .bool__lean_internal_is_stage0⟩]

/-- The operations of `lean_mk_array`. -/
def «cands_lean_mk_array» (σs : List JsTy) (τ : JsTy) : List Cand :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .generic α⟩ => [⟨_, _, _, _, .imported (.bigint_nat__lean_mk_array α)⟩] | _ => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .typed t⟩ => [⟨_, _, _, _, .imported (.typedArray__bigint_nat__lean_mk_array t)⟩] | _ => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .generic α⟩ => [⟨_, _, _, _, .imported (.uint53__lean_mk_array α)⟩] | _ => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .typed t⟩ => [⟨_, _, _, _, .imported (.typedArray__uint53__lean_mk_array t)⟩] | _ => [])

/-- The operations of `lean_mk_empty_array_with_capacity__Array_emptyWithCapacity`. -/
def «cands_lean_mk_empty_array_with_capacity__Array_emptyWithCapacity» (σs : List JsTy) (τ : JsTy) : List Cand :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .generic α⟩ => [⟨_, _, _, _, .inlined (.bigint_nat__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity α)⟩] | _ => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .typed t⟩ => [⟨_, _, _, _, .inlined (.typedArray__bigint_nat__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity t)⟩] | _ => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .generic α⟩ => [⟨_, _, _, _, .inlined (.uint53__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity α)⟩] | _ => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .typed t⟩ => [⟨_, _, _, _, .inlined (.typedArray__uint53__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity t)⟩] | _ => [])

/-- The operations of `lean_mk_empty_array_with_capacity__Array_mkEmpty`. -/
def «cands_lean_mk_empty_array_with_capacity__Array_mkEmpty» (σs : List JsTy) (τ : JsTy) : List Cand :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .generic α⟩ => [⟨_, _, _, _, .inlined (.bigint_nat__lean_mk_empty_array_with_capacity__Array_mkEmpty α)⟩] | _ => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .typed t⟩ => [⟨_, _, _, _, .inlined (.typedArray__bigint_nat__lean_mk_empty_array_with_capacity__Array_mkEmpty t)⟩] | _ => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .generic α⟩ => [⟨_, _, _, _, .inlined (.uint53__lean_mk_empty_array_with_capacity__Array_mkEmpty α)⟩] | _ => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .typed t⟩ => [⟨_, _, _, _, .inlined (.typedArray__uint53__lean_mk_empty_array_with_capacity__Array_mkEmpty t)⟩] | _ => [])

/-- The operations of `lean_mk_thunk`. -/
def «cands_lean_mk_thunk» (σs : List JsTy) (τ : JsTy) : List Cand :=
  [⟨_, _, _, _, .imported (.thunk__lean_mk_thunk (elemOf? (σs ++ [τ])))⟩]

/-- The operations of `lean_nat_abs`. -/
def «cands_lean_nat_abs» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__bigint_nat__lean_nat_abs⟩, ⟨_, _, _, _, .imported .bigint_int__uint53__lean_nat_abs⟩, ⟨_, _, _, _, .imported .int53__bigint_nat__lean_nat_abs⟩, ⟨_, _, _, _, .imported .int53__uint53__lean_nat_abs⟩]

/-- The operations of `lean_nat_add`. -/
def «cands_lean_nat_add» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_nat__lean_nat_add⟩, ⟨_, _, _, _, .imported .uint53__lean_nat_add⟩]

/-- The operations of `lean_nat_dec_eq__Nat_beq`. -/
def «cands_lean_nat_dec_eq__Nat_beq» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_nat__lean_nat_dec_eq__Nat_beq⟩, ⟨_, _, _, _, .inlined .uint53__lean_nat_dec_eq__Nat_beq⟩]

/-- The operations of `lean_nat_dec_eq__Nat_decEq`. -/
def «cands_lean_nat_dec_eq__Nat_decEq» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_nat__lean_nat_dec_eq__Nat_decEq⟩, ⟨_, _, _, _, .inlined .uint53__lean_nat_dec_eq__Nat_decEq⟩]

/-- The operations of `lean_nat_dec_le__Nat_ble`. -/
def «cands_lean_nat_dec_le__Nat_ble» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_nat__lean_nat_dec_le__Nat_ble⟩, ⟨_, _, _, _, .inlined .uint53__lean_nat_dec_le__Nat_ble⟩]

/-- The operations of `lean_nat_dec_le__Nat_decLe`. -/
def «cands_lean_nat_dec_le__Nat_decLe» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_nat__lean_nat_dec_le__Nat_decLe⟩, ⟨_, _, _, _, .inlined .uint53__lean_nat_dec_le__Nat_decLe⟩]

/-- The operations of `lean_nat_dec_lt`. -/
def «cands_lean_nat_dec_lt» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_nat__lean_nat_dec_lt⟩, ⟨_, _, _, _, .inlined .uint53__lean_nat_dec_lt⟩]

/-- The operations of `lean_nat_div`. -/
def «cands_lean_nat_div» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_nat_div⟩, ⟨_, _, _, _, .imported .uint53__lean_nat_div⟩]

/-- The operations of `lean_nat_div_exact`. -/
def «cands_lean_nat_div_exact» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_nat_div_exact⟩, ⟨_, _, _, _, .imported .uint53__lean_nat_div_exact⟩]

/-- The operations of `lean_nat_land`. -/
def «cands_lean_nat_land» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_nat__lean_nat_land⟩, ⟨_, _, _, _, .imported .uint53__lean_nat_land⟩]

/-- The operations of `lean_nat_log2`. -/
def «cands_lean_nat_log2» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_nat_log2⟩, ⟨_, _, _, _, .imported .uint53__lean_nat_log2⟩]

/-- The operations of `lean_nat_lor`. -/
def «cands_lean_nat_lor» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_nat__lean_nat_lor⟩, ⟨_, _, _, _, .imported .uint53__lean_nat_lor⟩]

/-- The operations of `lean_nat_lxor`. -/
def «cands_lean_nat_lxor» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_nat__lean_nat_lxor⟩, ⟨_, _, _, _, .imported .uint53__lean_nat_lxor⟩]

/-- The operations of `lean_nat_mod__Nat_mod`. -/
def «cands_lean_nat_mod__Nat_mod» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_nat_mod__Nat_mod⟩, ⟨_, _, _, _, .imported .uint53__lean_nat_mod__Nat_mod⟩]

/-- The operations of `lean_nat_mod__Nat_modCore`. -/
def «cands_lean_nat_mod__Nat_modCore» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_nat_mod__Nat_mod⟩, ⟨_, _, _, _, .imported .uint53__lean_nat_mod__Nat_mod⟩]

/-- The operations of `lean_nat_mul`. -/
def «cands_lean_nat_mul» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_nat__lean_nat_mul⟩, ⟨_, _, _, _, .imported .uint53__lean_nat_mul⟩]

/-- The operations of `lean_nat_pow`. -/
def «cands_lean_nat_pow» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_nat_pow⟩, ⟨_, _, _, _, .imported .uint53__lean_nat_pow⟩]

/-- The operations of `lean_nat_pred`. -/
def «cands_lean_nat_pred» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_nat_pred⟩, ⟨_, _, _, _, .imported .uint53__lean_nat_pred⟩]

/-- The operations of `lean_nat_shiftl`. -/
def «cands_lean_nat_shiftl» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_nat__lean_nat_shiftl⟩, ⟨_, _, _, _, .imported .uint53__lean_nat_shiftl⟩]

/-- The operations of `lean_nat_shiftr`. -/
def «cands_lean_nat_shiftr» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_nat__lean_nat_shiftr⟩, ⟨_, _, _, _, .imported .uint53__lean_nat_shiftr⟩]

/-- The operations of `lean_nat_sub`. -/
def «cands_lean_nat_sub» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_nat_sub⟩, ⟨_, _, _, _, .imported .uint53__lean_nat_sub⟩]

/-- The operations of `lean_nat_to_int`. -/
def «cands_lean_nat_to_int» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_nat__bigint_int__lean_nat_to_int⟩, ⟨_, _, _, _, .imported .bigint_nat__int53__lean_nat_to_int⟩, ⟨_, _, _, _, .inlined .uint53__bigint_int__lean_nat_to_int⟩, ⟨_, _, _, _, .inlined .uint53__int53__lean_nat_to_int⟩]

/-- The operations of `lean_slice_dec_lt`. -/
def «cands_lean_slice_dec_lt» : List Cand :=
  [⟨_, _, _, _, .imported .stringSlice__lean_slice_dec_lt⟩]

/-- The operations of `lean_slice_hash`. -/
def «cands_lean_slice_hash» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_slice_hash⟩, ⟨_, _, _, _, .imported .uint53__lean_slice_hash⟩]

/-- The operations of `lean_strict_and`. -/
def «cands_lean_strict_and» : List Cand :=
  [⟨_, _, _, _, .inlined .bool__lean_strict_and⟩]

/-- The operations of `lean_strict_or`. -/
def «cands_lean_strict_or» : List Cand :=
  [⟨_, _, _, _, .inlined .bool__lean_strict_or⟩]

/-- The operations of `lean_string_any`. -/
def «cands_lean_string_any» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_any⟩]

/-- The operations of `lean_string_append__String_Internal_append`. -/
def «cands_lean_string_append__String_Internal_append» : List Cand :=
  [⟨_, _, _, _, .inlined .string__lean_string_append__String_Internal_append⟩]

/-- The operations of `lean_string_append__String_append`. -/
def «cands_lean_string_append__String_append» : List Cand :=
  [⟨_, _, _, _, .inlined .string__lean_string_append__String_append⟩]

/-- The operations of `lean_string_capitalize`. -/
def «cands_lean_string_capitalize» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_capitalize⟩]

/-- The operations of `lean_string_compare`. -/
def «cands_lean_string_compare» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_compare⟩]

/-- The operations of `lean_string_contains`. -/
def «cands_lean_string_contains» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_contains⟩]

/-- The operations of `lean_string_data__String_data`. -/
def «cands_lean_string_data__String_data» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_data__String_data⟩]

/-- The operations of `lean_string_data__String_toList`. -/
def «cands_lean_string_data__String_toList» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_data__String_data⟩]

/-- The operations of `lean_string_dec_eq`. -/
def «cands_lean_string_dec_eq» : List Cand :=
  [⟨_, _, _, _, .inlined .string__lean_string_dec_eq⟩]

/-- The operations of `lean_string_dec_lt`. -/
def «cands_lean_string_dec_lt» : List Cand :=
  [⟨_, _, _, _, .inlined .string__lean_string_dec_lt⟩]

/-- The operations of `lean_string_drop`. -/
def «cands_lean_string_drop» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_string_drop⟩, ⟨_, _, _, _, .imported .uint53__lean_string_drop⟩]

/-- The operations of `lean_string_dropright`. -/
def «cands_lean_string_dropright» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_string_dropright⟩, ⟨_, _, _, _, .imported .uint53__lean_string_dropright⟩]

/-- The operations of `lean_string_foldl`. -/
def «cands_lean_string_foldl» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_foldl⟩]

/-- The operations of `lean_string_front`. -/
def «cands_lean_string_front» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_front⟩]

/-- The operations of `lean_string_get_byte_fast__String_Internal_getUTF8Byte`. -/
def «cands_lean_string_get_byte_fast__String_Internal_getUTF8Byte» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_string_get_byte_fast__String_Internal_getUTF8Byte⟩, ⟨_, _, _, _, .imported .uint53__lean_string_get_byte_fast__String_Internal_getUTF8Byte⟩]

/-- The operations of `lean_string_get_byte_fast__String_getUTF8Byte`. -/
def «cands_lean_string_get_byte_fast__String_getUTF8Byte» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_get_byte_fast__String_getUTF8Byte⟩]

/-- The operations of `lean_string_get_byte_fast__String_getUtf8Byte`. -/
def «cands_lean_string_get_byte_fast__String_getUtf8Byte» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_get_byte_fast__String_getUTF8Byte⟩]

/-- The operations of `lean_string_hash`. -/
def «cands_lean_string_hash» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_string_hash⟩, ⟨_, _, _, _, .imported .uint53__lean_string_hash⟩]

/-- The operations of `lean_string_intercalate`. -/
def «cands_lean_string_intercalate» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_intercalate⟩]

/-- The operations of `lean_string_is_valid_pos`. -/
def «cands_lean_string_is_valid_pos» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_is_valid_pos⟩]

/-- The operations of `lean_string_isempty`. -/
def «cands_lean_string_isempty» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_isempty⟩]

/-- The operations of `lean_string_isprefixof`. -/
def «cands_lean_string_isprefixof» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_isprefixof⟩]

/-- The operations of `lean_string_length__String_Internal_length`. -/
def «cands_lean_string_length__String_Internal_length» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_string_length__String_Internal_length⟩, ⟨_, _, _, _, .imported .uint53__lean_string_length__String_Internal_length⟩]

/-- The operations of `lean_string_length__String_length`. -/
def «cands_lean_string_length__String_length» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_string_length__String_Internal_length⟩, ⟨_, _, _, _, .imported .uint53__lean_string_length__String_Internal_length⟩]

/-- The operations of `lean_string_memcmp`. -/
def «cands_lean_string_memcmp» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_memcmp⟩]

/-- The operations of `lean_string_mk__String_mk`. -/
def «cands_lean_string_mk__String_mk» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_mk__String_mk⟩]

/-- The operations of `lean_string_mk__String_ofList`. -/
def «cands_lean_string_mk__String_ofList» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_mk__String_mk⟩]

/-- The operations of `lean_string_nextwhile`. -/
def «cands_lean_string_nextwhile» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_nextwhile⟩]

/-- The operations of `lean_string_offsetofpos`. -/
def «cands_lean_string_offsetofpos» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_string_offsetofpos⟩, ⟨_, _, _, _, .imported .uint53__lean_string_offsetofpos⟩]

/-- The operations of `lean_string_pos_min`. -/
def «cands_lean_string_pos_min» : List Cand :=
  [⟨_, _, _, _, .imported .uint53__lean_string_pos_min⟩]

/-- The operations of `lean_string_pos_sub`. -/
def «cands_lean_string_pos_sub» : List Cand :=
  [⟨_, _, _, _, .imported .uint53__lean_string_pos_sub⟩]

/-- The operations of `lean_string_posof`. -/
def «cands_lean_string_posof» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_posof⟩]

/-- The operations of `lean_string_push`. -/
def «cands_lean_string_push» : List Cand :=
  [⟨_, _, _, _, .inlined .string__lean_string_push⟩]

/-- The operations of `lean_string_pushn`. -/
def «cands_lean_string_pushn» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_string_pushn⟩, ⟨_, _, _, _, .imported .uint53__lean_string_pushn⟩]

/-- The operations of `lean_string_trim`. -/
def «cands_lean_string_trim» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_trim⟩]

/-- The operations of `lean_string_utf8_at_end__String_Internal_atEnd`. -/
def «cands_lean_string_utf8_at_end__String_Internal_atEnd» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_utf8_at_end__String_Internal_atEnd⟩]

/-- The operations of `lean_string_utf8_at_end__String_Pos_Raw_atEnd`. -/
def «cands_lean_string_utf8_at_end__String_Pos_Raw_atEnd» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_utf8_at_end__String_Internal_atEnd⟩]

/-- The operations of `lean_string_utf8_at_end__String_atEnd`. -/
def «cands_lean_string_utf8_at_end__String_atEnd» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_utf8_at_end__String_Internal_atEnd⟩]

/-- The operations of `lean_string_utf8_byte_size`. -/
def «cands_lean_string_utf8_byte_size» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_string_utf8_byte_size⟩, ⟨_, _, _, _, .imported .uint53__lean_string_utf8_byte_size⟩]

/-- The operations of `lean_string_utf8_extract__String_Internal_extract`. -/
def «cands_lean_string_utf8_extract__String_Internal_extract» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_utf8_extract__String_Internal_extract⟩]

/-- The operations of `lean_string_utf8_extract__String_Pos_Raw_extract`. -/
def «cands_lean_string_utf8_extract__String_Pos_Raw_extract» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_utf8_extract__String_Internal_extract⟩]

/-- The operations of `lean_string_utf8_extract_fast`. -/
def «cands_lean_string_utf8_extract_fast» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_utf8_extract_fast⟩]

/-- The operations of `lean_string_utf8_get__String_Internal_get`. -/
def «cands_lean_string_utf8_get__String_Internal_get» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_utf8_get__String_Internal_get⟩]

/-- The operations of `lean_string_utf8_get__String_Pos_Raw_get`. -/
def «cands_lean_string_utf8_get__String_Pos_Raw_get» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_utf8_get__String_Internal_get⟩]

/-- The operations of `lean_string_utf8_get__String_get`. -/
def «cands_lean_string_utf8_get__String_get» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_utf8_get__String_Internal_get⟩]

/-- The operations of `lean_string_utf8_get_bang__String_Pos_Raw_get!`. -/
def «cands_lean_string_utf8_get_bang__String_Pos_Raw_get!» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_utf8_get_bang__String_Pos_Raw_get!⟩]

/-- The operations of `lean_string_utf8_get_bang__String_get!`. -/
def «cands_lean_string_utf8_get_bang__String_get!» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_utf8_get_bang__String_Pos_Raw_get!⟩]

/-- The operations of `lean_string_utf8_get_fast__String_Pos_Raw_get'`. -/
def «cands_lean_string_utf8_get_fast__String_Pos_Raw_get'» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_utf8_get_bang__String_Pos_Raw_get!⟩]

/-- The operations of `lean_string_utf8_get_fast__String_get'`. -/
def «cands_lean_string_utf8_get_fast__String_get'» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_utf8_get_bang__String_Pos_Raw_get!⟩]

/-- The operations of `lean_string_utf8_get_opt__String_Pos_Raw_get?`. -/
def «cands_lean_string_utf8_get_opt__String_Pos_Raw_get?» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_utf8_get_opt__String_Pos_Raw_get?⟩]

/-- The operations of `lean_string_utf8_get_opt__String_get?`. -/
def «cands_lean_string_utf8_get_opt__String_get?» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_utf8_get_opt__String_Pos_Raw_get?⟩]

/-- The operations of `lean_string_utf8_next__String_Internal_next`. -/
def «cands_lean_string_utf8_next__String_Internal_next» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_utf8_next__String_Internal_next⟩]

/-- The operations of `lean_string_utf8_next__String_Pos_Raw_next`. -/
def «cands_lean_string_utf8_next__String_Pos_Raw_next» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_utf8_next__String_Internal_next⟩]

/-- The operations of `lean_string_utf8_next__String_next`. -/
def «cands_lean_string_utf8_next__String_next» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_utf8_next__String_Internal_next⟩]

/-- The operations of `lean_string_utf8_next_fast__String_Pos_next`. -/
def «cands_lean_string_utf8_next_fast__String_Pos_next» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_utf8_next_fast__String_Pos_next⟩]

/-- The operations of `lean_string_utf8_next_fast__String_next'`. -/
def «cands_lean_string_utf8_next_fast__String_next'» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_utf8_next_fast__String_next'⟩]

/-- The operations of `lean_string_utf8_prev__String_Pos_Raw_prev`. -/
def «cands_lean_string_utf8_prev__String_Pos_Raw_prev» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_utf8_prev__String_Pos_Raw_prev⟩]

/-- The operations of `lean_string_utf8_prev__String_prev`. -/
def «cands_lean_string_utf8_prev__String_prev» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_utf8_prev__String_Pos_Raw_prev⟩]

/-- The operations of `lean_string_utf8_set__String_Pos_Raw_set`. -/
def «cands_lean_string_utf8_set__String_Pos_Raw_set» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_utf8_set__String_Pos_Raw_set⟩]

/-- The operations of `lean_string_utf8_set__String_Pos_set`. -/
def «cands_lean_string_utf8_set__String_Pos_set» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_utf8_set__String_Pos_set⟩]

/-- The operations of `lean_string_utf8_set__String_set`. -/
def «cands_lean_string_utf8_set__String_set» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_string_utf8_set__String_Pos_Raw_set⟩]

/-- The operations of `lean_substring_all`. -/
def «cands_lean_substring_all» : List Cand :=
  [⟨_, _, _, _, .imported .substring__lean_substring_all⟩]

/-- The operations of `lean_substring_beq`. -/
def «cands_lean_substring_beq» : List Cand :=
  [⟨_, _, _, _, .imported .substring__lean_substring_beq⟩]

/-- The operations of `lean_substring_drop`. -/
def «cands_lean_substring_drop» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_substring_drop⟩, ⟨_, _, _, _, .imported .uint53__lean_substring_drop⟩]

/-- The operations of `lean_substring_extract`. -/
def «cands_lean_substring_extract» : List Cand :=
  [⟨_, _, _, _, .imported .substring__lean_substring_extract⟩]

/-- The operations of `lean_substring_front`. -/
def «cands_lean_substring_front» : List Cand :=
  [⟨_, _, _, _, .imported .substring__lean_substring_front⟩]

/-- The operations of `lean_substring_get`. -/
def «cands_lean_substring_get» : List Cand :=
  [⟨_, _, _, _, .imported .substring__lean_substring_get⟩]

/-- The operations of `lean_substring_isempty`. -/
def «cands_lean_substring_isempty» : List Cand :=
  [⟨_, _, _, _, .imported .substring__lean_substring_isempty⟩]

/-- The operations of `lean_substring_prev`. -/
def «cands_lean_substring_prev» : List Cand :=
  [⟨_, _, _, _, .imported .substring__lean_substring_prev⟩]

/-- The operations of `lean_substring_takewhile`. -/
def «cands_lean_substring_takewhile» : List Cand :=
  [⟨_, _, _, _, .imported .substring__lean_substring_takewhile⟩]

/-- The operations of `lean_substring_tostring`. -/
def «cands_lean_substring_tostring» : List Cand :=
  [⟨_, _, _, _, .imported .substring__lean_substring_tostring⟩]

/-- The operations of `lean_system_platform_emscripten`. -/
def «cands_lean_system_platform_emscripten» : List Cand :=
  [⟨_, _, _, _, .imported .bool__lean_system_platform_emscripten⟩]

/-- The operations of `lean_system_platform_target`. -/
def «cands_lean_system_platform_target» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_system_platform_target⟩]

/-- The operations of `lean_thunk_get_own`. -/
def «cands_lean_thunk_get_own» (σs : List JsTy) (τ : JsTy) : List Cand :=
  [⟨_, _, _, _, .imported (.thunk__lean_thunk_get_own (elemOf? (σs ++ [τ])))⟩]

/-- The operations of `lean_thunk_pure`. -/
def «cands_lean_thunk_pure» (σs : List JsTy) (τ : JsTy) : List Cand :=
  [⟨_, _, _, _, .imported (.thunk__lean_thunk_pure (elemOf? (σs ++ [τ])))⟩]

/-- The operations of `lean_uint16_add`. -/
def «cands_lean_uint16_add» : List Cand :=
  [⟨_, _, _, _, .imported .uint16__lean_uint16_add⟩]

/-- The operations of `lean_uint16_complement`. -/
def «cands_lean_uint16_complement» : List Cand :=
  [⟨_, _, _, _, .imported .uint16__lean_uint16_complement⟩]

/-- The operations of `lean_uint16_dec_eq`. -/
def «cands_lean_uint16_dec_eq» : List Cand :=
  [⟨_, _, _, _, .inlined .uint16__lean_uint16_dec_eq⟩]

/-- The operations of `lean_uint16_dec_le`. -/
def «cands_lean_uint16_dec_le» : List Cand :=
  [⟨_, _, _, _, .inlined .uint16__lean_uint16_dec_le⟩]

/-- The operations of `lean_uint16_dec_lt`. -/
def «cands_lean_uint16_dec_lt» : List Cand :=
  [⟨_, _, _, _, .inlined .uint16__lean_uint16_dec_lt⟩]

/-- The operations of `lean_uint16_div`. -/
def «cands_lean_uint16_div» : List Cand :=
  [⟨_, _, _, _, .imported .uint16__lean_uint16_div⟩]

/-- The operations of `lean_uint16_land`. -/
def «cands_lean_uint16_land» : List Cand :=
  [⟨_, _, _, _, .imported .uint16__lean_uint16_land⟩]

/-- The operations of `lean_uint16_log2`. -/
def «cands_lean_uint16_log2» : List Cand :=
  [⟨_, _, _, _, .imported .uint16__lean_uint16_log2⟩]

/-- The operations of `lean_uint16_lor`. -/
def «cands_lean_uint16_lor» : List Cand :=
  [⟨_, _, _, _, .imported .uint16__lean_uint16_lor⟩]

/-- The operations of `lean_uint16_mod`. -/
def «cands_lean_uint16_mod» : List Cand :=
  [⟨_, _, _, _, .imported .uint16__lean_uint16_mod⟩]

/-- The operations of `lean_uint16_mul`. -/
def «cands_lean_uint16_mul» : List Cand :=
  [⟨_, _, _, _, .imported .uint16__lean_uint16_mul⟩]

/-- The operations of `lean_uint16_neg`. -/
def «cands_lean_uint16_neg» : List Cand :=
  [⟨_, _, _, _, .imported .uint16__lean_uint16_neg⟩]

/-- The operations of `lean_uint16_of_nat__UInt16_ofNat`. -/
def «cands_lean_uint16_of_nat__UInt16_ofNat» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_uint16_of_nat__UInt16_ofNat⟩, ⟨_, _, _, _, .imported .uint53__lean_uint16_of_nat__UInt16_ofNat⟩]

/-- The operations of `lean_uint16_of_nat__UInt16_ofNatLT`. -/
def «cands_lean_uint16_of_nat__UInt16_ofNatLT» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_uint16_of_nat__UInt16_ofNat⟩, ⟨_, _, _, _, .imported .uint53__lean_uint16_of_nat__UInt16_ofNat⟩]

/-- The operations of `lean_uint16_of_nat_mk`. -/
def «cands_lean_uint16_of_nat_mk» : List Cand :=
  [⟨_, _, _, _, .inlined .bitvec16__lean_uint16_of_nat_mk⟩]

/-- The operations of `lean_uint16_shift_left`. -/
def «cands_lean_uint16_shift_left» : List Cand :=
  [⟨_, _, _, _, .imported .uint16__lean_uint16_shift_left⟩]

/-- The operations of `lean_uint16_shift_right`. -/
def «cands_lean_uint16_shift_right» : List Cand :=
  [⟨_, _, _, _, .imported .uint16__lean_uint16_shift_right⟩]

/-- The operations of `lean_uint16_sub`. -/
def «cands_lean_uint16_sub» : List Cand :=
  [⟨_, _, _, _, .imported .uint16__lean_uint16_sub⟩]

/-- The operations of `lean_uint16_to_float`. -/
def «cands_lean_uint16_to_float» : List Cand :=
  [⟨_, _, _, _, .inlined .uint16__lean_uint16_to_float⟩]

/-- The operations of `lean_uint16_to_float32`. -/
def «cands_lean_uint16_to_float32» : List Cand :=
  [⟨_, _, _, _, .inlined .uint16__lean_uint16_to_float32⟩]

/-- The operations of `lean_uint16_to_nat__UInt16_toBitVec`. -/
def «cands_lean_uint16_to_nat__UInt16_toBitVec» : List Cand :=
  [⟨_, _, _, _, .inlined .uint16__lean_uint16_to_nat__UInt16_toBitVec⟩]

/-- The operations of `lean_uint16_to_nat__UInt16_toNat`. -/
def «cands_lean_uint16_to_nat__UInt16_toNat» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_nat__lean_uint16_to_nat__UInt16_toNat⟩, ⟨_, _, _, _, .inlined .uint53__lean_uint16_to_nat__UInt16_toNat⟩]

/-- The operations of `lean_uint16_to_uint32`. -/
def «cands_lean_uint16_to_uint32» : List Cand :=
  [⟨_, _, _, _, .inlined .uint16__lean_uint16_to_uint32⟩]

/-- The operations of `lean_uint16_to_uint64`. -/
def «cands_lean_uint16_to_uint64» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_nat__lean_uint16_to_uint64⟩, ⟨_, _, _, _, .inlined .uint53__lean_uint16_to_uint64⟩]

/-- The operations of `lean_uint16_to_uint8`. -/
def «cands_lean_uint16_to_uint8» : List Cand :=
  [⟨_, _, _, _, .imported .uint16__lean_uint16_to_uint8⟩]

/-- The operations of `lean_uint16_xor`. -/
def «cands_lean_uint16_xor» : List Cand :=
  [⟨_, _, _, _, .imported .uint16__lean_uint16_xor⟩]

/-- The operations of `lean_uint32_add`. -/
def «cands_lean_uint32_add» : List Cand :=
  [⟨_, _, _, _, .imported .uint32__lean_uint32_add⟩]

/-- The operations of `lean_uint32_complement`. -/
def «cands_lean_uint32_complement» : List Cand :=
  [⟨_, _, _, _, .imported .uint32__lean_uint32_complement⟩]

/-- The operations of `lean_uint32_dec_eq`. -/
def «cands_lean_uint32_dec_eq» : List Cand :=
  [⟨_, _, _, _, .inlined .uint32__lean_uint32_dec_eq⟩]

/-- The operations of `lean_uint32_dec_le`. -/
def «cands_lean_uint32_dec_le» : List Cand :=
  [⟨_, _, _, _, .inlined .uint32__lean_uint32_dec_le⟩]

/-- The operations of `lean_uint32_dec_lt`. -/
def «cands_lean_uint32_dec_lt» : List Cand :=
  [⟨_, _, _, _, .inlined .uint32__lean_uint32_dec_lt⟩]

/-- The operations of `lean_uint32_div`. -/
def «cands_lean_uint32_div» : List Cand :=
  [⟨_, _, _, _, .imported .uint32__lean_uint32_div⟩]

/-- The operations of `lean_uint32_land`. -/
def «cands_lean_uint32_land» : List Cand :=
  [⟨_, _, _, _, .imported .uint32__lean_uint32_land⟩]

/-- The operations of `lean_uint32_log2`. -/
def «cands_lean_uint32_log2» : List Cand :=
  [⟨_, _, _, _, .imported .uint32__lean_uint32_log2⟩]

/-- The operations of `lean_uint32_lor`. -/
def «cands_lean_uint32_lor» : List Cand :=
  [⟨_, _, _, _, .imported .uint32__lean_uint32_lor⟩]

/-- The operations of `lean_uint32_mod`. -/
def «cands_lean_uint32_mod» : List Cand :=
  [⟨_, _, _, _, .imported .uint32__lean_uint32_mod⟩]

/-- The operations of `lean_uint32_mul`. -/
def «cands_lean_uint32_mul» : List Cand :=
  [⟨_, _, _, _, .imported .uint32__lean_uint32_mul⟩]

/-- The operations of `lean_uint32_neg`. -/
def «cands_lean_uint32_neg» : List Cand :=
  [⟨_, _, _, _, .imported .uint32__lean_uint32_neg⟩]

/-- The operations of `lean_uint32_of_nat__Char_ofNatAux`. -/
def «cands_lean_uint32_of_nat__Char_ofNatAux» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_uint32_of_nat__Char_ofNatAux⟩, ⟨_, _, _, _, .imported .uint53__lean_uint32_of_nat__Char_ofNatAux⟩]

/-- The operations of `lean_uint32_of_nat__UInt32_ofNat`. -/
def «cands_lean_uint32_of_nat__UInt32_ofNat» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_uint32_of_nat__UInt32_ofNat⟩, ⟨_, _, _, _, .imported .uint53__lean_uint32_of_nat__UInt32_ofNat⟩]

/-- The operations of `lean_uint32_of_nat__UInt32_ofNatLT`. -/
def «cands_lean_uint32_of_nat__UInt32_ofNatLT» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_uint32_of_nat__UInt32_ofNat⟩, ⟨_, _, _, _, .imported .uint53__lean_uint32_of_nat__UInt32_ofNat⟩]

/-- The operations of `lean_uint32_of_nat_mk`. -/
def «cands_lean_uint32_of_nat_mk» : List Cand :=
  [⟨_, _, _, _, .inlined .bitvec32__lean_uint32_of_nat_mk⟩]

/-- The operations of `lean_uint32_shift_left`. -/
def «cands_lean_uint32_shift_left» : List Cand :=
  [⟨_, _, _, _, .imported .uint32__lean_uint32_shift_left⟩]

/-- The operations of `lean_uint32_shift_right`. -/
def «cands_lean_uint32_shift_right» : List Cand :=
  [⟨_, _, _, _, .imported .uint32__lean_uint32_shift_right⟩]

/-- The operations of `lean_uint32_sub`. -/
def «cands_lean_uint32_sub» : List Cand :=
  [⟨_, _, _, _, .imported .uint32__lean_uint32_sub⟩]

/-- The operations of `lean_uint32_to_float`. -/
def «cands_lean_uint32_to_float» : List Cand :=
  [⟨_, _, _, _, .inlined .uint32__lean_uint32_to_float⟩]

/-- The operations of `lean_uint32_to_float32`. -/
def «cands_lean_uint32_to_float32» : List Cand :=
  [⟨_, _, _, _, .inlined .uint32__lean_uint32_to_float32⟩]

/-- The operations of `lean_uint32_to_nat__UInt32_toBitVec`. -/
def «cands_lean_uint32_to_nat__UInt32_toBitVec» : List Cand :=
  [⟨_, _, _, _, .inlined .uint32__lean_uint32_to_nat__UInt32_toBitVec⟩]

/-- The operations of `lean_uint32_to_nat__UInt32_toNat`. -/
def «cands_lean_uint32_to_nat__UInt32_toNat» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_nat__lean_uint32_to_nat__UInt32_toNat⟩, ⟨_, _, _, _, .inlined .uint53__lean_uint32_to_nat__UInt32_toNat⟩]

/-- The operations of `lean_uint32_to_uint16`. -/
def «cands_lean_uint32_to_uint16» : List Cand :=
  [⟨_, _, _, _, .imported .uint32__lean_uint32_to_uint16⟩]

/-- The operations of `lean_uint32_to_uint64`. -/
def «cands_lean_uint32_to_uint64» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_nat__lean_uint32_to_uint64⟩, ⟨_, _, _, _, .inlined .uint53__lean_uint32_to_uint64⟩]

/-- The operations of `lean_uint32_to_uint8`. -/
def «cands_lean_uint32_to_uint8» : List Cand :=
  [⟨_, _, _, _, .imported .uint32__lean_uint32_to_uint8⟩]

/-- The operations of `lean_uint32_xor`. -/
def «cands_lean_uint32_xor» : List Cand :=
  [⟨_, _, _, _, .imported .uint32__lean_uint32_xor⟩]

/-- The operations of `lean_uint64_add`. -/
def «cands_lean_uint64_add» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_uint64_add⟩, ⟨_, _, _, _, .imported .uint53__lean_uint64_add⟩]

/-- The operations of `lean_uint64_complement`. -/
def «cands_lean_uint64_complement» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_uint64_complement⟩, ⟨_, _, _, _, .imported .uint53__lean_uint64_complement⟩]

/-- The operations of `lean_uint64_dec_eq`. -/
def «cands_lean_uint64_dec_eq» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_nat__lean_uint64_dec_eq⟩, ⟨_, _, _, _, .inlined .uint53__lean_uint64_dec_eq⟩]

/-- The operations of `lean_uint64_dec_le`. -/
def «cands_lean_uint64_dec_le» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_nat__lean_uint64_dec_le⟩, ⟨_, _, _, _, .inlined .uint53__lean_uint64_dec_le⟩]

/-- The operations of `lean_uint64_dec_lt`. -/
def «cands_lean_uint64_dec_lt» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_nat__lean_uint64_dec_lt⟩, ⟨_, _, _, _, .inlined .uint53__lean_uint64_dec_lt⟩]

/-- The operations of `lean_uint64_div`. -/
def «cands_lean_uint64_div» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_uint64_div⟩, ⟨_, _, _, _, .imported .uint53__lean_uint64_div⟩]

/-- The operations of `lean_uint64_land`. -/
def «cands_lean_uint64_land» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_uint64_land⟩, ⟨_, _, _, _, .imported .uint53__lean_uint64_land⟩]

/-- The operations of `lean_uint64_log2`. -/
def «cands_lean_uint64_log2» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_uint64_log2⟩, ⟨_, _, _, _, .imported .uint53__lean_uint64_log2⟩]

/-- The operations of `lean_uint64_lor`. -/
def «cands_lean_uint64_lor» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_uint64_lor⟩, ⟨_, _, _, _, .imported .uint53__lean_uint64_lor⟩]

/-- The operations of `lean_uint64_mix_hash`. -/
def «cands_lean_uint64_mix_hash» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_uint64_mix_hash⟩, ⟨_, _, _, _, .imported .uint53__lean_uint64_mix_hash⟩]

/-- The operations of `lean_uint64_mod`. -/
def «cands_lean_uint64_mod» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_uint64_mod⟩, ⟨_, _, _, _, .imported .uint53__lean_uint64_mod⟩]

/-- The operations of `lean_uint64_mul`. -/
def «cands_lean_uint64_mul» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_uint64_mul⟩, ⟨_, _, _, _, .imported .uint53__lean_uint64_mul⟩]

/-- The operations of `lean_uint64_neg`. -/
def «cands_lean_uint64_neg» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_uint64_neg⟩, ⟨_, _, _, _, .imported .uint53__lean_uint64_neg⟩]

/-- The operations of `lean_uint64_of_nat__UInt64_ofNat`. -/
def «cands_lean_uint64_of_nat__UInt64_ofNat» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_uint64_of_nat__UInt64_ofNat⟩, ⟨_, _, _, _, .imported .bigint_nat__uint53__lean_uint64_of_nat__UInt64_ofNat⟩, ⟨_, _, _, _, .imported .uint53__bigint_nat__lean_uint64_of_nat__UInt64_ofNat⟩, ⟨_, _, _, _, .imported .uint53__lean_uint64_of_nat__UInt64_ofNat⟩]

/-- The operations of `lean_uint64_of_nat__UInt64_ofNatLT`. -/
def «cands_lean_uint64_of_nat__UInt64_ofNatLT» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_uint64_of_nat__UInt64_ofNat⟩, ⟨_, _, _, _, .imported .bigint_nat__uint53__lean_uint64_of_nat__UInt64_ofNat⟩, ⟨_, _, _, _, .imported .uint53__bigint_nat__lean_uint64_of_nat__UInt64_ofNatLT⟩, ⟨_, _, _, _, .imported .uint53__lean_uint64_of_nat__UInt64_ofNatLT⟩]

/-- The operations of `lean_uint64_of_nat_mk`. -/
def «cands_lean_uint64_of_nat_mk» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_bitvec64__bigint_nat__lean_uint64_of_nat_mk⟩, ⟨_, _, _, _, .imported .bigint_bitvec64__uint53__lean_uint64_of_nat_mk⟩, ⟨_, _, _, _, .inlined .int53_bitvec64__bigint_nat__lean_uint64_of_nat_mk⟩, ⟨_, _, _, _, .inlined .int53_bitvec64__uint53__lean_uint64_of_nat_mk⟩]

/-- The operations of `lean_uint64_shift_left`. -/
def «cands_lean_uint64_shift_left» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_uint64_shift_left⟩, ⟨_, _, _, _, .imported .uint53__lean_uint64_shift_left⟩]

/-- The operations of `lean_uint64_shift_right`. -/
def «cands_lean_uint64_shift_right» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_uint64_shift_right⟩, ⟨_, _, _, _, .imported .uint53__lean_uint64_shift_right⟩]

/-- The operations of `lean_uint64_sub`. -/
def «cands_lean_uint64_sub» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_uint64_sub⟩, ⟨_, _, _, _, .imported .uint53__lean_uint64_sub⟩]

/-- The operations of `lean_uint64_to_float`. -/
def «cands_lean_uint64_to_float» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_nat__lean_uint64_to_float⟩, ⟨_, _, _, _, .inlined .uint53__lean_uint64_to_float⟩]

/-- The operations of `lean_uint64_to_float32`. -/
def «cands_lean_uint64_to_float32» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_nat__lean_uint64_to_float32⟩, ⟨_, _, _, _, .inlined .uint53__lean_uint64_to_float32⟩]

/-- The operations of `lean_uint64_to_nat__UInt64_toBitVec`. -/
def «cands_lean_uint64_to_nat__UInt64_toBitVec» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_nat__bigint_bitvec64__lean_uint64_to_nat__UInt64_toBitVec⟩, ⟨_, _, _, _, .imported .bigint_nat__int53_bitvec64__lean_uint64_to_nat__UInt64_toBitVec⟩, ⟨_, _, _, _, .inlined .uint53__bigint_bitvec64__lean_uint64_to_nat__UInt64_toBitVec⟩, ⟨_, _, _, _, .inlined .uint53__int53_bitvec64__lean_uint64_to_nat__UInt64_toBitVec⟩]

/-- The operations of `lean_uint64_to_nat__UInt64_toNat`. -/
def «cands_lean_uint64_to_nat__UInt64_toNat» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_nat__lean_uint64_to_nat__UInt64_toNat⟩, ⟨_, _, _, _, .imported .bigint_nat__uint53__lean_uint64_to_nat__UInt64_toNat⟩, ⟨_, _, _, _, .inlined .uint53__bigint_nat__lean_uint64_to_nat__UInt64_toNat⟩, ⟨_, _, _, _, .inlined .uint53__lean_uint64_to_nat__UInt64_toNat⟩]

/-- The operations of `lean_uint64_to_uint16`. -/
def «cands_lean_uint64_to_uint16» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_uint64_to_uint16⟩, ⟨_, _, _, _, .imported .uint53__lean_uint64_to_uint16⟩]

/-- The operations of `lean_uint64_to_uint32`. -/
def «cands_lean_uint64_to_uint32» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_uint64_to_uint32⟩, ⟨_, _, _, _, .imported .uint53__lean_uint64_to_uint32⟩]

/-- The operations of `lean_uint64_to_uint8`. -/
def «cands_lean_uint64_to_uint8» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_uint64_to_uint8⟩, ⟨_, _, _, _, .imported .uint53__lean_uint64_to_uint8⟩]

/-- The operations of `lean_uint64_xor`. -/
def «cands_lean_uint64_xor» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_uint64_xor⟩, ⟨_, _, _, _, .imported .uint53__lean_uint64_xor⟩]

/-- The operations of `lean_uint8_add`. -/
def «cands_lean_uint8_add» : List Cand :=
  [⟨_, _, _, _, .imported .uint8__lean_uint8_add⟩]

/-- The operations of `lean_uint8_complement`. -/
def «cands_lean_uint8_complement» : List Cand :=
  [⟨_, _, _, _, .imported .uint8__lean_uint8_complement⟩]

/-- The operations of `lean_uint8_dec_eq`. -/
def «cands_lean_uint8_dec_eq» : List Cand :=
  [⟨_, _, _, _, .inlined .uint8__lean_uint8_dec_eq⟩]

/-- The operations of `lean_uint8_dec_le`. -/
def «cands_lean_uint8_dec_le» : List Cand :=
  [⟨_, _, _, _, .inlined .uint8__lean_uint8_dec_le⟩]

/-- The operations of `lean_uint8_dec_lt`. -/
def «cands_lean_uint8_dec_lt» : List Cand :=
  [⟨_, _, _, _, .inlined .uint8__lean_uint8_dec_lt⟩]

/-- The operations of `lean_uint8_div`. -/
def «cands_lean_uint8_div» : List Cand :=
  [⟨_, _, _, _, .imported .uint8__lean_uint8_div⟩]

/-- The operations of `lean_uint8_land`. -/
def «cands_lean_uint8_land» : List Cand :=
  [⟨_, _, _, _, .imported .uint8__lean_uint8_land⟩]

/-- The operations of `lean_uint8_log2`. -/
def «cands_lean_uint8_log2» : List Cand :=
  [⟨_, _, _, _, .imported .uint8__lean_uint8_log2⟩]

/-- The operations of `lean_uint8_lor`. -/
def «cands_lean_uint8_lor» : List Cand :=
  [⟨_, _, _, _, .imported .uint8__lean_uint8_lor⟩]

/-- The operations of `lean_uint8_mod`. -/
def «cands_lean_uint8_mod» : List Cand :=
  [⟨_, _, _, _, .imported .uint8__lean_uint8_mod⟩]

/-- The operations of `lean_uint8_mul`. -/
def «cands_lean_uint8_mul» : List Cand :=
  [⟨_, _, _, _, .imported .uint8__lean_uint8_mul⟩]

/-- The operations of `lean_uint8_neg`. -/
def «cands_lean_uint8_neg» : List Cand :=
  [⟨_, _, _, _, .imported .uint8__lean_uint8_neg⟩]

/-- The operations of `lean_uint8_of_nat__UInt8_ofNat`. -/
def «cands_lean_uint8_of_nat__UInt8_ofNat» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_uint8_of_nat__UInt8_ofNat⟩, ⟨_, _, _, _, .imported .uint53__lean_uint8_of_nat__UInt8_ofNat⟩]

/-- The operations of `lean_uint8_of_nat__UInt8_ofNatLT`. -/
def «cands_lean_uint8_of_nat__UInt8_ofNatLT» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_uint8_of_nat__UInt8_ofNat⟩, ⟨_, _, _, _, .imported .uint53__lean_uint8_of_nat__UInt8_ofNat⟩]

/-- The operations of `lean_uint8_of_nat_mk`. -/
def «cands_lean_uint8_of_nat_mk» : List Cand :=
  [⟨_, _, _, _, .inlined .bitvec8__lean_uint8_of_nat_mk⟩]

/-- The operations of `lean_uint8_shift_left`. -/
def «cands_lean_uint8_shift_left» : List Cand :=
  [⟨_, _, _, _, .imported .uint8__lean_uint8_shift_left⟩]

/-- The operations of `lean_uint8_shift_right`. -/
def «cands_lean_uint8_shift_right» : List Cand :=
  [⟨_, _, _, _, .imported .uint8__lean_uint8_shift_right⟩]

/-- The operations of `lean_uint8_sub`. -/
def «cands_lean_uint8_sub» : List Cand :=
  [⟨_, _, _, _, .imported .uint8__lean_uint8_sub⟩]

/-- The operations of `lean_uint8_to_float`. -/
def «cands_lean_uint8_to_float» : List Cand :=
  [⟨_, _, _, _, .inlined .uint8__lean_uint8_to_float⟩]

/-- The operations of `lean_uint8_to_float32`. -/
def «cands_lean_uint8_to_float32» : List Cand :=
  [⟨_, _, _, _, .inlined .uint8__lean_uint8_to_float32⟩]

/-- The operations of `lean_uint8_to_nat__UInt8_toBitVec`. -/
def «cands_lean_uint8_to_nat__UInt8_toBitVec» : List Cand :=
  [⟨_, _, _, _, .inlined .uint8__lean_uint8_to_nat__UInt8_toBitVec⟩]

/-- The operations of `lean_uint8_to_nat__UInt8_toNat`. -/
def «cands_lean_uint8_to_nat__UInt8_toNat» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_nat__lean_uint8_to_nat__UInt8_toNat⟩, ⟨_, _, _, _, .inlined .uint53__lean_uint8_to_nat__UInt8_toNat⟩]

/-- The operations of `lean_uint8_to_uint16`. -/
def «cands_lean_uint8_to_uint16» : List Cand :=
  [⟨_, _, _, _, .inlined .uint8__lean_uint8_to_uint16⟩]

/-- The operations of `lean_uint8_to_uint32`. -/
def «cands_lean_uint8_to_uint32» : List Cand :=
  [⟨_, _, _, _, .inlined .uint8__lean_uint8_to_uint32⟩]

/-- The operations of `lean_uint8_to_uint64`. -/
def «cands_lean_uint8_to_uint64» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_nat__lean_uint8_to_uint64⟩, ⟨_, _, _, _, .inlined .uint53__lean_uint8_to_uint64⟩]

/-- The operations of `lean_uint8_xor`. -/
def «cands_lean_uint8_xor» : List Cand :=
  [⟨_, _, _, _, .imported .uint8__lean_uint8_xor⟩]

/-- The operations of `lean_version_get_is_release`. -/
def «cands_lean_version_get_is_release» : List Cand :=
  [⟨_, _, _, _, .imported .bool__lean_version_get_is_release⟩]

/-- The operations of `lean_version_get_major`. -/
def «cands_lean_version_get_major» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_version_get_major⟩, ⟨_, _, _, _, .imported .uint53__lean_version_get_major⟩]

/-- The operations of `lean_version_get_minor`. -/
def «cands_lean_version_get_minor» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_version_get_minor⟩, ⟨_, _, _, _, .imported .uint53__lean_version_get_minor⟩]

/-- The operations of `lean_version_get_patch`. -/
def «cands_lean_version_get_patch» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_version_get_patch⟩, ⟨_, _, _, _, .imported .uint53__lean_version_get_patch⟩]

/-- The operations of `lean_version_get_special_desc`. -/
def «cands_lean_version_get_special_desc» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_version_get_special_desc⟩]

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

/-- The operation of the extern `name` at the signature `σs → τ`, if there is one. -/
def lookup (name : String) (σs : List JsTy) (τ : JsTy) : Option (JsSomeOp σs τ) :=
  firstOf σs τ (match name with
    | "acos" => «cands_acos»
    | "acosf" => «cands_acosf»
    | "acosh" => «cands_acosh»
    | "acoshf" => «cands_acoshf»
    | "asin" => «cands_asin»
    | "asinf" => «cands_asinf»
    | "asinh" => «cands_asinh»
    | "asinhf" => «cands_asinhf»
    | "atan" => «cands_atan»
    | "atan2" => «cands_atan2»
    | "atan2f" => «cands_atan2f»
    | "atanf" => «cands_atanf»
    | "atanh" => «cands_atanh»
    | "atanhf" => «cands_atanhf»
    | "cbrt" => «cands_cbrt»
    | "cbrtf" => «cands_cbrtf»
    | "ceil" => «cands_ceil»
    | "ceilf" => «cands_ceilf»
    | "cos" => «cands_cos»
    | "cosf" => «cands_cosf»
    | "cosh" => «cands_cosh»
    | "coshf" => «cands_coshf»
    | "exp" => «cands_exp»
    | "exp2" => «cands_exp2»
    | "exp2f" => «cands_exp2f»
    | "expf" => «cands_expf»
    | "fabs" => «cands_fabs»
    | "fabsf" => «cands_fabsf»
    | "floor" => «cands_floor»
    | "floorf" => «cands_floorf»
    | "lean_array_fset" => «cands_lean_array_fset» σs τ
    | "lean_array_fswap" => «cands_lean_array_fswap» σs τ
    | "lean_array_get" => «cands_lean_array_get» σs τ
    | "lean_array_get_borrowed" => «cands_lean_array_get_borrowed» σs τ
    | "lean_array_get_size" => «cands_lean_array_get_size» σs τ
    | "lean_array_mk" => «cands_lean_array_mk» σs τ
    | "lean_array_pop" => «cands_lean_array_pop» σs τ
    | "lean_array_push" => «cands_lean_array_push» σs τ
    | "lean_array_set" => «cands_lean_array_set» σs τ
    | "lean_array_swap" => «cands_lean_array_swap» σs τ
    | "lean_array_to_list" => «cands_lean_array_to_list» σs τ
    | "lean_bool_to_int16" => «cands_lean_bool_to_int16»
    | "lean_bool_to_int32" => «cands_lean_bool_to_int32»
    | "lean_bool_to_int64" => «cands_lean_bool_to_int64»
    | "lean_bool_to_int8" => «cands_lean_bool_to_int8»
    | "lean_bool_to_uint16" => «cands_lean_bool_to_uint16»
    | "lean_bool_to_uint32" => «cands_lean_bool_to_uint32»
    | "lean_bool_to_uint64" => «cands_lean_bool_to_uint64»
    | "lean_bool_to_uint8" => «cands_lean_bool_to_uint8»
    | "lean_dbg_trace_if_shared" => «cands_lean_dbg_trace_if_shared» σs τ
    | "lean_float32_add" => «cands_lean_float32_add»
    | "lean_float32_beq" => «cands_lean_float32_beq»
    | "lean_float32_decLe__Float32_decLe" => «cands_lean_float32_decLe__Float32_decLe»
    | "lean_float32_decLe__Float32_le" => «cands_lean_float32_decLe__Float32_le»
    | "lean_float32_decLt__Float32_decLt" => «cands_lean_float32_decLt__Float32_decLt»
    | "lean_float32_decLt__Float32_lt" => «cands_lean_float32_decLt__Float32_lt»
    | "lean_float32_div" => «cands_lean_float32_div»
    | "lean_float32_frexp" => «cands_lean_float32_frexp»
    | "lean_float32_isfinite" => «cands_lean_float32_isfinite»
    | "lean_float32_isinf" => «cands_lean_float32_isinf»
    | "lean_float32_isnan" => «cands_lean_float32_isnan»
    | "lean_float32_mul" => «cands_lean_float32_mul»
    | "lean_float32_negate" => «cands_lean_float32_negate»
    | "lean_float32_of_bits__Float32_ofBits" => «cands_lean_float32_of_bits__Float32_ofBits»
    | "lean_float32_of_bits__Float32_ofModel" => «cands_lean_float32_of_bits__Float32_ofModel»
    | "lean_float32_scaleb" => «cands_lean_float32_scaleb»
    | "lean_float32_sub" => «cands_lean_float32_sub»
    | "lean_float32_to_bits__Float32_toBits" => «cands_lean_float32_to_bits__Float32_toBits»
    | "lean_float32_to_bits__Float32_toModel" => «cands_lean_float32_to_bits__Float32_toModel»
    | "lean_float32_to_float" => «cands_lean_float32_to_float»
    | "lean_float32_to_int16" => «cands_lean_float32_to_int16»
    | "lean_float32_to_int32" => «cands_lean_float32_to_int32»
    | "lean_float32_to_int64" => «cands_lean_float32_to_int64»
    | "lean_float32_to_int8" => «cands_lean_float32_to_int8»
    | "lean_float32_to_string" => «cands_lean_float32_to_string»
    | "lean_float32_to_uint16" => «cands_lean_float32_to_uint16»
    | "lean_float32_to_uint32" => «cands_lean_float32_to_uint32»
    | "lean_float32_to_uint64" => «cands_lean_float32_to_uint64»
    | "lean_float32_to_uint8" => «cands_lean_float32_to_uint8»
    | "lean_float_add" => «cands_lean_float_add»
    | "lean_float_beq" => «cands_lean_float_beq»
    | "lean_float_decLe__Float_decLe" => «cands_lean_float_decLe__Float_decLe»
    | "lean_float_decLe__Float_le" => «cands_lean_float_decLe__Float_le»
    | "lean_float_decLt__Float_decLt" => «cands_lean_float_decLt__Float_decLt»
    | "lean_float_decLt__Float_lt" => «cands_lean_float_decLt__Float_lt»
    | "lean_float_div" => «cands_lean_float_div»
    | "lean_float_frexp" => «cands_lean_float_frexp»
    | "lean_float_isfinite" => «cands_lean_float_isfinite»
    | "lean_float_isinf" => «cands_lean_float_isinf»
    | "lean_float_isnan" => «cands_lean_float_isnan»
    | "lean_float_mul" => «cands_lean_float_mul»
    | "lean_float_negate" => «cands_lean_float_negate»
    | "lean_float_of_bits__Float_ofBits" => «cands_lean_float_of_bits__Float_ofBits»
    | "lean_float_of_bits__Float_ofModel" => «cands_lean_float_of_bits__Float_ofModel»
    | "lean_float_scaleb" => «cands_lean_float_scaleb»
    | "lean_float_sub" => «cands_lean_float_sub»
    | "lean_float_to_bits__Float_toBits" => «cands_lean_float_to_bits__Float_toBits»
    | "lean_float_to_bits__Float_toModel" => «cands_lean_float_to_bits__Float_toModel»
    | "lean_float_to_float32" => «cands_lean_float_to_float32»
    | "lean_float_to_int16" => «cands_lean_float_to_int16»
    | "lean_float_to_int32" => «cands_lean_float_to_int32»
    | "lean_float_to_int64" => «cands_lean_float_to_int64»
    | "lean_float_to_int8" => «cands_lean_float_to_int8»
    | "lean_float_to_string" => «cands_lean_float_to_string»
    | "lean_float_to_uint16" => «cands_lean_float_to_uint16»
    | "lean_float_to_uint32" => «cands_lean_float_to_uint32»
    | "lean_float_to_uint64" => «cands_lean_float_to_uint64»
    | "lean_float_to_uint8" => «cands_lean_float_to_uint8»
    | "lean_get_githash" => «cands_lean_get_githash»
    | "lean_int16_abs" => «cands_lean_int16_abs»
    | "lean_int16_add" => «cands_lean_int16_add»
    | "lean_int16_complement" => «cands_lean_int16_complement»
    | "lean_int16_dec_eq" => «cands_lean_int16_dec_eq»
    | "lean_int16_dec_le" => «cands_lean_int16_dec_le»
    | "lean_int16_dec_lt" => «cands_lean_int16_dec_lt»
    | "lean_int16_div" => «cands_lean_int16_div»
    | "lean_int16_land" => «cands_lean_int16_land»
    | "lean_int16_lor" => «cands_lean_int16_lor»
    | "lean_int16_mod" => «cands_lean_int16_mod»
    | "lean_int16_mul" => «cands_lean_int16_mul»
    | "lean_int16_neg" => «cands_lean_int16_neg»
    | "lean_int16_of_int" => «cands_lean_int16_of_int»
    | "lean_int16_of_nat" => «cands_lean_int16_of_nat»
    | "lean_int16_shift_left" => «cands_lean_int16_shift_left»
    | "lean_int16_shift_right" => «cands_lean_int16_shift_right»
    | "lean_int16_sub" => «cands_lean_int16_sub»
    | "lean_int16_to_float" => «cands_lean_int16_to_float»
    | "lean_int16_to_float32" => «cands_lean_int16_to_float32»
    | "lean_int16_to_int" => «cands_lean_int16_to_int»
    | "lean_int16_to_int32" => «cands_lean_int16_to_int32»
    | "lean_int16_to_int64" => «cands_lean_int16_to_int64»
    | "lean_int16_to_int8" => «cands_lean_int16_to_int8»
    | "lean_int16_xor" => «cands_lean_int16_xor»
    | "lean_int32_abs" => «cands_lean_int32_abs»
    | "lean_int32_add" => «cands_lean_int32_add»
    | "lean_int32_complement" => «cands_lean_int32_complement»
    | "lean_int32_dec_eq" => «cands_lean_int32_dec_eq»
    | "lean_int32_dec_le" => «cands_lean_int32_dec_le»
    | "lean_int32_dec_lt" => «cands_lean_int32_dec_lt»
    | "lean_int32_div" => «cands_lean_int32_div»
    | "lean_int32_land" => «cands_lean_int32_land»
    | "lean_int32_lor" => «cands_lean_int32_lor»
    | "lean_int32_mod" => «cands_lean_int32_mod»
    | "lean_int32_mul" => «cands_lean_int32_mul»
    | "lean_int32_neg" => «cands_lean_int32_neg»
    | "lean_int32_of_int" => «cands_lean_int32_of_int»
    | "lean_int32_of_nat" => «cands_lean_int32_of_nat»
    | "lean_int32_shift_left" => «cands_lean_int32_shift_left»
    | "lean_int32_shift_right" => «cands_lean_int32_shift_right»
    | "lean_int32_sub" => «cands_lean_int32_sub»
    | "lean_int32_to_float" => «cands_lean_int32_to_float»
    | "lean_int32_to_float32" => «cands_lean_int32_to_float32»
    | "lean_int32_to_int" => «cands_lean_int32_to_int»
    | "lean_int32_to_int16" => «cands_lean_int32_to_int16»
    | "lean_int32_to_int64" => «cands_lean_int32_to_int64»
    | "lean_int32_to_int8" => «cands_lean_int32_to_int8»
    | "lean_int32_xor" => «cands_lean_int32_xor»
    | "lean_int64_abs" => «cands_lean_int64_abs»
    | "lean_int64_add" => «cands_lean_int64_add»
    | "lean_int64_complement" => «cands_lean_int64_complement»
    | "lean_int64_dec_eq" => «cands_lean_int64_dec_eq»
    | "lean_int64_dec_le" => «cands_lean_int64_dec_le»
    | "lean_int64_dec_lt" => «cands_lean_int64_dec_lt»
    | "lean_int64_div" => «cands_lean_int64_div»
    | "lean_int64_land" => «cands_lean_int64_land»
    | "lean_int64_lor" => «cands_lean_int64_lor»
    | "lean_int64_mod" => «cands_lean_int64_mod»
    | "lean_int64_mul" => «cands_lean_int64_mul»
    | "lean_int64_neg" => «cands_lean_int64_neg»
    | "lean_int64_of_int" => «cands_lean_int64_of_int»
    | "lean_int64_of_nat" => «cands_lean_int64_of_nat»
    | "lean_int64_shift_left" => «cands_lean_int64_shift_left»
    | "lean_int64_shift_right" => «cands_lean_int64_shift_right»
    | "lean_int64_sub" => «cands_lean_int64_sub»
    | "lean_int64_to_float" => «cands_lean_int64_to_float»
    | "lean_int64_to_float32" => «cands_lean_int64_to_float32»
    | "lean_int64_to_int16" => «cands_lean_int64_to_int16»
    | "lean_int64_to_int32" => «cands_lean_int64_to_int32»
    | "lean_int64_to_int8" => «cands_lean_int64_to_int8»
    | "lean_int64_to_int_sint" => «cands_lean_int64_to_int_sint»
    | "lean_int64_xor" => «cands_lean_int64_xor»
    | "lean_int8_abs" => «cands_lean_int8_abs»
    | "lean_int8_add" => «cands_lean_int8_add»
    | "lean_int8_complement" => «cands_lean_int8_complement»
    | "lean_int8_dec_eq" => «cands_lean_int8_dec_eq»
    | "lean_int8_dec_le" => «cands_lean_int8_dec_le»
    | "lean_int8_dec_lt" => «cands_lean_int8_dec_lt»
    | "lean_int8_div" => «cands_lean_int8_div»
    | "lean_int8_land" => «cands_lean_int8_land»
    | "lean_int8_lor" => «cands_lean_int8_lor»
    | "lean_int8_mod" => «cands_lean_int8_mod»
    | "lean_int8_mul" => «cands_lean_int8_mul»
    | "lean_int8_neg" => «cands_lean_int8_neg»
    | "lean_int8_of_int" => «cands_lean_int8_of_int»
    | "lean_int8_of_nat" => «cands_lean_int8_of_nat»
    | "lean_int8_shift_left" => «cands_lean_int8_shift_left»
    | "lean_int8_shift_right" => «cands_lean_int8_shift_right»
    | "lean_int8_sub" => «cands_lean_int8_sub»
    | "lean_int8_to_float" => «cands_lean_int8_to_float»
    | "lean_int8_to_float32" => «cands_lean_int8_to_float32»
    | "lean_int8_to_int" => «cands_lean_int8_to_int»
    | "lean_int8_to_int16" => «cands_lean_int8_to_int16»
    | "lean_int8_to_int32" => «cands_lean_int8_to_int32»
    | "lean_int8_to_int64" => «cands_lean_int8_to_int64»
    | "lean_int8_xor" => «cands_lean_int8_xor»
    | "lean_int_add" => «cands_lean_int_add»
    | "lean_int_dec_eq" => «cands_lean_int_dec_eq»
    | "lean_int_dec_le" => «cands_lean_int_dec_le»
    | "lean_int_dec_lt" => «cands_lean_int_dec_lt»
    | "lean_int_dec_nonneg" => «cands_lean_int_dec_nonneg»
    | "lean_int_div" => «cands_lean_int_div»
    | "lean_int_div_exact" => «cands_lean_int_div_exact»
    | "lean_int_ediv" => «cands_lean_int_ediv»
    | "lean_int_emod" => «cands_lean_int_emod»
    | "lean_int_mod" => «cands_lean_int_mod»
    | "lean_int_mul" => «cands_lean_int_mul»
    | "lean_int_neg" => «cands_lean_int_neg»
    | "lean_int_neg_succ_of_nat" => «cands_lean_int_neg_succ_of_nat»
    | "lean_int_sub" => «cands_lean_int_sub»
    | "lean_internal_has_llvm_backend" => «cands_lean_internal_has_llvm_backend»
    | "lean_internal_is_stage0" => «cands_lean_internal_is_stage0»
    | "lean_mk_array" => «cands_lean_mk_array» σs τ
    | "lean_mk_empty_array_with_capacity__Array_emptyWithCapacity" => «cands_lean_mk_empty_array_with_capacity__Array_emptyWithCapacity» σs τ
    | "lean_mk_empty_array_with_capacity__Array_mkEmpty" => «cands_lean_mk_empty_array_with_capacity__Array_mkEmpty» σs τ
    | "lean_mk_thunk" => «cands_lean_mk_thunk» σs τ
    | "lean_nat_abs" => «cands_lean_nat_abs»
    | "lean_nat_add" => «cands_lean_nat_add»
    | "lean_nat_dec_eq__Nat_beq" => «cands_lean_nat_dec_eq__Nat_beq»
    | "lean_nat_dec_eq__Nat_decEq" => «cands_lean_nat_dec_eq__Nat_decEq»
    | "lean_nat_dec_le__Nat_ble" => «cands_lean_nat_dec_le__Nat_ble»
    | "lean_nat_dec_le__Nat_decLe" => «cands_lean_nat_dec_le__Nat_decLe»
    | "lean_nat_dec_lt" => «cands_lean_nat_dec_lt»
    | "lean_nat_div" => «cands_lean_nat_div»
    | "lean_nat_div_exact" => «cands_lean_nat_div_exact»
    | "lean_nat_land" => «cands_lean_nat_land»
    | "lean_nat_log2" => «cands_lean_nat_log2»
    | "lean_nat_lor" => «cands_lean_nat_lor»
    | "lean_nat_lxor" => «cands_lean_nat_lxor»
    | "lean_nat_mod__Nat_mod" => «cands_lean_nat_mod__Nat_mod»
    | "lean_nat_mod__Nat_modCore" => «cands_lean_nat_mod__Nat_modCore»
    | "lean_nat_mul" => «cands_lean_nat_mul»
    | "lean_nat_pow" => «cands_lean_nat_pow»
    | "lean_nat_pred" => «cands_lean_nat_pred»
    | "lean_nat_shiftl" => «cands_lean_nat_shiftl»
    | "lean_nat_shiftr" => «cands_lean_nat_shiftr»
    | "lean_nat_sub" => «cands_lean_nat_sub»
    | "lean_nat_to_int" => «cands_lean_nat_to_int»
    | "lean_slice_dec_lt" => «cands_lean_slice_dec_lt»
    | "lean_slice_hash" => «cands_lean_slice_hash»
    | "lean_strict_and" => «cands_lean_strict_and»
    | "lean_strict_or" => «cands_lean_strict_or»
    | "lean_string_any" => «cands_lean_string_any»
    | "lean_string_append__String_Internal_append" => «cands_lean_string_append__String_Internal_append»
    | "lean_string_append__String_append" => «cands_lean_string_append__String_append»
    | "lean_string_capitalize" => «cands_lean_string_capitalize»
    | "lean_string_compare" => «cands_lean_string_compare»
    | "lean_string_contains" => «cands_lean_string_contains»
    | "lean_string_data__String_data" => «cands_lean_string_data__String_data»
    | "lean_string_data__String_toList" => «cands_lean_string_data__String_toList»
    | "lean_string_dec_eq" => «cands_lean_string_dec_eq»
    | "lean_string_dec_lt" => «cands_lean_string_dec_lt»
    | "lean_string_drop" => «cands_lean_string_drop»
    | "lean_string_dropright" => «cands_lean_string_dropright»
    | "lean_string_foldl" => «cands_lean_string_foldl»
    | "lean_string_front" => «cands_lean_string_front»
    | "lean_string_get_byte_fast__String_Internal_getUTF8Byte" => «cands_lean_string_get_byte_fast__String_Internal_getUTF8Byte»
    | "lean_string_get_byte_fast__String_getUTF8Byte" => «cands_lean_string_get_byte_fast__String_getUTF8Byte»
    | "lean_string_get_byte_fast__String_getUtf8Byte" => «cands_lean_string_get_byte_fast__String_getUtf8Byte»
    | "lean_string_hash" => «cands_lean_string_hash»
    | "lean_string_intercalate" => «cands_lean_string_intercalate»
    | "lean_string_is_valid_pos" => «cands_lean_string_is_valid_pos»
    | "lean_string_isempty" => «cands_lean_string_isempty»
    | "lean_string_isprefixof" => «cands_lean_string_isprefixof»
    | "lean_string_length__String_Internal_length" => «cands_lean_string_length__String_Internal_length»
    | "lean_string_length__String_length" => «cands_lean_string_length__String_length»
    | "lean_string_memcmp" => «cands_lean_string_memcmp»
    | "lean_string_mk__String_mk" => «cands_lean_string_mk__String_mk»
    | "lean_string_mk__String_ofList" => «cands_lean_string_mk__String_ofList»
    | "lean_string_nextwhile" => «cands_lean_string_nextwhile»
    | "lean_string_offsetofpos" => «cands_lean_string_offsetofpos»
    | "lean_string_pos_min" => «cands_lean_string_pos_min»
    | "lean_string_pos_sub" => «cands_lean_string_pos_sub»
    | "lean_string_posof" => «cands_lean_string_posof»
    | "lean_string_push" => «cands_lean_string_push»
    | "lean_string_pushn" => «cands_lean_string_pushn»
    | "lean_string_trim" => «cands_lean_string_trim»
    | "lean_string_utf8_at_end__String_Internal_atEnd" => «cands_lean_string_utf8_at_end__String_Internal_atEnd»
    | "lean_string_utf8_at_end__String_Pos_Raw_atEnd" => «cands_lean_string_utf8_at_end__String_Pos_Raw_atEnd»
    | "lean_string_utf8_at_end__String_atEnd" => «cands_lean_string_utf8_at_end__String_atEnd»
    | "lean_string_utf8_byte_size" => «cands_lean_string_utf8_byte_size»
    | "lean_string_utf8_extract__String_Internal_extract" => «cands_lean_string_utf8_extract__String_Internal_extract»
    | "lean_string_utf8_extract__String_Pos_Raw_extract" => «cands_lean_string_utf8_extract__String_Pos_Raw_extract»
    | "lean_string_utf8_extract_fast" => «cands_lean_string_utf8_extract_fast»
    | "lean_string_utf8_get__String_Internal_get" => «cands_lean_string_utf8_get__String_Internal_get»
    | "lean_string_utf8_get__String_Pos_Raw_get" => «cands_lean_string_utf8_get__String_Pos_Raw_get»
    | "lean_string_utf8_get__String_get" => «cands_lean_string_utf8_get__String_get»
    | "lean_string_utf8_get_bang__String_Pos_Raw_get!" => «cands_lean_string_utf8_get_bang__String_Pos_Raw_get!»
    | "lean_string_utf8_get_bang__String_get!" => «cands_lean_string_utf8_get_bang__String_get!»
    | "lean_string_utf8_get_fast__String_Pos_Raw_get'" => «cands_lean_string_utf8_get_fast__String_Pos_Raw_get'»
    | "lean_string_utf8_get_fast__String_get'" => «cands_lean_string_utf8_get_fast__String_get'»
    | "lean_string_utf8_get_opt__String_Pos_Raw_get?" => «cands_lean_string_utf8_get_opt__String_Pos_Raw_get?»
    | "lean_string_utf8_get_opt__String_get?" => «cands_lean_string_utf8_get_opt__String_get?»
    | "lean_string_utf8_next__String_Internal_next" => «cands_lean_string_utf8_next__String_Internal_next»
    | "lean_string_utf8_next__String_Pos_Raw_next" => «cands_lean_string_utf8_next__String_Pos_Raw_next»
    | "lean_string_utf8_next__String_next" => «cands_lean_string_utf8_next__String_next»
    | "lean_string_utf8_next_fast__String_Pos_next" => «cands_lean_string_utf8_next_fast__String_Pos_next»
    | "lean_string_utf8_next_fast__String_next'" => «cands_lean_string_utf8_next_fast__String_next'»
    | "lean_string_utf8_prev__String_Pos_Raw_prev" => «cands_lean_string_utf8_prev__String_Pos_Raw_prev»
    | "lean_string_utf8_prev__String_prev" => «cands_lean_string_utf8_prev__String_prev»
    | "lean_string_utf8_set__String_Pos_Raw_set" => «cands_lean_string_utf8_set__String_Pos_Raw_set»
    | "lean_string_utf8_set__String_Pos_set" => «cands_lean_string_utf8_set__String_Pos_set»
    | "lean_string_utf8_set__String_set" => «cands_lean_string_utf8_set__String_set»
    | "lean_substring_all" => «cands_lean_substring_all»
    | "lean_substring_beq" => «cands_lean_substring_beq»
    | "lean_substring_drop" => «cands_lean_substring_drop»
    | "lean_substring_extract" => «cands_lean_substring_extract»
    | "lean_substring_front" => «cands_lean_substring_front»
    | "lean_substring_get" => «cands_lean_substring_get»
    | "lean_substring_isempty" => «cands_lean_substring_isempty»
    | "lean_substring_prev" => «cands_lean_substring_prev»
    | "lean_substring_takewhile" => «cands_lean_substring_takewhile»
    | "lean_substring_tostring" => «cands_lean_substring_tostring»
    | "lean_system_platform_emscripten" => «cands_lean_system_platform_emscripten»
    | "lean_system_platform_target" => «cands_lean_system_platform_target»
    | "lean_thunk_get_own" => «cands_lean_thunk_get_own» σs τ
    | "lean_thunk_pure" => «cands_lean_thunk_pure» σs τ
    | "lean_uint16_add" => «cands_lean_uint16_add»
    | "lean_uint16_complement" => «cands_lean_uint16_complement»
    | "lean_uint16_dec_eq" => «cands_lean_uint16_dec_eq»
    | "lean_uint16_dec_le" => «cands_lean_uint16_dec_le»
    | "lean_uint16_dec_lt" => «cands_lean_uint16_dec_lt»
    | "lean_uint16_div" => «cands_lean_uint16_div»
    | "lean_uint16_land" => «cands_lean_uint16_land»
    | "lean_uint16_log2" => «cands_lean_uint16_log2»
    | "lean_uint16_lor" => «cands_lean_uint16_lor»
    | "lean_uint16_mod" => «cands_lean_uint16_mod»
    | "lean_uint16_mul" => «cands_lean_uint16_mul»
    | "lean_uint16_neg" => «cands_lean_uint16_neg»
    | "lean_uint16_of_nat__UInt16_ofNat" => «cands_lean_uint16_of_nat__UInt16_ofNat»
    | "lean_uint16_of_nat__UInt16_ofNatLT" => «cands_lean_uint16_of_nat__UInt16_ofNatLT»
    | "lean_uint16_of_nat_mk" => «cands_lean_uint16_of_nat_mk»
    | "lean_uint16_shift_left" => «cands_lean_uint16_shift_left»
    | "lean_uint16_shift_right" => «cands_lean_uint16_shift_right»
    | "lean_uint16_sub" => «cands_lean_uint16_sub»
    | "lean_uint16_to_float" => «cands_lean_uint16_to_float»
    | "lean_uint16_to_float32" => «cands_lean_uint16_to_float32»
    | "lean_uint16_to_nat__UInt16_toBitVec" => «cands_lean_uint16_to_nat__UInt16_toBitVec»
    | "lean_uint16_to_nat__UInt16_toNat" => «cands_lean_uint16_to_nat__UInt16_toNat»
    | "lean_uint16_to_uint32" => «cands_lean_uint16_to_uint32»
    | "lean_uint16_to_uint64" => «cands_lean_uint16_to_uint64»
    | "lean_uint16_to_uint8" => «cands_lean_uint16_to_uint8»
    | "lean_uint16_xor" => «cands_lean_uint16_xor»
    | "lean_uint32_add" => «cands_lean_uint32_add»
    | "lean_uint32_complement" => «cands_lean_uint32_complement»
    | "lean_uint32_dec_eq" => «cands_lean_uint32_dec_eq»
    | "lean_uint32_dec_le" => «cands_lean_uint32_dec_le»
    | "lean_uint32_dec_lt" => «cands_lean_uint32_dec_lt»
    | "lean_uint32_div" => «cands_lean_uint32_div»
    | "lean_uint32_land" => «cands_lean_uint32_land»
    | "lean_uint32_log2" => «cands_lean_uint32_log2»
    | "lean_uint32_lor" => «cands_lean_uint32_lor»
    | "lean_uint32_mod" => «cands_lean_uint32_mod»
    | "lean_uint32_mul" => «cands_lean_uint32_mul»
    | "lean_uint32_neg" => «cands_lean_uint32_neg»
    | "lean_uint32_of_nat__Char_ofNatAux" => «cands_lean_uint32_of_nat__Char_ofNatAux»
    | "lean_uint32_of_nat__UInt32_ofNat" => «cands_lean_uint32_of_nat__UInt32_ofNat»
    | "lean_uint32_of_nat__UInt32_ofNatLT" => «cands_lean_uint32_of_nat__UInt32_ofNatLT»
    | "lean_uint32_of_nat_mk" => «cands_lean_uint32_of_nat_mk»
    | "lean_uint32_shift_left" => «cands_lean_uint32_shift_left»
    | "lean_uint32_shift_right" => «cands_lean_uint32_shift_right»
    | "lean_uint32_sub" => «cands_lean_uint32_sub»
    | "lean_uint32_to_float" => «cands_lean_uint32_to_float»
    | "lean_uint32_to_float32" => «cands_lean_uint32_to_float32»
    | "lean_uint32_to_nat__UInt32_toBitVec" => «cands_lean_uint32_to_nat__UInt32_toBitVec»
    | "lean_uint32_to_nat__UInt32_toNat" => «cands_lean_uint32_to_nat__UInt32_toNat»
    | "lean_uint32_to_uint16" => «cands_lean_uint32_to_uint16»
    | "lean_uint32_to_uint64" => «cands_lean_uint32_to_uint64»
    | "lean_uint32_to_uint8" => «cands_lean_uint32_to_uint8»
    | "lean_uint32_xor" => «cands_lean_uint32_xor»
    | "lean_uint64_add" => «cands_lean_uint64_add»
    | "lean_uint64_complement" => «cands_lean_uint64_complement»
    | "lean_uint64_dec_eq" => «cands_lean_uint64_dec_eq»
    | "lean_uint64_dec_le" => «cands_lean_uint64_dec_le»
    | "lean_uint64_dec_lt" => «cands_lean_uint64_dec_lt»
    | "lean_uint64_div" => «cands_lean_uint64_div»
    | "lean_uint64_land" => «cands_lean_uint64_land»
    | "lean_uint64_log2" => «cands_lean_uint64_log2»
    | "lean_uint64_lor" => «cands_lean_uint64_lor»
    | "lean_uint64_mix_hash" => «cands_lean_uint64_mix_hash»
    | "lean_uint64_mod" => «cands_lean_uint64_mod»
    | "lean_uint64_mul" => «cands_lean_uint64_mul»
    | "lean_uint64_neg" => «cands_lean_uint64_neg»
    | "lean_uint64_of_nat__UInt64_ofNat" => «cands_lean_uint64_of_nat__UInt64_ofNat»
    | "lean_uint64_of_nat__UInt64_ofNatLT" => «cands_lean_uint64_of_nat__UInt64_ofNatLT»
    | "lean_uint64_of_nat_mk" => «cands_lean_uint64_of_nat_mk»
    | "lean_uint64_shift_left" => «cands_lean_uint64_shift_left»
    | "lean_uint64_shift_right" => «cands_lean_uint64_shift_right»
    | "lean_uint64_sub" => «cands_lean_uint64_sub»
    | "lean_uint64_to_float" => «cands_lean_uint64_to_float»
    | "lean_uint64_to_float32" => «cands_lean_uint64_to_float32»
    | "lean_uint64_to_nat__UInt64_toBitVec" => «cands_lean_uint64_to_nat__UInt64_toBitVec»
    | "lean_uint64_to_nat__UInt64_toNat" => «cands_lean_uint64_to_nat__UInt64_toNat»
    | "lean_uint64_to_uint16" => «cands_lean_uint64_to_uint16»
    | "lean_uint64_to_uint32" => «cands_lean_uint64_to_uint32»
    | "lean_uint64_to_uint8" => «cands_lean_uint64_to_uint8»
    | "lean_uint64_xor" => «cands_lean_uint64_xor»
    | "lean_uint8_add" => «cands_lean_uint8_add»
    | "lean_uint8_complement" => «cands_lean_uint8_complement»
    | "lean_uint8_dec_eq" => «cands_lean_uint8_dec_eq»
    | "lean_uint8_dec_le" => «cands_lean_uint8_dec_le»
    | "lean_uint8_dec_lt" => «cands_lean_uint8_dec_lt»
    | "lean_uint8_div" => «cands_lean_uint8_div»
    | "lean_uint8_land" => «cands_lean_uint8_land»
    | "lean_uint8_log2" => «cands_lean_uint8_log2»
    | "lean_uint8_lor" => «cands_lean_uint8_lor»
    | "lean_uint8_mod" => «cands_lean_uint8_mod»
    | "lean_uint8_mul" => «cands_lean_uint8_mul»
    | "lean_uint8_neg" => «cands_lean_uint8_neg»
    | "lean_uint8_of_nat__UInt8_ofNat" => «cands_lean_uint8_of_nat__UInt8_ofNat»
    | "lean_uint8_of_nat__UInt8_ofNatLT" => «cands_lean_uint8_of_nat__UInt8_ofNatLT»
    | "lean_uint8_of_nat_mk" => «cands_lean_uint8_of_nat_mk»
    | "lean_uint8_shift_left" => «cands_lean_uint8_shift_left»
    | "lean_uint8_shift_right" => «cands_lean_uint8_shift_right»
    | "lean_uint8_sub" => «cands_lean_uint8_sub»
    | "lean_uint8_to_float" => «cands_lean_uint8_to_float»
    | "lean_uint8_to_float32" => «cands_lean_uint8_to_float32»
    | "lean_uint8_to_nat__UInt8_toBitVec" => «cands_lean_uint8_to_nat__UInt8_toBitVec»
    | "lean_uint8_to_nat__UInt8_toNat" => «cands_lean_uint8_to_nat__UInt8_toNat»
    | "lean_uint8_to_uint16" => «cands_lean_uint8_to_uint16»
    | "lean_uint8_to_uint32" => «cands_lean_uint8_to_uint32»
    | "lean_uint8_to_uint64" => «cands_lean_uint8_to_uint64»
    | "lean_uint8_xor" => «cands_lean_uint8_xor»
    | "lean_version_get_is_release" => «cands_lean_version_get_is_release»
    | "lean_version_get_major" => «cands_lean_version_get_major»
    | "lean_version_get_minor" => «cands_lean_version_get_minor»
    | "lean_version_get_patch" => «cands_lean_version_get_patch»
    | "lean_version_get_special_desc" => «cands_lean_version_get_special_desc»
    | "log" => «cands_log»
    | "log10" => «cands_log10»
    | "log10f" => «cands_log10f»
    | "log2" => «cands_log2»
    | "log2f" => «cands_log2f»
    | "logf" => «cands_logf»
    | "pow" => «cands_pow»
    | "powf" => «cands_powf»
    | "round" => «cands_round»
    | "roundf" => «cands_roundf»
    | "sin" => «cands_sin»
    | "sinf" => «cands_sinf»
    | "sinh" => «cands_sinh»
    | "sinhf" => «cands_sinhf»
    | "sqrt" => «cands_sqrt»
    | "sqrtf" => «cands_sqrtf»
    | "tan" => «cands_tan»
    | "tanf" => «cands_tanf»
    | "tanh" => «cands_tanh»
    | "tanhf" => «cands_tanhf»
    | _ => [])

end JsOp

end MoreJs

end
