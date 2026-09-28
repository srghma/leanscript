module

public import JsTerm.Ops.Op

@[expose] public section

set_option autoImplicit false

/-!
# The operations of the externs of the other externs

**Generated** by `scripts/gen_js_ops.py`; do not edit.

The candidates (`JsOp.Cand`) of every extern of the other externs (arrays, thunks, `Bool` conversions, version and platform): its
operations at their signatures, for the lookup (`JsOp.lookup`, `JsTerm.Ops.Lookup`).
-/

namespace MoreJs

namespace JsOp

/-- The operations of `lean_array_fset`. -/
def «cands_lean_array_fset» (σs : List JsTy) (τ : JsTy) : List Cand :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.bigint_nat__lean_array_fset_immutable l)⟩] | none => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.uint53__lean_array_fset_immutable l)⟩] | none => [])

/-- The operations of `lean_array_fswap`. -/
def «cands_lean_array_fswap» (σs : List JsTy) (τ : JsTy) : List Cand :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.bigint_nat__lean_array_fswap_immutable l)⟩] | none => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.uint53__lean_array_fswap_immutable l)⟩] | none => [])

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
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .generic α⟩ => [⟨_, _, _, _, .imported (.array__lean_array_pop_immutable α)⟩] | _ => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .typed t⟩ => [⟨_, _, _, _, .imported (.typedArray__lean_array_pop_immutable t)⟩] | _ => [])

/-- The operations of `lean_array_push`. -/
def «cands_lean_array_push» (σs : List JsTy) (τ : JsTy) : List Cand :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .generic α⟩ => [⟨_, _, _, _, .imported (.array__lean_array_push_immutable α)⟩] | _ => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .typed t⟩ => [⟨_, _, _, _, .imported (.typedArray__lean_array_push_immutable t)⟩] | _ => [])

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

/-- The operations of `lean_get_githash`. -/
def «cands_lean_get_githash» : List Cand :=
  [⟨_, _, _, _, .imported .string__lean_get_githash⟩]

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

/-- The operations of `lean_strict_and`. -/
def «cands_lean_strict_and» : List Cand :=
  [⟨_, _, _, _, .inlined .bool__lean_strict_and⟩]

/-- The operations of `lean_strict_or`. -/
def «cands_lean_strict_or» : List Cand :=
  [⟨_, _, _, _, .inlined .bool__lean_strict_or⟩]

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

/-- The candidates of the extern `name`, when it is one of the other externs. -/
def candsMisc? (name : String) (σs : List JsTy) (τ : JsTy) : Option (List Cand) :=
  match name with
  | "lean_array_fset" => some («cands_lean_array_fset» σs τ)
  | "lean_array_fswap" => some («cands_lean_array_fswap» σs τ)
  | "lean_array_get" => some («cands_lean_array_get» σs τ)
  | "lean_array_get_borrowed" => some («cands_lean_array_get_borrowed» σs τ)
  | "lean_array_get_size" => some («cands_lean_array_get_size» σs τ)
  | "lean_array_mk" => some («cands_lean_array_mk» σs τ)
  | "lean_array_pop" => some («cands_lean_array_pop» σs τ)
  | "lean_array_push" => some («cands_lean_array_push» σs τ)
  | "lean_array_set" => some («cands_lean_array_set» σs τ)
  | "lean_array_swap" => some («cands_lean_array_swap» σs τ)
  | "lean_array_to_list" => some («cands_lean_array_to_list» σs τ)
  | "lean_bool_to_int16" => some «cands_lean_bool_to_int16»
  | "lean_bool_to_int32" => some «cands_lean_bool_to_int32»
  | "lean_bool_to_int64" => some «cands_lean_bool_to_int64»
  | "lean_bool_to_int8" => some «cands_lean_bool_to_int8»
  | "lean_bool_to_uint16" => some «cands_lean_bool_to_uint16»
  | "lean_bool_to_uint32" => some «cands_lean_bool_to_uint32»
  | "lean_bool_to_uint64" => some «cands_lean_bool_to_uint64»
  | "lean_bool_to_uint8" => some «cands_lean_bool_to_uint8»
  | "lean_dbg_trace_if_shared" => some («cands_lean_dbg_trace_if_shared» σs τ)
  | "lean_get_githash" => some «cands_lean_get_githash»
  | "lean_internal_has_llvm_backend" => some «cands_lean_internal_has_llvm_backend»
  | "lean_internal_is_stage0" => some «cands_lean_internal_is_stage0»
  | "lean_mk_array" => some («cands_lean_mk_array» σs τ)
  | "lean_mk_empty_array_with_capacity__Array_emptyWithCapacity" => some («cands_lean_mk_empty_array_with_capacity__Array_emptyWithCapacity» σs τ)
  | "lean_mk_empty_array_with_capacity__Array_mkEmpty" => some («cands_lean_mk_empty_array_with_capacity__Array_mkEmpty» σs τ)
  | "lean_mk_thunk" => some («cands_lean_mk_thunk» σs τ)
  | "lean_strict_and" => some «cands_lean_strict_and»
  | "lean_strict_or" => some «cands_lean_strict_or»
  | "lean_system_platform_emscripten" => some «cands_lean_system_platform_emscripten»
  | "lean_system_platform_target" => some «cands_lean_system_platform_target»
  | "lean_thunk_get_own" => some («cands_lean_thunk_get_own» σs τ)
  | "lean_thunk_pure" => some («cands_lean_thunk_pure» σs τ)
  | "lean_version_get_is_release" => some «cands_lean_version_get_is_release»
  | "lean_version_get_major" => some «cands_lean_version_get_major»
  | "lean_version_get_minor" => some «cands_lean_version_get_minor»
  | "lean_version_get_patch" => some «cands_lean_version_get_patch»
  | "lean_version_get_special_desc" => some «cands_lean_version_get_special_desc»
  | _ => none

end JsOp

end MoreJs

end
