module

public import JsTerm.OpsImported
public import JsTerm.OpsInlined

@[expose] public section

set_option autoImplicit false

/-!
# Finding the operation of an extern call

**Generated** by `scripts/gen_js_ops.py`; do not edit.

`JsOp.lookup name σs τ` is the operation of the extern `name` (as the catalogue spells it,
`lean_nat_div`) at the argument types `σs` and the result type `τ`, if there is one: the
constructor of `JsOpImported` or `JsOpInlined` whose signature is exactly `σs → τ` (a
polymorphic one instantiated from the types).
-/

namespace MoreJs

/-- An operation: one that calls the runtime, or one written inline. -/
inductive JsOp : List JsTy → JsTy → Type where
  | imported {σs : List JsTy} {τ : JsTy} (op : JsOpImported σs τ) : JsOp σs τ
  | inlined {σs : List JsTy} {τ : JsTy} (op : JsOpInlined σs τ) : JsOp σs τ

namespace JsOp

/-- The name of the operation. -/
def name {σs : List JsTy} {τ : JsTy} : JsOp σs τ → String
  | .imported op => op.name
  | .inlined op => op.name

/-- The operation at the signature `σs → τ`, if it is its own. -/
def ofSig {σs' : List JsTy} {τ' : JsTy} (op : JsOp σs' τ') (σs : List JsTy) (τ : JsTy) :
    Option (JsOp σs τ) :=
  if h : σs' = σs ∧ τ' = τ then some (h.1 ▸ h.2 ▸ op) else none

/-- The first operation of a list of candidates that has the signature `σs → τ`. -/
def firstOf (σs : List JsTy) (τ : JsTy) : List (Σ σs' τ', JsOp σs' τ') → Option (JsOp σs τ)
  | [] => none
  | ⟨_, _, op⟩ :: rest => (op.ofSig σs τ).orElse fun _ => firstOf σs τ rest

/-- The type a thunk operation delays (the first delay among the types). -/
def elemOf? : List JsTy → JsTy
  | [] => .terminal .bool
  | .thunk t :: _ => t
  | .lazy t :: _ => t
  | _ :: ts => elemOf? ts

/-- The layout of the array among the argument types (the first one that is an array). -/
def layoutOf? : List JsTy → Option (Σ a e, JsArrayLayout a e)
  | [] => none
  | t :: ts => match JsArrayLayout.of? t with
    | some ⟨e, l⟩ => some ⟨t, e, l⟩
    | none => layoutOf? ts

/-- The operations of `lean_array_fset`. -/
def «cands_lean_array_fset» (σs : List JsTy) (τ : JsTy) : List (Σ σs' τ', JsOp σs' τ') :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, .imported (.bigint_nat__lean_array_fset l)⟩] | none => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, .imported (.uint53__lean_array_fset l)⟩] | none => [])

/-- The operations of `lean_array_fswap`. -/
def «cands_lean_array_fswap» (σs : List JsTy) (τ : JsTy) : List (Σ σs' τ', JsOp σs' τ') :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, .imported (.bigint_nat__lean_array_fswap l)⟩] | none => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, .imported (.uint53__lean_array_fswap l)⟩] | none => [])

/-- The operations of `lean_array_get`. -/
def «cands_lean_array_get» (σs : List JsTy) (τ : JsTy) : List (Σ σs' τ', JsOp σs' τ') :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, .imported (.bigint_nat__lean_array_get l)⟩] | none => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, .imported (.uint53__lean_array_get l)⟩] | none => [])

/-- The operations of `lean_array_get_borrowed`. -/
def «cands_lean_array_get_borrowed» (σs : List JsTy) (τ : JsTy) : List (Σ σs' τ', JsOp σs' τ') :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, .imported (.bigint_nat__lean_array_get_borrowed l)⟩] | none => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, .imported (.uint53__lean_array_get_borrowed l)⟩] | none => [])

/-- The operations of `lean_array_get_size`. -/
def «cands_lean_array_get_size» (σs : List JsTy) (τ : JsTy) : List (Σ σs' τ', JsOp σs' τ') :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, .inlined (.bigint_nat__lean_array_get_size l)⟩] | none => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, .inlined (.uint53__lean_array_get_size l)⟩] | none => [])

/-- The operations of `lean_array_mk`. -/
def «cands_lean_array_mk» (σs : List JsTy) (τ : JsTy) : List (Σ σs' τ', JsOp σs' τ') :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .generic α⟩ => [⟨_, _, .inlined (.array__lean_array_mk α)⟩] | _ => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .typed k e⟩ => [⟨_, _, .inlined (.typedArray__lean_array_mk k e)⟩] | _ => [])

/-- The operations of `lean_array_pop`. -/
def «cands_lean_array_pop» (σs : List JsTy) (τ : JsTy) : List (Σ σs' τ', JsOp σs' τ') :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, .imported (.array__lean_array_pop l)⟩] | none => [])

/-- The operations of `lean_array_push`. -/
def «cands_lean_array_push» (σs : List JsTy) (τ : JsTy) : List (Σ σs' τ', JsOp σs' τ') :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, .imported (.array__lean_array_push l)⟩] | none => [])

/-- The operations of `lean_array_set`. -/
def «cands_lean_array_set» (σs : List JsTy) (τ : JsTy) : List (Σ σs' τ', JsOp σs' τ') :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, .imported (.bigint_nat__lean_array_set l)⟩] | none => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, .imported (.uint53__lean_array_set l)⟩] | none => [])

/-- The operations of `lean_array_swap`. -/
def «cands_lean_array_swap» (σs : List JsTy) (τ : JsTy) : List (Σ σs' τ', JsOp σs' τ') :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, .imported (.bigint_nat__lean_array_swap l)⟩] | none => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, .imported (.uint53__lean_array_swap l)⟩] | none => [])

/-- The operations of `lean_array_to_list`. -/
def «cands_lean_array_to_list» (σs : List JsTy) (τ : JsTy) : List (Σ σs' τ', JsOp σs' τ') :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .generic α⟩ => [⟨_, _, .inlined (.array__lean_array_to_list α)⟩] | _ => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .typed k e⟩ => [⟨_, _, .imported (.typedArray__lean_array_to_list k e)⟩] | _ => [])

/-- The operations of `lean_bool_to_int16`. -/
def «cands_lean_bool_to_int16» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bool__lean_bool_to_int16⟩]

/-- The operations of `lean_bool_to_int32`. -/
def «cands_lean_bool_to_int32» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bool__lean_bool_to_int32⟩]

/-- The operations of `lean_bool_to_int64`. -/
def «cands_lean_bool_to_int64» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_int__lean_bool_to_int64⟩, ⟨_, _, .imported .int53__lean_bool_to_int64⟩]

/-- The operations of `lean_bool_to_int8`. -/
def «cands_lean_bool_to_int8» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bool__lean_bool_to_int8⟩]

/-- The operations of `lean_bool_to_uint16`. -/
def «cands_lean_bool_to_uint16» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bool__lean_bool_to_uint16⟩]

/-- The operations of `lean_bool_to_uint32`. -/
def «cands_lean_bool_to_uint32» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bool__lean_bool_to_uint32⟩]

/-- The operations of `lean_bool_to_uint64`. -/
def «cands_lean_bool_to_uint64» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_bool_to_uint64⟩, ⟨_, _, .imported .uint53__lean_bool_to_uint64⟩]

/-- The operations of `lean_bool_to_uint8`. -/
def «cands_lean_bool_to_uint8» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bool__lean_bool_to_uint8⟩]

/-- The operations of `lean_float32_add`. -/
def «cands_lean_float32_add» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .float32__lean_float32_add⟩]

/-- The operations of `lean_float32_beq`. -/
def «cands_lean_float32_beq» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .float32__lean_float32_beq⟩]

/-- The operations of `lean_float32_decLe__Float32_decLe`. -/
def «cands_lean_float32_decLe__Float32_decLe» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .float32__lean_float32_decLe__Float32_decLe⟩]

/-- The operations of `lean_float32_decLe__Float32_le`. -/
def «cands_lean_float32_decLe__Float32_le» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .float32__lean_float32_decLe__Float32_le⟩]

/-- The operations of `lean_float32_decLt__Float32_decLt`. -/
def «cands_lean_float32_decLt__Float32_decLt» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .float32__lean_float32_decLt__Float32_decLt⟩]

/-- The operations of `lean_float32_decLt__Float32_lt`. -/
def «cands_lean_float32_decLt__Float32_lt» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .float32__lean_float32_decLt__Float32_lt⟩]

/-- The operations of `lean_float32_div`. -/
def «cands_lean_float32_div» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .float32__lean_float32_div⟩]

/-- The operations of `lean_float32_isfinite`. -/
def «cands_lean_float32_isfinite» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .float32__lean_float32_isfinite⟩]

/-- The operations of `lean_float32_isinf`. -/
def «cands_lean_float32_isinf» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .float32__lean_float32_isinf⟩]

/-- The operations of `lean_float32_isnan`. -/
def «cands_lean_float32_isnan» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .float32__lean_float32_isnan⟩]

/-- The operations of `lean_float32_mul`. -/
def «cands_lean_float32_mul» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .float32__lean_float32_mul⟩]

/-- The operations of `lean_float32_negate`. -/
def «cands_lean_float32_negate» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .float32__lean_float32_negate⟩]

/-- The operations of `lean_float32_of_bits__Float32_ofModel`. -/
def «cands_lean_float32_of_bits__Float32_ofModel» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .float32__lean_float32_of_bits__Float32_ofModel⟩]

/-- The operations of `lean_float32_sub`. -/
def «cands_lean_float32_sub» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .float32__lean_float32_sub⟩]

/-- The operations of `lean_float32_to_bits__Float32_toModel`. -/
def «cands_lean_float32_to_bits__Float32_toModel» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .float32__lean_float32_to_bits__Float32_toModel⟩]

/-- The operations of `lean_float32_to_float`. -/
def «cands_lean_float32_to_float» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .float32__lean_float32_to_float⟩]

/-- The operations of `lean_float_add`. -/
def «cands_lean_float_add» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .float__lean_float_add⟩]

/-- The operations of `lean_float_beq`. -/
def «cands_lean_float_beq» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .float__lean_float_beq⟩]

/-- The operations of `lean_float_decLe__Float_decLe`. -/
def «cands_lean_float_decLe__Float_decLe» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .float__lean_float_decLe__Float_decLe⟩]

/-- The operations of `lean_float_decLe__Float_le`. -/
def «cands_lean_float_decLe__Float_le» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .float__lean_float_decLe__Float_le⟩]

/-- The operations of `lean_float_decLt__Float_decLt`. -/
def «cands_lean_float_decLt__Float_decLt» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .float__lean_float_decLt__Float_decLt⟩]

/-- The operations of `lean_float_decLt__Float_lt`. -/
def «cands_lean_float_decLt__Float_lt» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .float__lean_float_decLt__Float_lt⟩]

/-- The operations of `lean_float_div`. -/
def «cands_lean_float_div» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .float__lean_float_div⟩]

/-- The operations of `lean_float_isfinite`. -/
def «cands_lean_float_isfinite» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .float__lean_float_isfinite⟩]

/-- The operations of `lean_float_isinf`. -/
def «cands_lean_float_isinf» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .float__lean_float_isinf⟩]

/-- The operations of `lean_float_isnan`. -/
def «cands_lean_float_isnan» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .float__lean_float_isnan⟩]

/-- The operations of `lean_float_mul`. -/
def «cands_lean_float_mul» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .float__lean_float_mul⟩]

/-- The operations of `lean_float_negate`. -/
def «cands_lean_float_negate» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .float__lean_float_negate⟩]

/-- The operations of `lean_float_of_bits__Float_ofModel`. -/
def «cands_lean_float_of_bits__Float_ofModel» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .float__lean_float_of_bits__Float_ofModel⟩]

/-- The operations of `lean_float_sub`. -/
def «cands_lean_float_sub» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .float__lean_float_sub⟩]

/-- The operations of `lean_float_to_bits__Float_toModel`. -/
def «cands_lean_float_to_bits__Float_toModel» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .float__lean_float_to_bits__Float_toModel⟩]

/-- The operations of `lean_float_to_float32`. -/
def «cands_lean_float_to_float32» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .float__lean_float_to_float32⟩]

/-- The operations of `lean_int16_abs`. -/
def «cands_lean_int16_abs» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int16__lean_int16_abs⟩]

/-- The operations of `lean_int16_add`. -/
def «cands_lean_int16_add» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int16__lean_int16_add⟩]

/-- The operations of `lean_int16_complement`. -/
def «cands_lean_int16_complement» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int16__lean_int16_complement⟩]

/-- The operations of `lean_int16_dec_eq`. -/
def «cands_lean_int16_dec_eq» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .int16__lean_int16_dec_eq⟩]

/-- The operations of `lean_int16_dec_le`. -/
def «cands_lean_int16_dec_le» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .int16__lean_int16_dec_le⟩]

/-- The operations of `lean_int16_dec_lt`. -/
def «cands_lean_int16_dec_lt» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .int16__lean_int16_dec_lt⟩]

/-- The operations of `lean_int16_div`. -/
def «cands_lean_int16_div» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int16__lean_int16_div⟩]

/-- The operations of `lean_int16_land`. -/
def «cands_lean_int16_land» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int16__lean_int16_land⟩]

/-- The operations of `lean_int16_lor`. -/
def «cands_lean_int16_lor» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int16__lean_int16_lor⟩]

/-- The operations of `lean_int16_mod`. -/
def «cands_lean_int16_mod» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int16__lean_int16_mod⟩]

/-- The operations of `lean_int16_mul`. -/
def «cands_lean_int16_mul» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int16__lean_int16_mul⟩]

/-- The operations of `lean_int16_neg`. -/
def «cands_lean_int16_neg» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int16__lean_int16_neg⟩]

/-- The operations of `lean_int16_of_int`. -/
def «cands_lean_int16_of_int» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_int__lean_int16_of_int⟩, ⟨_, _, .imported .int53__lean_int16_of_int⟩]

/-- The operations of `lean_int16_of_nat`. -/
def «cands_lean_int16_of_nat» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_int16_of_nat⟩, ⟨_, _, .imported .uint53__lean_int16_of_nat⟩]

/-- The operations of `lean_int16_shift_left`. -/
def «cands_lean_int16_shift_left» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int16__lean_int16_shift_left⟩]

/-- The operations of `lean_int16_shift_right`. -/
def «cands_lean_int16_shift_right» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int16__lean_int16_shift_right⟩]

/-- The operations of `lean_int16_sub`. -/
def «cands_lean_int16_sub» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int16__lean_int16_sub⟩]

/-- The operations of `lean_int16_to_float`. -/
def «cands_lean_int16_to_float» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .int16__lean_int16_to_float⟩]

/-- The operations of `lean_int16_to_float32`. -/
def «cands_lean_int16_to_float32» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .int16__lean_int16_to_float32⟩]

/-- The operations of `lean_int16_to_int`. -/
def «cands_lean_int16_to_int» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_int__lean_int16_to_int⟩, ⟨_, _, .inlined .int53__lean_int16_to_int⟩]

/-- The operations of `lean_int16_to_int32`. -/
def «cands_lean_int16_to_int32» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .int16__lean_int16_to_int32⟩]

/-- The operations of `lean_int16_to_int64`. -/
def «cands_lean_int16_to_int64» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_int__lean_int16_to_int64⟩, ⟨_, _, .inlined .int53__lean_int16_to_int64⟩]

/-- The operations of `lean_int16_to_int8`. -/
def «cands_lean_int16_to_int8» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int16__lean_int16_to_int8⟩]

/-- The operations of `lean_int16_xor`. -/
def «cands_lean_int16_xor» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int16__lean_int16_xor⟩]

/-- The operations of `lean_int32_abs`. -/
def «cands_lean_int32_abs» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int32__lean_int32_abs⟩]

/-- The operations of `lean_int32_add`. -/
def «cands_lean_int32_add» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int32__lean_int32_add⟩]

/-- The operations of `lean_int32_complement`. -/
def «cands_lean_int32_complement» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int32__lean_int32_complement⟩]

/-- The operations of `lean_int32_dec_eq`. -/
def «cands_lean_int32_dec_eq» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .int32__lean_int32_dec_eq⟩]

/-- The operations of `lean_int32_dec_le`. -/
def «cands_lean_int32_dec_le» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .int32__lean_int32_dec_le⟩]

/-- The operations of `lean_int32_dec_lt`. -/
def «cands_lean_int32_dec_lt» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .int32__lean_int32_dec_lt⟩]

/-- The operations of `lean_int32_div`. -/
def «cands_lean_int32_div» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int32__lean_int32_div⟩]

/-- The operations of `lean_int32_land`. -/
def «cands_lean_int32_land» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int32__lean_int32_land⟩]

/-- The operations of `lean_int32_lor`. -/
def «cands_lean_int32_lor» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int32__lean_int32_lor⟩]

/-- The operations of `lean_int32_mod`. -/
def «cands_lean_int32_mod» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int32__lean_int32_mod⟩]

/-- The operations of `lean_int32_mul`. -/
def «cands_lean_int32_mul» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int32__lean_int32_mul⟩]

/-- The operations of `lean_int32_neg`. -/
def «cands_lean_int32_neg» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int32__lean_int32_neg⟩]

/-- The operations of `lean_int32_of_int`. -/
def «cands_lean_int32_of_int» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_int__lean_int32_of_int⟩, ⟨_, _, .imported .int53__lean_int32_of_int⟩]

/-- The operations of `lean_int32_of_nat`. -/
def «cands_lean_int32_of_nat» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_int32_of_nat⟩, ⟨_, _, .imported .uint53__lean_int32_of_nat⟩]

/-- The operations of `lean_int32_shift_left`. -/
def «cands_lean_int32_shift_left» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int32__lean_int32_shift_left⟩]

/-- The operations of `lean_int32_shift_right`. -/
def «cands_lean_int32_shift_right» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int32__lean_int32_shift_right⟩]

/-- The operations of `lean_int32_sub`. -/
def «cands_lean_int32_sub» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int32__lean_int32_sub⟩]

/-- The operations of `lean_int32_to_float`. -/
def «cands_lean_int32_to_float» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .int32__lean_int32_to_float⟩]

/-- The operations of `lean_int32_to_float32`. -/
def «cands_lean_int32_to_float32» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .int32__lean_int32_to_float32⟩]

/-- The operations of `lean_int32_to_int`. -/
def «cands_lean_int32_to_int» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_int__lean_int32_to_int⟩, ⟨_, _, .inlined .int53__lean_int32_to_int⟩]

/-- The operations of `lean_int32_to_int16`. -/
def «cands_lean_int32_to_int16» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int32__lean_int32_to_int16⟩]

/-- The operations of `lean_int32_to_int64`. -/
def «cands_lean_int32_to_int64» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_int__lean_int32_to_int64⟩, ⟨_, _, .inlined .int53__lean_int32_to_int64⟩]

/-- The operations of `lean_int32_to_int8`. -/
def «cands_lean_int32_to_int8» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int32__lean_int32_to_int8⟩]

/-- The operations of `lean_int32_xor`. -/
def «cands_lean_int32_xor» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int32__lean_int32_xor⟩]

/-- The operations of `lean_int64_abs`. -/
def «cands_lean_int64_abs» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_int__lean_int64_abs⟩, ⟨_, _, .imported .int53__lean_int64_abs⟩]

/-- The operations of `lean_int64_add`. -/
def «cands_lean_int64_add» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_int__lean_int64_add⟩, ⟨_, _, .imported .int53__lean_int64_add⟩]

/-- The operations of `lean_int64_complement`. -/
def «cands_lean_int64_complement» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_int__lean_int64_complement⟩, ⟨_, _, .imported .int53__lean_int64_complement⟩]

/-- The operations of `lean_int64_dec_eq`. -/
def «cands_lean_int64_dec_eq» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_int__lean_int64_dec_eq⟩, ⟨_, _, .inlined .int53__lean_int64_dec_eq⟩]

/-- The operations of `lean_int64_dec_le`. -/
def «cands_lean_int64_dec_le» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_int__lean_int64_dec_le⟩, ⟨_, _, .inlined .int53__lean_int64_dec_le⟩]

/-- The operations of `lean_int64_dec_lt`. -/
def «cands_lean_int64_dec_lt» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_int__lean_int64_dec_lt⟩, ⟨_, _, .inlined .int53__lean_int64_dec_lt⟩]

/-- The operations of `lean_int64_div`. -/
def «cands_lean_int64_div» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_int__lean_int64_div⟩, ⟨_, _, .imported .int53__lean_int64_div⟩]

/-- The operations of `lean_int64_land`. -/
def «cands_lean_int64_land» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_int__lean_int64_land⟩, ⟨_, _, .imported .int53__lean_int64_land⟩]

/-- The operations of `lean_int64_lor`. -/
def «cands_lean_int64_lor» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_int__lean_int64_lor⟩, ⟨_, _, .imported .int53__lean_int64_lor⟩]

/-- The operations of `lean_int64_mod`. -/
def «cands_lean_int64_mod» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_int__lean_int64_mod⟩, ⟨_, _, .imported .int53__lean_int64_mod⟩]

/-- The operations of `lean_int64_mul`. -/
def «cands_lean_int64_mul» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_int__lean_int64_mul⟩, ⟨_, _, .imported .int53__lean_int64_mul⟩]

/-- The operations of `lean_int64_neg`. -/
def «cands_lean_int64_neg» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_int__lean_int64_neg⟩, ⟨_, _, .imported .int53__lean_int64_neg⟩]

/-- The operations of `lean_int64_of_int`. -/
def «cands_lean_int64_of_int» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_int__lean_int64_of_int⟩, ⟨_, _, .imported .bigint_int__int53__lean_int64_of_int⟩, ⟨_, _, .imported .int53__bigint_int__lean_int64_of_int⟩, ⟨_, _, .imported .int53__lean_int64_of_int⟩]

/-- The operations of `lean_int64_of_nat`. -/
def «cands_lean_int64_of_nat» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__bigint_int__lean_int64_of_nat⟩, ⟨_, _, .imported .bigint_nat__int53__lean_int64_of_nat⟩, ⟨_, _, .imported .uint53__bigint_int__lean_int64_of_nat⟩, ⟨_, _, .imported .uint53__int53__lean_int64_of_nat⟩]

/-- The operations of `lean_int64_shift_left`. -/
def «cands_lean_int64_shift_left» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_int__lean_int64_shift_left⟩, ⟨_, _, .imported .int53__lean_int64_shift_left⟩]

/-- The operations of `lean_int64_shift_right`. -/
def «cands_lean_int64_shift_right» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_int__lean_int64_shift_right⟩, ⟨_, _, .imported .int53__lean_int64_shift_right⟩]

/-- The operations of `lean_int64_sub`. -/
def «cands_lean_int64_sub» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_int__lean_int64_sub⟩, ⟨_, _, .imported .int53__lean_int64_sub⟩]

/-- The operations of `lean_int64_to_float`. -/
def «cands_lean_int64_to_float» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_int__lean_int64_to_float⟩, ⟨_, _, .inlined .int53__lean_int64_to_float⟩]

/-- The operations of `lean_int64_to_float32`. -/
def «cands_lean_int64_to_float32» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_int__lean_int64_to_float32⟩, ⟨_, _, .inlined .int53__lean_int64_to_float32⟩]

/-- The operations of `lean_int64_to_int16`. -/
def «cands_lean_int64_to_int16» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_int__lean_int64_to_int16⟩, ⟨_, _, .imported .int53__lean_int64_to_int16⟩]

/-- The operations of `lean_int64_to_int32`. -/
def «cands_lean_int64_to_int32» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_int__lean_int64_to_int32⟩, ⟨_, _, .imported .int53__lean_int64_to_int32⟩]

/-- The operations of `lean_int64_to_int8`. -/
def «cands_lean_int64_to_int8» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_int__lean_int64_to_int8⟩, ⟨_, _, .imported .int53__lean_int64_to_int8⟩]

/-- The operations of `lean_int64_to_int_sint`. -/
def «cands_lean_int64_to_int_sint» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_int__lean_int64_to_int_sint⟩, ⟨_, _, .imported .bigint_int__int53__lean_int64_to_int_sint⟩, ⟨_, _, .inlined .int53__bigint_int__lean_int64_to_int_sint⟩, ⟨_, _, .inlined .int53__lean_int64_to_int_sint⟩]

/-- The operations of `lean_int64_xor`. -/
def «cands_lean_int64_xor» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_int__lean_int64_xor⟩, ⟨_, _, .imported .int53__lean_int64_xor⟩]

/-- The operations of `lean_int8_abs`. -/
def «cands_lean_int8_abs» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int8__lean_int8_abs⟩]

/-- The operations of `lean_int8_add`. -/
def «cands_lean_int8_add» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int8__lean_int8_add⟩]

/-- The operations of `lean_int8_complement`. -/
def «cands_lean_int8_complement» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int8__lean_int8_complement⟩]

/-- The operations of `lean_int8_dec_eq`. -/
def «cands_lean_int8_dec_eq» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .int8__lean_int8_dec_eq⟩]

/-- The operations of `lean_int8_dec_le`. -/
def «cands_lean_int8_dec_le» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .int8__lean_int8_dec_le⟩]

/-- The operations of `lean_int8_dec_lt`. -/
def «cands_lean_int8_dec_lt» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .int8__lean_int8_dec_lt⟩]

/-- The operations of `lean_int8_div`. -/
def «cands_lean_int8_div» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int8__lean_int8_div⟩]

/-- The operations of `lean_int8_land`. -/
def «cands_lean_int8_land» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int8__lean_int8_land⟩]

/-- The operations of `lean_int8_lor`. -/
def «cands_lean_int8_lor» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int8__lean_int8_lor⟩]

/-- The operations of `lean_int8_mod`. -/
def «cands_lean_int8_mod» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int8__lean_int8_mod⟩]

/-- The operations of `lean_int8_mul`. -/
def «cands_lean_int8_mul» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int8__lean_int8_mul⟩]

/-- The operations of `lean_int8_neg`. -/
def «cands_lean_int8_neg» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int8__lean_int8_neg⟩]

/-- The operations of `lean_int8_of_int`. -/
def «cands_lean_int8_of_int» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_int__lean_int8_of_int⟩, ⟨_, _, .imported .int53__lean_int8_of_int⟩]

/-- The operations of `lean_int8_of_nat`. -/
def «cands_lean_int8_of_nat» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_int8_of_nat⟩, ⟨_, _, .imported .uint53__lean_int8_of_nat⟩]

/-- The operations of `lean_int8_shift_left`. -/
def «cands_lean_int8_shift_left» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int8__lean_int8_shift_left⟩]

/-- The operations of `lean_int8_shift_right`. -/
def «cands_lean_int8_shift_right» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int8__lean_int8_shift_right⟩]

/-- The operations of `lean_int8_sub`. -/
def «cands_lean_int8_sub» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int8__lean_int8_sub⟩]

/-- The operations of `lean_int8_to_float`. -/
def «cands_lean_int8_to_float» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .int8__lean_int8_to_float⟩]

/-- The operations of `lean_int8_to_float32`. -/
def «cands_lean_int8_to_float32» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .int8__lean_int8_to_float32⟩]

/-- The operations of `lean_int8_to_int`. -/
def «cands_lean_int8_to_int» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_int__lean_int8_to_int⟩, ⟨_, _, .inlined .int53__lean_int8_to_int⟩]

/-- The operations of `lean_int8_to_int16`. -/
def «cands_lean_int8_to_int16» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .int8__lean_int8_to_int16⟩]

/-- The operations of `lean_int8_to_int32`. -/
def «cands_lean_int8_to_int32» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .int8__lean_int8_to_int32⟩]

/-- The operations of `lean_int8_to_int64`. -/
def «cands_lean_int8_to_int64» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_int__lean_int8_to_int64⟩, ⟨_, _, .inlined .int53__lean_int8_to_int64⟩]

/-- The operations of `lean_int8_xor`. -/
def «cands_lean_int8_xor» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .int8__lean_int8_xor⟩]

/-- The operations of `lean_int_add`. -/
def «cands_lean_int_add» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_int__lean_int_add⟩, ⟨_, _, .imported .int53__lean_int_add⟩]

/-- The operations of `lean_int_dec_eq`. -/
def «cands_lean_int_dec_eq» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_int__lean_int_dec_eq⟩, ⟨_, _, .inlined .int53__lean_int_dec_eq⟩]

/-- The operations of `lean_int_dec_le`. -/
def «cands_lean_int_dec_le» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_int__lean_int_dec_le⟩, ⟨_, _, .inlined .int53__lean_int_dec_le⟩]

/-- The operations of `lean_int_dec_lt`. -/
def «cands_lean_int_dec_lt» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_int__lean_int_dec_lt⟩, ⟨_, _, .inlined .int53__lean_int_dec_lt⟩]

/-- The operations of `lean_int_dec_nonneg`. -/
def «cands_lean_int_dec_nonneg» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_int__lean_int_dec_nonneg⟩, ⟨_, _, .inlined .int53__lean_int_dec_nonneg⟩]

/-- The operations of `lean_int_div`. -/
def «cands_lean_int_div» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_int__lean_int_div⟩, ⟨_, _, .imported .int53__lean_int_div⟩]

/-- The operations of `lean_int_div_exact`. -/
def «cands_lean_int_div_exact» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_int__lean_int_div_exact⟩, ⟨_, _, .imported .int53__lean_int_div_exact⟩]

/-- The operations of `lean_int_ediv`. -/
def «cands_lean_int_ediv» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_int__lean_int_ediv⟩, ⟨_, _, .imported .int53__lean_int_ediv⟩]

/-- The operations of `lean_int_emod`. -/
def «cands_lean_int_emod» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_int__lean_int_emod⟩, ⟨_, _, .imported .int53__lean_int_emod⟩]

/-- The operations of `lean_int_mod`. -/
def «cands_lean_int_mod» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_int__lean_int_mod⟩, ⟨_, _, .imported .int53__lean_int_mod⟩]

/-- The operations of `lean_int_mul`. -/
def «cands_lean_int_mul» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_int__lean_int_mul⟩, ⟨_, _, .imported .int53__lean_int_mul⟩]

/-- The operations of `lean_int_neg`. -/
def «cands_lean_int_neg» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_int__lean_int_neg⟩, ⟨_, _, .imported .int53__lean_int_neg⟩]

/-- The operations of `lean_int_neg_succ_of_nat`. -/
def «cands_lean_int_neg_succ_of_nat» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__bigint_int__lean_int_neg_succ_of_nat⟩, ⟨_, _, .imported .bigint_nat__int53__lean_int_neg_succ_of_nat⟩, ⟨_, _, .imported .uint53__bigint_int__lean_int_neg_succ_of_nat⟩, ⟨_, _, .imported .uint53__int53__lean_int_neg_succ_of_nat⟩]

/-- The operations of `lean_int_sub`. -/
def «cands_lean_int_sub» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_int__lean_int_sub⟩, ⟨_, _, .imported .int53__lean_int_sub⟩]

/-- The operations of `lean_mk_array`. -/
def «cands_lean_mk_array» (σs : List JsTy) (τ : JsTy) : List (Σ σs' τ', JsOp σs' τ') :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .generic α⟩ => [⟨_, _, .imported (.bigint_nat__lean_mk_array α)⟩] | _ => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .typed k e⟩ => [⟨_, _, .imported (.typedArray__bigint_nat__lean_mk_array k e)⟩] | _ => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .generic α⟩ => [⟨_, _, .imported (.uint53__lean_mk_array α)⟩] | _ => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .typed k e⟩ => [⟨_, _, .imported (.typedArray__uint53__lean_mk_array k e)⟩] | _ => [])

/-- The operations of `lean_mk_empty_array_with_capacity__Array_emptyWithCapacity`. -/
def «cands_lean_mk_empty_array_with_capacity__Array_emptyWithCapacity» (σs : List JsTy) (τ : JsTy) : List (Σ σs' τ', JsOp σs' τ') :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .generic α⟩ => [⟨_, _, .inlined (.bigint_nat__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity α)⟩] | _ => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .typed k e⟩ => [⟨_, _, .inlined (.typedArray__bigint_nat__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity k e)⟩] | _ => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .generic α⟩ => [⟨_, _, .inlined (.uint53__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity α)⟩] | _ => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .typed k e⟩ => [⟨_, _, .inlined (.typedArray__uint53__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity k e)⟩] | _ => [])

/-- The operations of `lean_mk_empty_array_with_capacity__Array_mkEmpty`. -/
def «cands_lean_mk_empty_array_with_capacity__Array_mkEmpty» (σs : List JsTy) (τ : JsTy) : List (Σ σs' τ', JsOp σs' τ') :=
  (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .generic α⟩ => [⟨_, _, .inlined (.bigint_nat__lean_mk_empty_array_with_capacity__Array_mkEmpty α)⟩] | _ => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .typed k e⟩ => [⟨_, _, .inlined (.typedArray__bigint_nat__lean_mk_empty_array_with_capacity__Array_mkEmpty k e)⟩] | _ => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .generic α⟩ => [⟨_, _, .inlined (.uint53__lean_mk_empty_array_with_capacity__Array_mkEmpty α)⟩] | _ => []) ++ (match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .typed k e⟩ => [⟨_, _, .inlined (.typedArray__uint53__lean_mk_empty_array_with_capacity__Array_mkEmpty k e)⟩] | _ => [])

/-- The operations of `lean_mk_thunk`. -/
def «cands_lean_mk_thunk» (σs : List JsTy) (τ : JsTy) : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported (.thunk__lean_mk_thunk (elemOf? (σs ++ [τ])))⟩]

/-- The operations of `lean_nat_abs`. -/
def «cands_lean_nat_abs» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_int__bigint_nat__lean_nat_abs⟩, ⟨_, _, .imported .bigint_int__uint53__lean_nat_abs⟩, ⟨_, _, .imported .int53__bigint_nat__lean_nat_abs⟩, ⟨_, _, .imported .int53__uint53__lean_nat_abs⟩]

/-- The operations of `lean_nat_add`. -/
def «cands_lean_nat_add» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_nat__lean_nat_add⟩, ⟨_, _, .imported .uint53__lean_nat_add⟩]

/-- The operations of `lean_nat_dec_eq__Nat_beq`. -/
def «cands_lean_nat_dec_eq__Nat_beq» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_nat__lean_nat_dec_eq__Nat_beq⟩, ⟨_, _, .inlined .uint53__lean_nat_dec_eq__Nat_beq⟩]

/-- The operations of `lean_nat_dec_eq__Nat_decEq`. -/
def «cands_lean_nat_dec_eq__Nat_decEq» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_nat__lean_nat_dec_eq__Nat_decEq⟩, ⟨_, _, .inlined .uint53__lean_nat_dec_eq__Nat_decEq⟩]

/-- The operations of `lean_nat_dec_le__Nat_ble`. -/
def «cands_lean_nat_dec_le__Nat_ble» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_nat__lean_nat_dec_le__Nat_ble⟩, ⟨_, _, .inlined .uint53__lean_nat_dec_le__Nat_ble⟩]

/-- The operations of `lean_nat_dec_le__Nat_decLe`. -/
def «cands_lean_nat_dec_le__Nat_decLe» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_nat__lean_nat_dec_le__Nat_decLe⟩, ⟨_, _, .inlined .uint53__lean_nat_dec_le__Nat_decLe⟩]

/-- The operations of `lean_nat_dec_lt`. -/
def «cands_lean_nat_dec_lt» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_nat__lean_nat_dec_lt⟩, ⟨_, _, .inlined .uint53__lean_nat_dec_lt⟩]

/-- The operations of `lean_nat_div`. -/
def «cands_lean_nat_div» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_nat_div⟩, ⟨_, _, .imported .uint53__lean_nat_div⟩]

/-- The operations of `lean_nat_div_exact`. -/
def «cands_lean_nat_div_exact» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_nat_div_exact⟩, ⟨_, _, .imported .uint53__lean_nat_div_exact⟩]

/-- The operations of `lean_nat_land`. -/
def «cands_lean_nat_land» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_nat__lean_nat_land⟩, ⟨_, _, .imported .uint53__lean_nat_land⟩]

/-- The operations of `lean_nat_log2`. -/
def «cands_lean_nat_log2» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_nat_log2⟩, ⟨_, _, .imported .uint53__lean_nat_log2⟩]

/-- The operations of `lean_nat_lor`. -/
def «cands_lean_nat_lor» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_nat__lean_nat_lor⟩, ⟨_, _, .imported .uint53__lean_nat_lor⟩]

/-- The operations of `lean_nat_lxor`. -/
def «cands_lean_nat_lxor» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_nat__lean_nat_lxor⟩, ⟨_, _, .imported .uint53__lean_nat_lxor⟩]

/-- The operations of `lean_nat_mod__Nat_mod`. -/
def «cands_lean_nat_mod__Nat_mod» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_nat_mod__Nat_mod⟩, ⟨_, _, .imported .uint53__lean_nat_mod__Nat_mod⟩]

/-- The operations of `lean_nat_mod__Nat_modCore`. -/
def «cands_lean_nat_mod__Nat_modCore» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_nat_mod__Nat_modCore⟩, ⟨_, _, .imported .uint53__lean_nat_mod__Nat_modCore⟩]

/-- The operations of `lean_nat_mul`. -/
def «cands_lean_nat_mul» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_nat__lean_nat_mul⟩, ⟨_, _, .imported .uint53__lean_nat_mul⟩]

/-- The operations of `lean_nat_pow`. -/
def «cands_lean_nat_pow» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_nat_pow⟩, ⟨_, _, .imported .uint53__lean_nat_pow⟩]

/-- The operations of `lean_nat_pred`. -/
def «cands_lean_nat_pred» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_nat_pred⟩, ⟨_, _, .imported .uint53__lean_nat_pred⟩]

/-- The operations of `lean_nat_shiftl`. -/
def «cands_lean_nat_shiftl» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_nat__lean_nat_shiftl⟩, ⟨_, _, .imported .uint53__lean_nat_shiftl⟩]

/-- The operations of `lean_nat_shiftr`. -/
def «cands_lean_nat_shiftr» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_nat__lean_nat_shiftr⟩, ⟨_, _, .imported .uint53__lean_nat_shiftr⟩]

/-- The operations of `lean_nat_sub`. -/
def «cands_lean_nat_sub» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_nat_sub⟩, ⟨_, _, .imported .uint53__lean_nat_sub⟩]

/-- The operations of `lean_nat_to_int`. -/
def «cands_lean_nat_to_int» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_nat__bigint_int__lean_nat_to_int⟩, ⟨_, _, .imported .bigint_nat__int53__lean_nat_to_int⟩, ⟨_, _, .inlined .uint53__bigint_int__lean_nat_to_int⟩, ⟨_, _, .inlined .uint53__int53__lean_nat_to_int⟩]

/-- The operations of `lean_strict_and`. -/
def «cands_lean_strict_and» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bool__lean_strict_and⟩]

/-- The operations of `lean_strict_or`. -/
def «cands_lean_strict_or» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bool__lean_strict_or⟩]

/-- The operations of `lean_string_append__String_Internal_append`. -/
def «cands_lean_string_append__String_Internal_append» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .string__lean_string_append__String_Internal_append⟩]

/-- The operations of `lean_string_append__String_append`. -/
def «cands_lean_string_append__String_append» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .string__lean_string_append__String_append⟩]

/-- The operations of `lean_string_compare`. -/
def «cands_lean_string_compare» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .string__lean_string_compare⟩]

/-- The operations of `lean_string_data__String_data`. -/
def «cands_lean_string_data__String_data» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .string__lean_string_data__String_data⟩]

/-- The operations of `lean_string_data__String_toList`. -/
def «cands_lean_string_data__String_toList» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .string__lean_string_data__String_toList⟩]

/-- The operations of `lean_string_dec_eq`. -/
def «cands_lean_string_dec_eq» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .string__lean_string_dec_eq⟩]

/-- The operations of `lean_string_dec_lt`. -/
def «cands_lean_string_dec_lt» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .string__lean_string_dec_lt⟩]

/-- The operations of `lean_string_hash`. -/
def «cands_lean_string_hash» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_string_hash⟩, ⟨_, _, .imported .uint53__lean_string_hash⟩]

/-- The operations of `lean_string_isempty`. -/
def «cands_lean_string_isempty» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .string__lean_string_isempty⟩]

/-- The operations of `lean_string_length__String_Internal_length`. -/
def «cands_lean_string_length__String_Internal_length» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_string_length__String_Internal_length⟩, ⟨_, _, .imported .uint53__lean_string_length__String_Internal_length⟩]

/-- The operations of `lean_string_length__String_length`. -/
def «cands_lean_string_length__String_length» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_string_length__String_length⟩, ⟨_, _, .imported .uint53__lean_string_length__String_length⟩]

/-- The operations of `lean_string_memcmp`. -/
def «cands_lean_string_memcmp» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .string__lean_string_memcmp⟩]

/-- The operations of `lean_string_mk__String_mk`. -/
def «cands_lean_string_mk__String_mk» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .string__lean_string_mk__String_mk⟩]

/-- The operations of `lean_string_mk__String_ofList`. -/
def «cands_lean_string_mk__String_ofList» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .string__lean_string_mk__String_ofList⟩]

/-- The operations of `lean_string_push`. -/
def «cands_lean_string_push» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .string__lean_string_push⟩]

/-- The operations of `lean_string_pushn`. -/
def «cands_lean_string_pushn» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_string_pushn⟩, ⟨_, _, .imported .uint53__lean_string_pushn⟩]

/-- The operations of `lean_string_utf8_at_end__String_Internal_atEnd`. -/
def «cands_lean_string_utf8_at_end__String_Internal_atEnd» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .string__lean_string_utf8_at_end__String_Internal_atEnd⟩]

/-- The operations of `lean_string_utf8_at_end__String_Pos_Raw_atEnd`. -/
def «cands_lean_string_utf8_at_end__String_Pos_Raw_atEnd» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .string__lean_string_utf8_at_end__String_Pos_Raw_atEnd⟩]

/-- The operations of `lean_string_utf8_at_end__String_atEnd`. -/
def «cands_lean_string_utf8_at_end__String_atEnd» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .string__lean_string_utf8_at_end__String_atEnd⟩]

/-- The operations of `lean_string_utf8_byte_size`. -/
def «cands_lean_string_utf8_byte_size» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_string_utf8_byte_size⟩, ⟨_, _, .imported .uint53__lean_string_utf8_byte_size⟩]

/-- The operations of `lean_string_utf8_extract__String_Internal_extract`. -/
def «cands_lean_string_utf8_extract__String_Internal_extract» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .string__lean_string_utf8_extract__String_Internal_extract⟩]

/-- The operations of `lean_string_utf8_extract__String_Pos_Raw_extract`. -/
def «cands_lean_string_utf8_extract__String_Pos_Raw_extract» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .string__lean_string_utf8_extract__String_Pos_Raw_extract⟩]

/-- The operations of `lean_string_utf8_get__String_Internal_get`. -/
def «cands_lean_string_utf8_get__String_Internal_get» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .string__lean_string_utf8_get__String_Internal_get⟩]

/-- The operations of `lean_string_utf8_get__String_Pos_Raw_get`. -/
def «cands_lean_string_utf8_get__String_Pos_Raw_get» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .string__lean_string_utf8_get__String_Pos_Raw_get⟩]

/-- The operations of `lean_string_utf8_get__String_get`. -/
def «cands_lean_string_utf8_get__String_get» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .string__lean_string_utf8_get__String_get⟩]

/-- The operations of `lean_string_utf8_next__String_Internal_next`. -/
def «cands_lean_string_utf8_next__String_Internal_next» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .string__lean_string_utf8_next__String_Internal_next⟩]

/-- The operations of `lean_string_utf8_next__String_Pos_Raw_next`. -/
def «cands_lean_string_utf8_next__String_Pos_Raw_next» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .string__lean_string_utf8_next__String_Pos_Raw_next⟩]

/-- The operations of `lean_string_utf8_next__String_next`. -/
def «cands_lean_string_utf8_next__String_next» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .string__lean_string_utf8_next__String_next⟩]

/-- The operations of `lean_string_utf8_set__String_Pos_Raw_set`. -/
def «cands_lean_string_utf8_set__String_Pos_Raw_set» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .string__lean_string_utf8_set__String_Pos_Raw_set⟩]

/-- The operations of `lean_string_utf8_set__String_Pos_set`. -/
def «cands_lean_string_utf8_set__String_Pos_set» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint53__lean_string_utf8_set__String_Pos_set⟩]

/-- The operations of `lean_string_utf8_set__String_set`. -/
def «cands_lean_string_utf8_set__String_set» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .string__lean_string_utf8_set__String_set⟩]

/-- The operations of `lean_thunk_get_own`. -/
def «cands_lean_thunk_get_own» (σs : List JsTy) (τ : JsTy) : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported (.thunk__lean_thunk_get_own (elemOf? (σs ++ [τ])))⟩]

/-- The operations of `lean_thunk_pure`. -/
def «cands_lean_thunk_pure» (σs : List JsTy) (τ : JsTy) : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported (.thunk__lean_thunk_pure (elemOf? (σs ++ [τ])))⟩]

/-- The operations of `lean_uint16_add`. -/
def «cands_lean_uint16_add» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint16__lean_uint16_add⟩]

/-- The operations of `lean_uint16_complement`. -/
def «cands_lean_uint16_complement» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint16__lean_uint16_complement⟩]

/-- The operations of `lean_uint16_dec_eq`. -/
def «cands_lean_uint16_dec_eq» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .uint16__lean_uint16_dec_eq⟩]

/-- The operations of `lean_uint16_dec_le`. -/
def «cands_lean_uint16_dec_le» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .uint16__lean_uint16_dec_le⟩]

/-- The operations of `lean_uint16_dec_lt`. -/
def «cands_lean_uint16_dec_lt» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .uint16__lean_uint16_dec_lt⟩]

/-- The operations of `lean_uint16_div`. -/
def «cands_lean_uint16_div» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint16__lean_uint16_div⟩]

/-- The operations of `lean_uint16_land`. -/
def «cands_lean_uint16_land» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint16__lean_uint16_land⟩]

/-- The operations of `lean_uint16_log2`. -/
def «cands_lean_uint16_log2» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint16__lean_uint16_log2⟩]

/-- The operations of `lean_uint16_lor`. -/
def «cands_lean_uint16_lor» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint16__lean_uint16_lor⟩]

/-- The operations of `lean_uint16_mod`. -/
def «cands_lean_uint16_mod» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint16__lean_uint16_mod⟩]

/-- The operations of `lean_uint16_mul`. -/
def «cands_lean_uint16_mul» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint16__lean_uint16_mul⟩]

/-- The operations of `lean_uint16_neg`. -/
def «cands_lean_uint16_neg» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint16__lean_uint16_neg⟩]

/-- The operations of `lean_uint16_of_nat__UInt16_ofNat`. -/
def «cands_lean_uint16_of_nat__UInt16_ofNat» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_uint16_of_nat__UInt16_ofNat⟩, ⟨_, _, .imported .uint53__lean_uint16_of_nat__UInt16_ofNat⟩]

/-- The operations of `lean_uint16_of_nat__UInt16_ofNatLT`. -/
def «cands_lean_uint16_of_nat__UInt16_ofNatLT» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_uint16_of_nat__UInt16_ofNatLT⟩, ⟨_, _, .imported .uint53__lean_uint16_of_nat__UInt16_ofNatLT⟩]

/-- The operations of `lean_uint16_of_nat_mk`. -/
def «cands_lean_uint16_of_nat_mk» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bitvec16__lean_uint16_of_nat_mk⟩]

/-- The operations of `lean_uint16_shift_left`. -/
def «cands_lean_uint16_shift_left» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint16__lean_uint16_shift_left⟩]

/-- The operations of `lean_uint16_shift_right`. -/
def «cands_lean_uint16_shift_right» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint16__lean_uint16_shift_right⟩]

/-- The operations of `lean_uint16_sub`. -/
def «cands_lean_uint16_sub» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint16__lean_uint16_sub⟩]

/-- The operations of `lean_uint16_to_float`. -/
def «cands_lean_uint16_to_float» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .uint16__lean_uint16_to_float⟩]

/-- The operations of `lean_uint16_to_float32`. -/
def «cands_lean_uint16_to_float32» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .uint16__lean_uint16_to_float32⟩]

/-- The operations of `lean_uint16_to_nat__UInt16_toBitVec`. -/
def «cands_lean_uint16_to_nat__UInt16_toBitVec» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .uint16__lean_uint16_to_nat__UInt16_toBitVec⟩]

/-- The operations of `lean_uint16_to_nat__UInt16_toNat`. -/
def «cands_lean_uint16_to_nat__UInt16_toNat» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_nat__lean_uint16_to_nat__UInt16_toNat⟩, ⟨_, _, .inlined .uint53__lean_uint16_to_nat__UInt16_toNat⟩]

/-- The operations of `lean_uint16_to_uint32`. -/
def «cands_lean_uint16_to_uint32» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .uint16__lean_uint16_to_uint32⟩]

/-- The operations of `lean_uint16_to_uint64`. -/
def «cands_lean_uint16_to_uint64» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_nat__lean_uint16_to_uint64⟩, ⟨_, _, .inlined .uint53__lean_uint16_to_uint64⟩]

/-- The operations of `lean_uint16_to_uint8`. -/
def «cands_lean_uint16_to_uint8» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint16__lean_uint16_to_uint8⟩]

/-- The operations of `lean_uint16_xor`. -/
def «cands_lean_uint16_xor» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint16__lean_uint16_xor⟩]

/-- The operations of `lean_uint32_add`. -/
def «cands_lean_uint32_add» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint32__lean_uint32_add⟩]

/-- The operations of `lean_uint32_complement`. -/
def «cands_lean_uint32_complement» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint32__lean_uint32_complement⟩]

/-- The operations of `lean_uint32_dec_eq`. -/
def «cands_lean_uint32_dec_eq» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .uint32__lean_uint32_dec_eq⟩]

/-- The operations of `lean_uint32_dec_le`. -/
def «cands_lean_uint32_dec_le» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .uint32__lean_uint32_dec_le⟩]

/-- The operations of `lean_uint32_dec_lt`. -/
def «cands_lean_uint32_dec_lt» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .uint32__lean_uint32_dec_lt⟩]

/-- The operations of `lean_uint32_div`. -/
def «cands_lean_uint32_div» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint32__lean_uint32_div⟩]

/-- The operations of `lean_uint32_land`. -/
def «cands_lean_uint32_land» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint32__lean_uint32_land⟩]

/-- The operations of `lean_uint32_log2`. -/
def «cands_lean_uint32_log2» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint32__lean_uint32_log2⟩]

/-- The operations of `lean_uint32_lor`. -/
def «cands_lean_uint32_lor» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint32__lean_uint32_lor⟩]

/-- The operations of `lean_uint32_mod`. -/
def «cands_lean_uint32_mod» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint32__lean_uint32_mod⟩]

/-- The operations of `lean_uint32_mul`. -/
def «cands_lean_uint32_mul» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint32__lean_uint32_mul⟩]

/-- The operations of `lean_uint32_neg`. -/
def «cands_lean_uint32_neg» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint32__lean_uint32_neg⟩]

/-- The operations of `lean_uint32_of_nat__Char_ofNatAux`. -/
def «cands_lean_uint32_of_nat__Char_ofNatAux» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_uint32_of_nat__Char_ofNatAux⟩, ⟨_, _, .imported .uint53__lean_uint32_of_nat__Char_ofNatAux⟩]

/-- The operations of `lean_uint32_of_nat__UInt32_ofNat`. -/
def «cands_lean_uint32_of_nat__UInt32_ofNat» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_uint32_of_nat__UInt32_ofNat⟩, ⟨_, _, .imported .uint53__lean_uint32_of_nat__UInt32_ofNat⟩]

/-- The operations of `lean_uint32_of_nat__UInt32_ofNatLT`. -/
def «cands_lean_uint32_of_nat__UInt32_ofNatLT» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_uint32_of_nat__UInt32_ofNatLT⟩, ⟨_, _, .imported .uint53__lean_uint32_of_nat__UInt32_ofNatLT⟩]

/-- The operations of `lean_uint32_of_nat_mk`. -/
def «cands_lean_uint32_of_nat_mk» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bitvec32__lean_uint32_of_nat_mk⟩]

/-- The operations of `lean_uint32_shift_left`. -/
def «cands_lean_uint32_shift_left» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint32__lean_uint32_shift_left⟩]

/-- The operations of `lean_uint32_shift_right`. -/
def «cands_lean_uint32_shift_right» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint32__lean_uint32_shift_right⟩]

/-- The operations of `lean_uint32_sub`. -/
def «cands_lean_uint32_sub» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint32__lean_uint32_sub⟩]

/-- The operations of `lean_uint32_to_float`. -/
def «cands_lean_uint32_to_float» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .uint32__lean_uint32_to_float⟩]

/-- The operations of `lean_uint32_to_float32`. -/
def «cands_lean_uint32_to_float32» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .uint32__lean_uint32_to_float32⟩]

/-- The operations of `lean_uint32_to_nat__UInt32_toBitVec`. -/
def «cands_lean_uint32_to_nat__UInt32_toBitVec» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .uint32__lean_uint32_to_nat__UInt32_toBitVec⟩]

/-- The operations of `lean_uint32_to_nat__UInt32_toNat`. -/
def «cands_lean_uint32_to_nat__UInt32_toNat» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_nat__lean_uint32_to_nat__UInt32_toNat⟩, ⟨_, _, .inlined .uint53__lean_uint32_to_nat__UInt32_toNat⟩]

/-- The operations of `lean_uint32_to_uint16`. -/
def «cands_lean_uint32_to_uint16» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint32__lean_uint32_to_uint16⟩]

/-- The operations of `lean_uint32_to_uint64`. -/
def «cands_lean_uint32_to_uint64» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_nat__lean_uint32_to_uint64⟩, ⟨_, _, .inlined .uint53__lean_uint32_to_uint64⟩]

/-- The operations of `lean_uint32_to_uint8`. -/
def «cands_lean_uint32_to_uint8» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint32__lean_uint32_to_uint8⟩]

/-- The operations of `lean_uint32_xor`. -/
def «cands_lean_uint32_xor» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint32__lean_uint32_xor⟩]

/-- The operations of `lean_uint64_add`. -/
def «cands_lean_uint64_add» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_uint64_add⟩, ⟨_, _, .imported .uint53__lean_uint64_add⟩]

/-- The operations of `lean_uint64_complement`. -/
def «cands_lean_uint64_complement» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_uint64_complement⟩, ⟨_, _, .imported .uint53__lean_uint64_complement⟩]

/-- The operations of `lean_uint64_dec_eq`. -/
def «cands_lean_uint64_dec_eq» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_nat__lean_uint64_dec_eq⟩, ⟨_, _, .inlined .uint53__lean_uint64_dec_eq⟩]

/-- The operations of `lean_uint64_dec_le`. -/
def «cands_lean_uint64_dec_le» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_nat__lean_uint64_dec_le⟩, ⟨_, _, .inlined .uint53__lean_uint64_dec_le⟩]

/-- The operations of `lean_uint64_dec_lt`. -/
def «cands_lean_uint64_dec_lt» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_nat__lean_uint64_dec_lt⟩, ⟨_, _, .inlined .uint53__lean_uint64_dec_lt⟩]

/-- The operations of `lean_uint64_div`. -/
def «cands_lean_uint64_div» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_uint64_div⟩, ⟨_, _, .imported .uint53__lean_uint64_div⟩]

/-- The operations of `lean_uint64_land`. -/
def «cands_lean_uint64_land» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_uint64_land⟩, ⟨_, _, .imported .uint53__lean_uint64_land⟩]

/-- The operations of `lean_uint64_log2`. -/
def «cands_lean_uint64_log2» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_uint64_log2⟩, ⟨_, _, .imported .uint53__lean_uint64_log2⟩]

/-- The operations of `lean_uint64_lor`. -/
def «cands_lean_uint64_lor» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_uint64_lor⟩, ⟨_, _, .imported .uint53__lean_uint64_lor⟩]

/-- The operations of `lean_uint64_mod`. -/
def «cands_lean_uint64_mod» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_uint64_mod⟩, ⟨_, _, .imported .uint53__lean_uint64_mod⟩]

/-- The operations of `lean_uint64_mul`. -/
def «cands_lean_uint64_mul» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_uint64_mul⟩, ⟨_, _, .imported .uint53__lean_uint64_mul⟩]

/-- The operations of `lean_uint64_neg`. -/
def «cands_lean_uint64_neg» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_uint64_neg⟩, ⟨_, _, .imported .uint53__lean_uint64_neg⟩]

/-- The operations of `lean_uint64_of_nat__UInt64_ofNat`. -/
def «cands_lean_uint64_of_nat__UInt64_ofNat» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_uint64_of_nat__UInt64_ofNat⟩, ⟨_, _, .imported .bigint_nat__uint53__lean_uint64_of_nat__UInt64_ofNat⟩, ⟨_, _, .imported .uint53__bigint_nat__lean_uint64_of_nat__UInt64_ofNat⟩, ⟨_, _, .imported .uint53__lean_uint64_of_nat__UInt64_ofNat⟩]

/-- The operations of `lean_uint64_of_nat__UInt64_ofNatLT`. -/
def «cands_lean_uint64_of_nat__UInt64_ofNatLT» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_uint64_of_nat__UInt64_ofNatLT⟩, ⟨_, _, .imported .bigint_nat__uint53__lean_uint64_of_nat__UInt64_ofNatLT⟩, ⟨_, _, .imported .uint53__bigint_nat__lean_uint64_of_nat__UInt64_ofNatLT⟩, ⟨_, _, .imported .uint53__lean_uint64_of_nat__UInt64_ofNatLT⟩]

/-- The operations of `lean_uint64_of_nat_mk`. -/
def «cands_lean_uint64_of_nat_mk» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_bitvec64__bigint_nat__lean_uint64_of_nat_mk⟩, ⟨_, _, .imported .bigint_bitvec64__uint53__lean_uint64_of_nat_mk⟩, ⟨_, _, .inlined .int53_bitvec64__bigint_nat__lean_uint64_of_nat_mk⟩, ⟨_, _, .inlined .int53_bitvec64__uint53__lean_uint64_of_nat_mk⟩]

/-- The operations of `lean_uint64_shift_left`. -/
def «cands_lean_uint64_shift_left» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_uint64_shift_left⟩, ⟨_, _, .imported .uint53__lean_uint64_shift_left⟩]

/-- The operations of `lean_uint64_shift_right`. -/
def «cands_lean_uint64_shift_right» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_uint64_shift_right⟩, ⟨_, _, .imported .uint53__lean_uint64_shift_right⟩]

/-- The operations of `lean_uint64_sub`. -/
def «cands_lean_uint64_sub» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_uint64_sub⟩, ⟨_, _, .imported .uint53__lean_uint64_sub⟩]

/-- The operations of `lean_uint64_to_float`. -/
def «cands_lean_uint64_to_float» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_nat__lean_uint64_to_float⟩, ⟨_, _, .inlined .uint53__lean_uint64_to_float⟩]

/-- The operations of `lean_uint64_to_float32`. -/
def «cands_lean_uint64_to_float32» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_nat__lean_uint64_to_float32⟩, ⟨_, _, .inlined .uint53__lean_uint64_to_float32⟩]

/-- The operations of `lean_uint64_to_nat__UInt64_toBitVec`. -/
def «cands_lean_uint64_to_nat__UInt64_toBitVec» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_nat__bigint_bitvec64__lean_uint64_to_nat__UInt64_toBitVec⟩, ⟨_, _, .imported .bigint_nat__int53_bitvec64__lean_uint64_to_nat__UInt64_toBitVec⟩, ⟨_, _, .inlined .uint53__bigint_bitvec64__lean_uint64_to_nat__UInt64_toBitVec⟩, ⟨_, _, .inlined .uint53__int53_bitvec64__lean_uint64_to_nat__UInt64_toBitVec⟩]

/-- The operations of `lean_uint64_to_nat__UInt64_toNat`. -/
def «cands_lean_uint64_to_nat__UInt64_toNat» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_nat__lean_uint64_to_nat__UInt64_toNat⟩, ⟨_, _, .imported .bigint_nat__uint53__lean_uint64_to_nat__UInt64_toNat⟩, ⟨_, _, .inlined .uint53__bigint_nat__lean_uint64_to_nat__UInt64_toNat⟩, ⟨_, _, .inlined .uint53__lean_uint64_to_nat__UInt64_toNat⟩]

/-- The operations of `lean_uint64_to_uint16`. -/
def «cands_lean_uint64_to_uint16» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_uint64_to_uint16⟩, ⟨_, _, .imported .uint53__lean_uint64_to_uint16⟩]

/-- The operations of `lean_uint64_to_uint32`. -/
def «cands_lean_uint64_to_uint32» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_uint64_to_uint32⟩, ⟨_, _, .imported .uint53__lean_uint64_to_uint32⟩]

/-- The operations of `lean_uint64_to_uint8`. -/
def «cands_lean_uint64_to_uint8» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_uint64_to_uint8⟩, ⟨_, _, .imported .uint53__lean_uint64_to_uint8⟩]

/-- The operations of `lean_uint64_xor`. -/
def «cands_lean_uint64_xor» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_uint64_xor⟩, ⟨_, _, .imported .uint53__lean_uint64_xor⟩]

/-- The operations of `lean_uint8_add`. -/
def «cands_lean_uint8_add» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint8__lean_uint8_add⟩]

/-- The operations of `lean_uint8_complement`. -/
def «cands_lean_uint8_complement» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint8__lean_uint8_complement⟩]

/-- The operations of `lean_uint8_dec_eq`. -/
def «cands_lean_uint8_dec_eq» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .uint8__lean_uint8_dec_eq⟩]

/-- The operations of `lean_uint8_dec_le`. -/
def «cands_lean_uint8_dec_le» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .uint8__lean_uint8_dec_le⟩]

/-- The operations of `lean_uint8_dec_lt`. -/
def «cands_lean_uint8_dec_lt» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .uint8__lean_uint8_dec_lt⟩]

/-- The operations of `lean_uint8_div`. -/
def «cands_lean_uint8_div» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint8__lean_uint8_div⟩]

/-- The operations of `lean_uint8_land`. -/
def «cands_lean_uint8_land» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint8__lean_uint8_land⟩]

/-- The operations of `lean_uint8_log2`. -/
def «cands_lean_uint8_log2» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint8__lean_uint8_log2⟩]

/-- The operations of `lean_uint8_lor`. -/
def «cands_lean_uint8_lor» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint8__lean_uint8_lor⟩]

/-- The operations of `lean_uint8_mod`. -/
def «cands_lean_uint8_mod» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint8__lean_uint8_mod⟩]

/-- The operations of `lean_uint8_mul`. -/
def «cands_lean_uint8_mul» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint8__lean_uint8_mul⟩]

/-- The operations of `lean_uint8_neg`. -/
def «cands_lean_uint8_neg» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint8__lean_uint8_neg⟩]

/-- The operations of `lean_uint8_of_nat__UInt8_ofNat`. -/
def «cands_lean_uint8_of_nat__UInt8_ofNat» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_uint8_of_nat__UInt8_ofNat⟩, ⟨_, _, .imported .uint53__lean_uint8_of_nat__UInt8_ofNat⟩]

/-- The operations of `lean_uint8_of_nat__UInt8_ofNatLT`. -/
def «cands_lean_uint8_of_nat__UInt8_ofNatLT» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .bigint_nat__lean_uint8_of_nat__UInt8_ofNatLT⟩, ⟨_, _, .imported .uint53__lean_uint8_of_nat__UInt8_ofNatLT⟩]

/-- The operations of `lean_uint8_of_nat_mk`. -/
def «cands_lean_uint8_of_nat_mk» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bitvec8__lean_uint8_of_nat_mk⟩]

/-- The operations of `lean_uint8_shift_left`. -/
def «cands_lean_uint8_shift_left» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint8__lean_uint8_shift_left⟩]

/-- The operations of `lean_uint8_shift_right`. -/
def «cands_lean_uint8_shift_right» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint8__lean_uint8_shift_right⟩]

/-- The operations of `lean_uint8_sub`. -/
def «cands_lean_uint8_sub» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint8__lean_uint8_sub⟩]

/-- The operations of `lean_uint8_to_float`. -/
def «cands_lean_uint8_to_float» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .uint8__lean_uint8_to_float⟩]

/-- The operations of `lean_uint8_to_float32`. -/
def «cands_lean_uint8_to_float32» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .uint8__lean_uint8_to_float32⟩]

/-- The operations of `lean_uint8_to_nat__UInt8_toBitVec`. -/
def «cands_lean_uint8_to_nat__UInt8_toBitVec» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .uint8__lean_uint8_to_nat__UInt8_toBitVec⟩]

/-- The operations of `lean_uint8_to_nat__UInt8_toNat`. -/
def «cands_lean_uint8_to_nat__UInt8_toNat» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_nat__lean_uint8_to_nat__UInt8_toNat⟩, ⟨_, _, .inlined .uint53__lean_uint8_to_nat__UInt8_toNat⟩]

/-- The operations of `lean_uint8_to_uint16`. -/
def «cands_lean_uint8_to_uint16» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .uint8__lean_uint8_to_uint16⟩]

/-- The operations of `lean_uint8_to_uint32`. -/
def «cands_lean_uint8_to_uint32» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .uint8__lean_uint8_to_uint32⟩]

/-- The operations of `lean_uint8_to_uint64`. -/
def «cands_lean_uint8_to_uint64» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .inlined .bigint_nat__lean_uint8_to_uint64⟩, ⟨_, _, .inlined .uint53__lean_uint8_to_uint64⟩]

/-- The operations of `lean_uint8_xor`. -/
def «cands_lean_uint8_xor» : List (Σ σs' τ', JsOp σs' τ') :=
  [⟨_, _, .imported .uint8__lean_uint8_xor⟩]

/-- The operation of the extern `name` at the signature `σs → τ`, if there is one. -/
def lookup (name : String) (σs : List JsTy) (τ : JsTy) : Option (JsOp σs τ) :=
  firstOf σs τ (match name with
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
    | "lean_float32_add" => «cands_lean_float32_add»
    | "lean_float32_beq" => «cands_lean_float32_beq»
    | "lean_float32_decLe__Float32_decLe" => «cands_lean_float32_decLe__Float32_decLe»
    | "lean_float32_decLe__Float32_le" => «cands_lean_float32_decLe__Float32_le»
    | "lean_float32_decLt__Float32_decLt" => «cands_lean_float32_decLt__Float32_decLt»
    | "lean_float32_decLt__Float32_lt" => «cands_lean_float32_decLt__Float32_lt»
    | "lean_float32_div" => «cands_lean_float32_div»
    | "lean_float32_isfinite" => «cands_lean_float32_isfinite»
    | "lean_float32_isinf" => «cands_lean_float32_isinf»
    | "lean_float32_isnan" => «cands_lean_float32_isnan»
    | "lean_float32_mul" => «cands_lean_float32_mul»
    | "lean_float32_negate" => «cands_lean_float32_negate»
    | "lean_float32_of_bits__Float32_ofModel" => «cands_lean_float32_of_bits__Float32_ofModel»
    | "lean_float32_sub" => «cands_lean_float32_sub»
    | "lean_float32_to_bits__Float32_toModel" => «cands_lean_float32_to_bits__Float32_toModel»
    | "lean_float32_to_float" => «cands_lean_float32_to_float»
    | "lean_float_add" => «cands_lean_float_add»
    | "lean_float_beq" => «cands_lean_float_beq»
    | "lean_float_decLe__Float_decLe" => «cands_lean_float_decLe__Float_decLe»
    | "lean_float_decLe__Float_le" => «cands_lean_float_decLe__Float_le»
    | "lean_float_decLt__Float_decLt" => «cands_lean_float_decLt__Float_decLt»
    | "lean_float_decLt__Float_lt" => «cands_lean_float_decLt__Float_lt»
    | "lean_float_div" => «cands_lean_float_div»
    | "lean_float_isfinite" => «cands_lean_float_isfinite»
    | "lean_float_isinf" => «cands_lean_float_isinf»
    | "lean_float_isnan" => «cands_lean_float_isnan»
    | "lean_float_mul" => «cands_lean_float_mul»
    | "lean_float_negate" => «cands_lean_float_negate»
    | "lean_float_of_bits__Float_ofModel" => «cands_lean_float_of_bits__Float_ofModel»
    | "lean_float_sub" => «cands_lean_float_sub»
    | "lean_float_to_bits__Float_toModel" => «cands_lean_float_to_bits__Float_toModel»
    | "lean_float_to_float32" => «cands_lean_float_to_float32»
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
    | "lean_strict_and" => «cands_lean_strict_and»
    | "lean_strict_or" => «cands_lean_strict_or»
    | "lean_string_append__String_Internal_append" => «cands_lean_string_append__String_Internal_append»
    | "lean_string_append__String_append" => «cands_lean_string_append__String_append»
    | "lean_string_compare" => «cands_lean_string_compare»
    | "lean_string_data__String_data" => «cands_lean_string_data__String_data»
    | "lean_string_data__String_toList" => «cands_lean_string_data__String_toList»
    | "lean_string_dec_eq" => «cands_lean_string_dec_eq»
    | "lean_string_dec_lt" => «cands_lean_string_dec_lt»
    | "lean_string_hash" => «cands_lean_string_hash»
    | "lean_string_isempty" => «cands_lean_string_isempty»
    | "lean_string_length__String_Internal_length" => «cands_lean_string_length__String_Internal_length»
    | "lean_string_length__String_length" => «cands_lean_string_length__String_length»
    | "lean_string_memcmp" => «cands_lean_string_memcmp»
    | "lean_string_mk__String_mk" => «cands_lean_string_mk__String_mk»
    | "lean_string_mk__String_ofList" => «cands_lean_string_mk__String_ofList»
    | "lean_string_push" => «cands_lean_string_push»
    | "lean_string_pushn" => «cands_lean_string_pushn»
    | "lean_string_utf8_at_end__String_Internal_atEnd" => «cands_lean_string_utf8_at_end__String_Internal_atEnd»
    | "lean_string_utf8_at_end__String_Pos_Raw_atEnd" => «cands_lean_string_utf8_at_end__String_Pos_Raw_atEnd»
    | "lean_string_utf8_at_end__String_atEnd" => «cands_lean_string_utf8_at_end__String_atEnd»
    | "lean_string_utf8_byte_size" => «cands_lean_string_utf8_byte_size»
    | "lean_string_utf8_extract__String_Internal_extract" => «cands_lean_string_utf8_extract__String_Internal_extract»
    | "lean_string_utf8_extract__String_Pos_Raw_extract" => «cands_lean_string_utf8_extract__String_Pos_Raw_extract»
    | "lean_string_utf8_get__String_Internal_get" => «cands_lean_string_utf8_get__String_Internal_get»
    | "lean_string_utf8_get__String_Pos_Raw_get" => «cands_lean_string_utf8_get__String_Pos_Raw_get»
    | "lean_string_utf8_get__String_get" => «cands_lean_string_utf8_get__String_get»
    | "lean_string_utf8_next__String_Internal_next" => «cands_lean_string_utf8_next__String_Internal_next»
    | "lean_string_utf8_next__String_Pos_Raw_next" => «cands_lean_string_utf8_next__String_Pos_Raw_next»
    | "lean_string_utf8_next__String_next" => «cands_lean_string_utf8_next__String_next»
    | "lean_string_utf8_set__String_Pos_Raw_set" => «cands_lean_string_utf8_set__String_Pos_Raw_set»
    | "lean_string_utf8_set__String_Pos_set" => «cands_lean_string_utf8_set__String_Pos_set»
    | "lean_string_utf8_set__String_set" => «cands_lean_string_utf8_set__String_set»
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
    | _ => [])

end JsOp

end MoreJs

end
