module

public import JsTerm.Ops.Op

@[expose] public section

set_option autoImplicit false

/-!
# The operations of the externs of the array functions written in Lean

**Generated** by `scripts/gen_js_ops.py`; do not edit.

The candidates (`JsOp.Cand`) of every extern of the array functions written in Lean (`ArrayStdExtern`: `lean_array_append`, `lean_array_map`, …, `lean_list_append`; listed by hand in `scripts/js_ops_array_std.py`): its
operations at their signatures, for the lookup (`JsOp.lookup`, `JsTerm.Ops.Lookup`).
-/

namespace MoreJs

namespace JsOp

/-- The layout of argument `i` among the types `σs`, when it is an array. -/
def layoutAt? (σs : List JsTy) (i : Nat) : Option (Σ a e, JsArrayLayout a e) :=
  match σs[i]? with
  | some t => match JsArrayLayout.of? t with
    | some ⟨e, l⟩ => some ⟨t, e, l⟩
    | none => none
  | none => none

/-- The operations of `lean_array_all`. -/
def «cands_lean_array_all» (σs : List JsTy) (_ : JsTy) : List Cand :=
  match layoutAt? σs 0 with
  | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.bigint_nat__lean_array_all l)⟩, ⟨_, _, _, _, .imported (.uint53__lean_array_all l)⟩]
  | none => []

/-- The operations of `lean_array_any`. -/
def «cands_lean_array_any» (σs : List JsTy) (_ : JsTy) : List Cand :=
  match layoutAt? σs 0 with
  | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.bigint_nat__lean_array_any l)⟩, ⟨_, _, _, _, .imported (.uint53__lean_array_any l)⟩]
  | none => []

/-- The operations of `lean_array_append`. -/
def «cands_lean_array_append» (σs : List JsTy) (_ : JsTy) : List Cand :=
  match layoutAt? σs 0 with
  | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.array__lean_array_append_immutable l)⟩]
  | none => []

/-- The operations of `lean_array_back_opt`. -/
def «cands_lean_array_back_opt» (σs : List JsTy) (_ : JsTy) : List Cand :=
  match layoutAt? σs 0 with
  | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.array__lean_array_back_opt l)⟩]
  | none => []

/-- The operations of `lean_array_contains`. -/
def «cands_lean_array_contains» (σs : List JsTy) (_ : JsTy) : List Cand :=
  match layoutAt? σs 1 with
  | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.array__lean_array_contains l)⟩]
  | none => []

/-- The operations of `lean_array_count_p`. -/
def «cands_lean_array_count_p» (σs : List JsTy) (_ : JsTy) : List Cand :=
  match layoutAt? σs 1 with
  | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.bigint_nat__lean_array_count_p l)⟩, ⟨_, _, _, _, .imported (.uint53__lean_array_count_p l)⟩]
  | none => []

/-- The operations of `lean_array_erase_idx`. -/
def «cands_lean_array_erase_idx» (σs : List JsTy) (_ : JsTy) : List Cand :=
  match layoutAt? σs 0 with
  | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.bigint_nat__lean_array_erase_idx l)⟩, ⟨_, _, _, _, .imported (.uint53__lean_array_erase_idx l)⟩]
  | none => []

/-- The operations of `lean_array_erase_idx_if_in_bounds`. -/
def «cands_lean_array_erase_idx_if_in_bounds» (σs : List JsTy) (_ : JsTy) : List Cand :=
  match layoutAt? σs 0 with
  | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.bigint_nat__lean_array_erase_idx_if_in_bounds l)⟩, ⟨_, _, _, _, .imported (.uint53__lean_array_erase_idx_if_in_bounds l)⟩]
  | none => []

/-- The operations of `lean_array_extract`. -/
def «cands_lean_array_extract» (σs : List JsTy) (_ : JsTy) : List Cand :=
  match layoutAt? σs 0 with
  | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.bigint_nat__lean_array_extract l)⟩, ⟨_, _, _, _, .imported (.uint53__lean_array_extract l)⟩]
  | none => []

/-- The operations of `lean_array_filter`. -/
def «cands_lean_array_filter» (σs : List JsTy) (_ : JsTy) : List Cand :=
  match layoutAt? σs 1 with
  | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.bigint_nat__lean_array_filter l)⟩, ⟨_, _, _, _, .imported (.uint53__lean_array_filter l)⟩]
  | none => []

/-- The operations of `lean_array_find_idx_opt`. -/
def «cands_lean_array_find_idx_opt» (σs : List JsTy) (_ : JsTy) : List Cand :=
  match layoutAt? σs 1 with
  | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.bigint_nat__lean_array_find_idx_opt l)⟩, ⟨_, _, _, _, .imported (.uint53__lean_array_find_idx_opt l)⟩]
  | none => []

/-- The operations of `lean_array_find_opt`. -/
def «cands_lean_array_find_opt» (σs : List JsTy) (_ : JsTy) : List Cand :=
  match layoutAt? σs 1 with
  | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.array__lean_array_find_opt l)⟩]
  | none => []

/-- The operations of `lean_array_flat_map`. -/
def «cands_lean_array_flat_map» (σs : List JsTy) (τ : JsTy) : List Cand :=
  match layoutAt? σs 1, layoutOf? [τ] with
  | some ⟨_, _, l⟩, some ⟨_, _, .generic β⟩ => [⟨_, _, _, _, .imported (.array__lean_array_flat_map l β)⟩]
  | some ⟨_, _, l⟩, some ⟨_, _, .typed t⟩ => [⟨_, _, _, _, .imported (.typedArray__lean_array_flat_map l t)⟩]
  | _, _ => []

/-- The operations of `lean_array_flatten`. -/
def «cands_lean_array_flatten» (_ : List JsTy) (τ : JsTy) : List Cand :=
  match layoutOf? [τ] with
  | some ⟨_, _, .generic β⟩ => [⟨_, _, _, _, .imported (.array__lean_array_flatten β)⟩]
  | some ⟨_, _, .typed t⟩ => [⟨_, _, _, _, .imported (.typedArray__lean_array_flatten t)⟩]
  | none => []

/-- The operations of `lean_array_foldr`. -/
def «cands_lean_array_foldr» (σs : List JsTy) (τ : JsTy) : List Cand :=
  match layoutAt? σs 2 with
  | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.bigint_nat__lean_array_foldr l τ)⟩, ⟨_, _, _, _, .imported (.uint53__lean_array_foldr l τ)⟩]
  | none => []

/-- The operations of `lean_array_idx_of_opt`. -/
def «cands_lean_array_idx_of_opt» (σs : List JsTy) (_ : JsTy) : List Cand :=
  match layoutAt? σs 1 with
  | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.bigint_nat__lean_array_idx_of_opt l)⟩, ⟨_, _, _, _, .imported (.uint53__lean_array_idx_of_opt l)⟩]
  | none => []

/-- The operations of `lean_array_insert_idx`. -/
def «cands_lean_array_insert_idx» (σs : List JsTy) (_ : JsTy) : List Cand :=
  match layoutAt? σs 0 with
  | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.bigint_nat__lean_array_insert_idx l)⟩, ⟨_, _, _, _, .imported (.uint53__lean_array_insert_idx l)⟩]
  | none => []

/-- The operations of `lean_array_insert_idx_if_in_bounds`. -/
def «cands_lean_array_insert_idx_if_in_bounds» (σs : List JsTy) (_ : JsTy) : List Cand :=
  match layoutAt? σs 0 with
  | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.bigint_nat__lean_array_insert_idx_if_in_bounds l)⟩, ⟨_, _, _, _, .imported (.uint53__lean_array_insert_idx_if_in_bounds l)⟩]
  | none => []

/-- The operations of `lean_array_map`. -/
def «cands_lean_array_map» (σs : List JsTy) (τ : JsTy) : List Cand :=
  match layoutAt? σs 1, layoutOf? [τ] with
  | some ⟨_, _, l⟩, some ⟨_, _, .generic β⟩ => [⟨_, _, _, _, .imported (.array__lean_array_map l β)⟩]
  | some ⟨_, _, l⟩, some ⟨_, _, .typed t⟩ => [⟨_, _, _, _, .imported (.typedArray__lean_array_map l t)⟩]
  | _, _ => []

/-- The operations of `lean_array_qsort`. -/
def «cands_lean_array_qsort» (σs : List JsTy) (_ : JsTy) : List Cand :=
  match layoutAt? σs 0 with
  | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.bigint_nat__lean_array_qsort l)⟩, ⟨_, _, _, _, .imported (.uint53__lean_array_qsort l)⟩]
  | none => []

/-- The operations of `lean_array_reverse`. -/
def «cands_lean_array_reverse» (σs : List JsTy) (_ : JsTy) : List Cand :=
  match layoutAt? σs 0 with
  | some ⟨_, _, l⟩ => [⟨_, _, _, _, .imported (.array__lean_array_reverse l)⟩]
  | none => []

/-- The operations of `lean_array_zip`. -/
def «cands_lean_array_zip» (σs : List JsTy) (_ : JsTy) : List Cand :=
  match layoutAt? σs 0, layoutAt? σs 1 with
  | some ⟨_, _, l₁⟩, some ⟨_, _, l₂⟩ => [⟨_, _, _, _, .imported (.array__lean_array_zip l₁ l₂)⟩]
  | _, _ => []

/-- The operations of `lean_array_zip_with`. -/
def «cands_lean_array_zip_with» (σs : List JsTy) (τ : JsTy) : List Cand :=
  match layoutAt? σs 1, layoutAt? σs 2, layoutOf? [τ] with
  | some ⟨_, _, l₁⟩, some ⟨_, _, l₂⟩, some ⟨_, _, .generic γ⟩ => [⟨_, _, _, _, .imported (.array__lean_array_zip_with l₁ l₂ γ)⟩]
  | some ⟨_, _, l₁⟩, some ⟨_, _, l₂⟩, some ⟨_, _, .typed t⟩ => [⟨_, _, _, _, .imported (.typedArray__lean_array_zip_with l₁ l₂ t)⟩]
  | _, _, _ => []

/-- The operations of `lean_list_append`. -/
def «cands_lean_list_append» (_ : List JsTy) (τ : JsTy) : List Cand :=
  match τ with
  | .list α => [⟨_, _, _, _, .imported (.list__lean_list_append α)⟩]
  | .obj .consList [α] => [⟨_, _, _, _, .imported (.consList__lean_list_append α)⟩]
  | _ => []

/-- The candidates of the extern `name`, when it is one of the array functions written in Lean. -/
def candsArrayStd? (name : String) (σs : List JsTy) (τ : JsTy) : Option (List Cand) :=
  match name with
  | "lean_array_all" => some («cands_lean_array_all» σs τ)
  | "lean_array_any" => some («cands_lean_array_any» σs τ)
  | "lean_array_append" => some («cands_lean_array_append» σs τ)
  | "lean_array_back_opt" => some («cands_lean_array_back_opt» σs τ)
  | "lean_array_contains" => some («cands_lean_array_contains» σs τ)
  | "lean_array_count_p" => some («cands_lean_array_count_p» σs τ)
  | "lean_array_erase_idx" => some («cands_lean_array_erase_idx» σs τ)
  | "lean_array_erase_idx_if_in_bounds" => some («cands_lean_array_erase_idx_if_in_bounds» σs τ)
  | "lean_array_extract" => some («cands_lean_array_extract» σs τ)
  | "lean_array_filter" => some («cands_lean_array_filter» σs τ)
  | "lean_array_find_idx_opt" => some («cands_lean_array_find_idx_opt» σs τ)
  | "lean_array_find_opt" => some («cands_lean_array_find_opt» σs τ)
  | "lean_array_flat_map" => some («cands_lean_array_flat_map» σs τ)
  | "lean_array_flatten" => some («cands_lean_array_flatten» σs τ)
  | "lean_array_foldr" => some («cands_lean_array_foldr» σs τ)
  | "lean_array_idx_of_opt" => some («cands_lean_array_idx_of_opt» σs τ)
  | "lean_array_insert_idx" => some («cands_lean_array_insert_idx» σs τ)
  | "lean_array_insert_idx_if_in_bounds" => some («cands_lean_array_insert_idx_if_in_bounds» σs τ)
  | "lean_array_map" => some («cands_lean_array_map» σs τ)
  | "lean_array_qsort" => some («cands_lean_array_qsort» σs τ)
  | "lean_array_reverse" => some («cands_lean_array_reverse» σs τ)
  | "lean_array_zip" => some («cands_lean_array_zip» σs τ)
  | "lean_array_zip_with" => some («cands_lean_array_zip_with» σs τ)
  | "lean_list_append" => some («cands_lean_list_append» σs τ)
  | _ => none

end JsOp

end MoreJs

end
