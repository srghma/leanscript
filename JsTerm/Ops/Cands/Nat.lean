module

public import JsTerm.Ops.Op

@[expose] public section

set_option autoImplicit false

/-!
# The operations of the externs of `Nat` and `Int`

**Generated** by `scripts/gen_js_ops.py`; do not edit.

The candidates (`JsOp.Cand`) of every extern of `Nat` and `Int` (`lean_nat_*`, `lean_int_*`): its
operations at their signatures, for the lookup (`JsOp.lookup`, `JsTerm.Ops.Lookup`).
-/

namespace MoreJs

namespace JsOp

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

/-- The operations of `lean_int_pow`. -/
def «cands_lean_int_pow» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_int__bigint_nat__lean_int_pow⟩, ⟨_, _, _, _, .inlined .bigint_int__uint53__lean_int_pow⟩, ⟨_, _, _, _, .imported .int53__bigint_nat__lean_int_pow⟩, ⟨_, _, _, _, .imported .int53__uint53__lean_int_pow⟩]

/-- The operations of `lean_int_repr`. -/
def «cands_lean_int_repr» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_int__lean_int_repr⟩, ⟨_, _, _, _, .inlined .int53__lean_int_repr⟩]

/-- The operations of `lean_int_sub`. -/
def «cands_lean_int_sub» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_int__lean_int_sub⟩, ⟨_, _, _, _, .imported .int53__lean_int_sub⟩]

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
  [⟨_, _, _, _, .inlined .bigint_nat__lean_nat_pow⟩, ⟨_, _, _, _, .imported .uint53__lean_nat_pow⟩]

/-- The operations of `lean_nat_pred`. -/
def «cands_lean_nat_pred» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_nat_pred⟩, ⟨_, _, _, _, .imported .uint53__lean_nat_pred⟩]

/-- The operations of `lean_nat_repr`. -/
def «cands_lean_nat_repr» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_nat__lean_nat_repr⟩, ⟨_, _, _, _, .inlined .uint53__lean_nat_repr⟩]

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

/-- The candidates of the extern `name`, when it is one of `Nat` and `Int`. -/
def candsNat? (name : String) : Option (List Cand) :=
  match name with
  | "lean_int_add" => some «cands_lean_int_add»
  | "lean_int_dec_eq" => some «cands_lean_int_dec_eq»
  | "lean_int_dec_le" => some «cands_lean_int_dec_le»
  | "lean_int_dec_lt" => some «cands_lean_int_dec_lt»
  | "lean_int_dec_nonneg" => some «cands_lean_int_dec_nonneg»
  | "lean_int_div" => some «cands_lean_int_div»
  | "lean_int_div_exact" => some «cands_lean_int_div_exact»
  | "lean_int_ediv" => some «cands_lean_int_ediv»
  | "lean_int_emod" => some «cands_lean_int_emod»
  | "lean_int_mod" => some «cands_lean_int_mod»
  | "lean_int_mul" => some «cands_lean_int_mul»
  | "lean_int_neg" => some «cands_lean_int_neg»
  | "lean_int_neg_succ_of_nat" => some «cands_lean_int_neg_succ_of_nat»
  | "lean_int_pow" => some «cands_lean_int_pow»
  | "lean_int_repr" => some «cands_lean_int_repr»
  | "lean_int_sub" => some «cands_lean_int_sub»
  | "lean_nat_abs" => some «cands_lean_nat_abs»
  | "lean_nat_add" => some «cands_lean_nat_add»
  | "lean_nat_dec_eq__Nat_beq" => some «cands_lean_nat_dec_eq__Nat_beq»
  | "lean_nat_dec_eq__Nat_decEq" => some «cands_lean_nat_dec_eq__Nat_decEq»
  | "lean_nat_dec_le__Nat_ble" => some «cands_lean_nat_dec_le__Nat_ble»
  | "lean_nat_dec_le__Nat_decLe" => some «cands_lean_nat_dec_le__Nat_decLe»
  | "lean_nat_dec_lt" => some «cands_lean_nat_dec_lt»
  | "lean_nat_div" => some «cands_lean_nat_div»
  | "lean_nat_div_exact" => some «cands_lean_nat_div_exact»
  | "lean_nat_land" => some «cands_lean_nat_land»
  | "lean_nat_log2" => some «cands_lean_nat_log2»
  | "lean_nat_lor" => some «cands_lean_nat_lor»
  | "lean_nat_lxor" => some «cands_lean_nat_lxor»
  | "lean_nat_mod__Nat_mod" => some «cands_lean_nat_mod__Nat_mod»
  | "lean_nat_mod__Nat_modCore" => some «cands_lean_nat_mod__Nat_modCore»
  | "lean_nat_mul" => some «cands_lean_nat_mul»
  | "lean_nat_pow" => some «cands_lean_nat_pow»
  | "lean_nat_pred" => some «cands_lean_nat_pred»
  | "lean_nat_repr" => some «cands_lean_nat_repr»
  | "lean_nat_shiftl" => some «cands_lean_nat_shiftl»
  | "lean_nat_shiftr" => some «cands_lean_nat_shiftr»
  | "lean_nat_sub" => some «cands_lean_nat_sub»
  | "lean_nat_to_int" => some «cands_lean_nat_to_int»
  | _ => none

end JsOp

end MoreJs

end
