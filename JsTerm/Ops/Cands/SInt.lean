module

public import JsTerm.Ops.Op

@[expose] public section

set_option autoImplicit false

/-!
# The operations of the externs of the signed fixed-width integers

**Generated** by `scripts/gen_js_ops.py`; do not edit.

The candidates (`JsOp.Cand`) of every extern of the signed fixed-width integers (`lean_int8_*`, …, `lean_int64_*`, `lean_isize_*`): its
operations at their signatures, for the lookup (`JsOp.lookup`, `JsTerm.Ops.Lookup`).
-/

namespace MoreJs

namespace JsOp

/-- The operations of `lean_int16_abs`. -/
def «cands_lean_int16_abs» : List Cand :=
  [⟨_, _, _, _, .imported .int16__lean_int16_abs⟩]

/-- The operations of `lean_int16_add`. -/
def «cands_lean_int16_add» : List Cand :=
  [⟨_, _, _, _, .inlined .int16__lean_int16_add⟩]

/-- The operations of `lean_int16_complement`. -/
def «cands_lean_int16_complement» : List Cand :=
  [⟨_, _, _, _, .inlined .int16__lean_int16_complement⟩]

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
  [⟨_, _, _, _, .inlined .int16__lean_int16_div⟩]

/-- The operations of `lean_int16_land`. -/
def «cands_lean_int16_land» : List Cand :=
  [⟨_, _, _, _, .inlined .int16__lean_int16_land⟩]

/-- The operations of `lean_int16_lor`. -/
def «cands_lean_int16_lor» : List Cand :=
  [⟨_, _, _, _, .inlined .int16__lean_int16_lor⟩]

/-- The operations of `lean_int16_mod`. -/
def «cands_lean_int16_mod» : List Cand :=
  [⟨_, _, _, _, .imported .int16__lean_int16_mod⟩]

/-- The operations of `lean_int16_mul`. -/
def «cands_lean_int16_mul» : List Cand :=
  [⟨_, _, _, _, .inlined .int16__lean_int16_mul⟩]

/-- The operations of `lean_int16_neg`. -/
def «cands_lean_int16_neg» : List Cand :=
  [⟨_, _, _, _, .inlined .int16__lean_int16_neg⟩]

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
  [⟨_, _, _, _, .inlined .int16__lean_int16_sub⟩]

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
  [⟨_, _, _, _, .inlined .int16__lean_int16_xor⟩]

/-- The operations of `lean_int32_abs`. -/
def «cands_lean_int32_abs» : List Cand :=
  [⟨_, _, _, _, .imported .int32__lean_int32_abs⟩]

/-- The operations of `lean_int32_add`. -/
def «cands_lean_int32_add» : List Cand :=
  [⟨_, _, _, _, .inlined .int32__lean_int32_add⟩]

/-- The operations of `lean_int32_complement`. -/
def «cands_lean_int32_complement» : List Cand :=
  [⟨_, _, _, _, .inlined .int32__lean_int32_complement⟩]

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
  [⟨_, _, _, _, .inlined .int32__lean_int32_div⟩]

/-- The operations of `lean_int32_land`. -/
def «cands_lean_int32_land» : List Cand :=
  [⟨_, _, _, _, .inlined .int32__lean_int32_land⟩]

/-- The operations of `lean_int32_lor`. -/
def «cands_lean_int32_lor» : List Cand :=
  [⟨_, _, _, _, .inlined .int32__lean_int32_lor⟩]

/-- The operations of `lean_int32_mod`. -/
def «cands_lean_int32_mod» : List Cand :=
  [⟨_, _, _, _, .imported .int32__lean_int32_mod⟩]

/-- The operations of `lean_int32_mul`. -/
def «cands_lean_int32_mul» : List Cand :=
  [⟨_, _, _, _, .inlined .int32__lean_int32_mul⟩]

/-- The operations of `lean_int32_neg`. -/
def «cands_lean_int32_neg» : List Cand :=
  [⟨_, _, _, _, .inlined .int32__lean_int32_neg⟩]

/-- The operations of `lean_int32_of_int`. -/
def «cands_lean_int32_of_int» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_int32_of_int⟩, ⟨_, _, _, _, .imported .int53__lean_int32_of_int⟩]

/-- The operations of `lean_int32_of_nat`. -/
def «cands_lean_int32_of_nat» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_int32_of_nat⟩, ⟨_, _, _, _, .imported .uint53__lean_int32_of_nat⟩]

/-- The operations of `lean_int32_shift_left`. -/
def «cands_lean_int32_shift_left» : List Cand :=
  [⟨_, _, _, _, .inlined .int32__lean_int32_shift_left⟩]

/-- The operations of `lean_int32_shift_right`. -/
def «cands_lean_int32_shift_right» : List Cand :=
  [⟨_, _, _, _, .inlined .int32__lean_int32_shift_right⟩]

/-- The operations of `lean_int32_sub`. -/
def «cands_lean_int32_sub» : List Cand :=
  [⟨_, _, _, _, .inlined .int32__lean_int32_sub⟩]

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
  [⟨_, _, _, _, .inlined .int32__lean_int32_xor⟩]

/-- The operations of `lean_int64_abs`. -/
def «cands_lean_int64_abs» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_int64_abs⟩, ⟨_, _, _, _, .imported .int53__lean_int64_abs⟩]

/-- The operations of `lean_int64_add`. -/
def «cands_lean_int64_add» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_int__lean_int64_add⟩, ⟨_, _, _, _, .imported .int53__lean_int64_add⟩]

/-- The operations of `lean_int64_complement`. -/
def «cands_lean_int64_complement» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_int__lean_int64_complement⟩, ⟨_, _, _, _, .imported .int53__lean_int64_complement⟩]

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
  [⟨_, _, _, _, .inlined .bigint_int__lean_int64_land⟩, ⟨_, _, _, _, .imported .int53__lean_int64_land⟩]

/-- The operations of `lean_int64_lor`. -/
def «cands_lean_int64_lor» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_int__lean_int64_lor⟩, ⟨_, _, _, _, .imported .int53__lean_int64_lor⟩]

/-- The operations of `lean_int64_mod`. -/
def «cands_lean_int64_mod» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_int64_mod⟩, ⟨_, _, _, _, .imported .int53__lean_int64_mod⟩]

/-- The operations of `lean_int64_mul`. -/
def «cands_lean_int64_mul» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_int__lean_int64_mul⟩, ⟨_, _, _, _, .imported .int53__lean_int64_mul⟩]

/-- The operations of `lean_int64_neg`. -/
def «cands_lean_int64_neg» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_int__lean_int64_neg⟩, ⟨_, _, _, _, .inlined .int53__lean_int64_neg⟩]

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
  [⟨_, _, _, _, .inlined .bigint_int__lean_int64_sub⟩, ⟨_, _, _, _, .imported .int53__lean_int64_sub⟩]

/-- The operations of `lean_int64_to_float`. -/
def «cands_lean_int64_to_float» : List Cand :=
  [⟨_, _, _, _, .inlined .bigint_int__lean_int64_to_float⟩, ⟨_, _, _, _, .inlined .int53__lean_int64_to_float⟩]

/-- The operations of `lean_int64_to_float32`. -/
def «cands_lean_int64_to_float32» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_int__lean_int64_to_float32⟩, ⟨_, _, _, _, .inlined .int53__lean_int64_to_float32⟩]

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
  [⟨_, _, _, _, .inlined .bigint_int__lean_int64_xor⟩, ⟨_, _, _, _, .imported .int53__lean_int64_xor⟩]

/-- The operations of `lean_int8_abs`. -/
def «cands_lean_int8_abs» : List Cand :=
  [⟨_, _, _, _, .imported .int8__lean_int8_abs⟩]

/-- The operations of `lean_int8_add`. -/
def «cands_lean_int8_add» : List Cand :=
  [⟨_, _, _, _, .inlined .int8__lean_int8_add⟩]

/-- The operations of `lean_int8_complement`. -/
def «cands_lean_int8_complement» : List Cand :=
  [⟨_, _, _, _, .inlined .int8__lean_int8_complement⟩]

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
  [⟨_, _, _, _, .inlined .int8__lean_int8_div⟩]

/-- The operations of `lean_int8_land`. -/
def «cands_lean_int8_land» : List Cand :=
  [⟨_, _, _, _, .inlined .int8__lean_int8_land⟩]

/-- The operations of `lean_int8_lor`. -/
def «cands_lean_int8_lor» : List Cand :=
  [⟨_, _, _, _, .inlined .int8__lean_int8_lor⟩]

/-- The operations of `lean_int8_mod`. -/
def «cands_lean_int8_mod» : List Cand :=
  [⟨_, _, _, _, .imported .int8__lean_int8_mod⟩]

/-- The operations of `lean_int8_mul`. -/
def «cands_lean_int8_mul» : List Cand :=
  [⟨_, _, _, _, .inlined .int8__lean_int8_mul⟩]

/-- The operations of `lean_int8_neg`. -/
def «cands_lean_int8_neg» : List Cand :=
  [⟨_, _, _, _, .inlined .int8__lean_int8_neg⟩]

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
  [⟨_, _, _, _, .inlined .int8__lean_int8_sub⟩]

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
  [⟨_, _, _, _, .inlined .int8__lean_int8_xor⟩]

/-- The candidates of the extern `name`, when it is one of the signed fixed-width integers. -/
def candsSInt? (name : String) : Option (List Cand) :=
  match name with
  | "lean_int16_abs" => some «cands_lean_int16_abs»
  | "lean_int16_add" => some «cands_lean_int16_add»
  | "lean_int16_complement" => some «cands_lean_int16_complement»
  | "lean_int16_dec_eq" => some «cands_lean_int16_dec_eq»
  | "lean_int16_dec_le" => some «cands_lean_int16_dec_le»
  | "lean_int16_dec_lt" => some «cands_lean_int16_dec_lt»
  | "lean_int16_div" => some «cands_lean_int16_div»
  | "lean_int16_land" => some «cands_lean_int16_land»
  | "lean_int16_lor" => some «cands_lean_int16_lor»
  | "lean_int16_mod" => some «cands_lean_int16_mod»
  | "lean_int16_mul" => some «cands_lean_int16_mul»
  | "lean_int16_neg" => some «cands_lean_int16_neg»
  | "lean_int16_of_int" => some «cands_lean_int16_of_int»
  | "lean_int16_of_nat" => some «cands_lean_int16_of_nat»
  | "lean_int16_shift_left" => some «cands_lean_int16_shift_left»
  | "lean_int16_shift_right" => some «cands_lean_int16_shift_right»
  | "lean_int16_sub" => some «cands_lean_int16_sub»
  | "lean_int16_to_float" => some «cands_lean_int16_to_float»
  | "lean_int16_to_float32" => some «cands_lean_int16_to_float32»
  | "lean_int16_to_int" => some «cands_lean_int16_to_int»
  | "lean_int16_to_int32" => some «cands_lean_int16_to_int32»
  | "lean_int16_to_int64" => some «cands_lean_int16_to_int64»
  | "lean_int16_to_int8" => some «cands_lean_int16_to_int8»
  | "lean_int16_xor" => some «cands_lean_int16_xor»
  | "lean_int32_abs" => some «cands_lean_int32_abs»
  | "lean_int32_add" => some «cands_lean_int32_add»
  | "lean_int32_complement" => some «cands_lean_int32_complement»
  | "lean_int32_dec_eq" => some «cands_lean_int32_dec_eq»
  | "lean_int32_dec_le" => some «cands_lean_int32_dec_le»
  | "lean_int32_dec_lt" => some «cands_lean_int32_dec_lt»
  | "lean_int32_div" => some «cands_lean_int32_div»
  | "lean_int32_land" => some «cands_lean_int32_land»
  | "lean_int32_lor" => some «cands_lean_int32_lor»
  | "lean_int32_mod" => some «cands_lean_int32_mod»
  | "lean_int32_mul" => some «cands_lean_int32_mul»
  | "lean_int32_neg" => some «cands_lean_int32_neg»
  | "lean_int32_of_int" => some «cands_lean_int32_of_int»
  | "lean_int32_of_nat" => some «cands_lean_int32_of_nat»
  | "lean_int32_shift_left" => some «cands_lean_int32_shift_left»
  | "lean_int32_shift_right" => some «cands_lean_int32_shift_right»
  | "lean_int32_sub" => some «cands_lean_int32_sub»
  | "lean_int32_to_float" => some «cands_lean_int32_to_float»
  | "lean_int32_to_float32" => some «cands_lean_int32_to_float32»
  | "lean_int32_to_int" => some «cands_lean_int32_to_int»
  | "lean_int32_to_int16" => some «cands_lean_int32_to_int16»
  | "lean_int32_to_int64" => some «cands_lean_int32_to_int64»
  | "lean_int32_to_int8" => some «cands_lean_int32_to_int8»
  | "lean_int32_xor" => some «cands_lean_int32_xor»
  | "lean_int64_abs" => some «cands_lean_int64_abs»
  | "lean_int64_add" => some «cands_lean_int64_add»
  | "lean_int64_complement" => some «cands_lean_int64_complement»
  | "lean_int64_dec_eq" => some «cands_lean_int64_dec_eq»
  | "lean_int64_dec_le" => some «cands_lean_int64_dec_le»
  | "lean_int64_dec_lt" => some «cands_lean_int64_dec_lt»
  | "lean_int64_div" => some «cands_lean_int64_div»
  | "lean_int64_land" => some «cands_lean_int64_land»
  | "lean_int64_lor" => some «cands_lean_int64_lor»
  | "lean_int64_mod" => some «cands_lean_int64_mod»
  | "lean_int64_mul" => some «cands_lean_int64_mul»
  | "lean_int64_neg" => some «cands_lean_int64_neg»
  | "lean_int64_of_int" => some «cands_lean_int64_of_int»
  | "lean_int64_of_nat" => some «cands_lean_int64_of_nat»
  | "lean_int64_shift_left" => some «cands_lean_int64_shift_left»
  | "lean_int64_shift_right" => some «cands_lean_int64_shift_right»
  | "lean_int64_sub" => some «cands_lean_int64_sub»
  | "lean_int64_to_float" => some «cands_lean_int64_to_float»
  | "lean_int64_to_float32" => some «cands_lean_int64_to_float32»
  | "lean_int64_to_int16" => some «cands_lean_int64_to_int16»
  | "lean_int64_to_int32" => some «cands_lean_int64_to_int32»
  | "lean_int64_to_int8" => some «cands_lean_int64_to_int8»
  | "lean_int64_to_int_sint" => some «cands_lean_int64_to_int_sint»
  | "lean_int64_xor" => some «cands_lean_int64_xor»
  | "lean_int8_abs" => some «cands_lean_int8_abs»
  | "lean_int8_add" => some «cands_lean_int8_add»
  | "lean_int8_complement" => some «cands_lean_int8_complement»
  | "lean_int8_dec_eq" => some «cands_lean_int8_dec_eq»
  | "lean_int8_dec_le" => some «cands_lean_int8_dec_le»
  | "lean_int8_dec_lt" => some «cands_lean_int8_dec_lt»
  | "lean_int8_div" => some «cands_lean_int8_div»
  | "lean_int8_land" => some «cands_lean_int8_land»
  | "lean_int8_lor" => some «cands_lean_int8_lor»
  | "lean_int8_mod" => some «cands_lean_int8_mod»
  | "lean_int8_mul" => some «cands_lean_int8_mul»
  | "lean_int8_neg" => some «cands_lean_int8_neg»
  | "lean_int8_of_int" => some «cands_lean_int8_of_int»
  | "lean_int8_of_nat" => some «cands_lean_int8_of_nat»
  | "lean_int8_shift_left" => some «cands_lean_int8_shift_left»
  | "lean_int8_shift_right" => some «cands_lean_int8_shift_right»
  | "lean_int8_sub" => some «cands_lean_int8_sub»
  | "lean_int8_to_float" => some «cands_lean_int8_to_float»
  | "lean_int8_to_float32" => some «cands_lean_int8_to_float32»
  | "lean_int8_to_int" => some «cands_lean_int8_to_int»
  | "lean_int8_to_int16" => some «cands_lean_int8_to_int16»
  | "lean_int8_to_int32" => some «cands_lean_int8_to_int32»
  | "lean_int8_to_int64" => some «cands_lean_int8_to_int64»
  | "lean_int8_xor" => some «cands_lean_int8_xor»
  | _ => none

end JsOp

end MoreJs

end
