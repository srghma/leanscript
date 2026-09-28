module

public import JsTerm.Ops.Op

@[expose] public section

set_option autoImplicit false

/-!
# The operations of the externs of the strings

**Generated** by `scripts/gen_js_ops.py`; do not edit.

The candidates (`JsOp.Cand`) of every extern of the strings (`lean_string_*`, `lean_substring_*`, `lean_slice_*`, `lean_char_*`): its
operations at their signatures, for the lookup (`JsOp.lookup`, `JsTerm.Ops.Lookup`).
-/

namespace MoreJs

namespace JsOp

/-- The operations of `lean_slice_dec_lt`. -/
def «cands_lean_slice_dec_lt» : List Cand :=
  [⟨_, _, _, _, .imported .stringSlice__lean_slice_dec_lt⟩]

/-- The operations of `lean_slice_hash`. -/
def «cands_lean_slice_hash» : List Cand :=
  [⟨_, _, _, _, .imported .bigint_nat__lean_slice_hash⟩, ⟨_, _, _, _, .imported .uint53__lean_slice_hash⟩]

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

/-- The candidates of the extern `name`, when it is one of the strings. -/
def candsString? (name : String) : Option (List Cand) :=
  match name with
  | "lean_slice_dec_lt" => some «cands_lean_slice_dec_lt»
  | "lean_slice_hash" => some «cands_lean_slice_hash»
  | "lean_string_any" => some «cands_lean_string_any»
  | "lean_string_append__String_Internal_append" => some «cands_lean_string_append__String_Internal_append»
  | "lean_string_append__String_append" => some «cands_lean_string_append__String_append»
  | "lean_string_capitalize" => some «cands_lean_string_capitalize»
  | "lean_string_compare" => some «cands_lean_string_compare»
  | "lean_string_contains" => some «cands_lean_string_contains»
  | "lean_string_data__String_data" => some «cands_lean_string_data__String_data»
  | "lean_string_data__String_toList" => some «cands_lean_string_data__String_toList»
  | "lean_string_dec_eq" => some «cands_lean_string_dec_eq»
  | "lean_string_dec_lt" => some «cands_lean_string_dec_lt»
  | "lean_string_drop" => some «cands_lean_string_drop»
  | "lean_string_dropright" => some «cands_lean_string_dropright»
  | "lean_string_foldl" => some «cands_lean_string_foldl»
  | "lean_string_front" => some «cands_lean_string_front»
  | "lean_string_get_byte_fast__String_Internal_getUTF8Byte" => some «cands_lean_string_get_byte_fast__String_Internal_getUTF8Byte»
  | "lean_string_get_byte_fast__String_getUTF8Byte" => some «cands_lean_string_get_byte_fast__String_getUTF8Byte»
  | "lean_string_get_byte_fast__String_getUtf8Byte" => some «cands_lean_string_get_byte_fast__String_getUtf8Byte»
  | "lean_string_hash" => some «cands_lean_string_hash»
  | "lean_string_intercalate" => some «cands_lean_string_intercalate»
  | "lean_string_is_valid_pos" => some «cands_lean_string_is_valid_pos»
  | "lean_string_isempty" => some «cands_lean_string_isempty»
  | "lean_string_isprefixof" => some «cands_lean_string_isprefixof»
  | "lean_string_length__String_Internal_length" => some «cands_lean_string_length__String_Internal_length»
  | "lean_string_length__String_length" => some «cands_lean_string_length__String_length»
  | "lean_string_memcmp" => some «cands_lean_string_memcmp»
  | "lean_string_mk__String_mk" => some «cands_lean_string_mk__String_mk»
  | "lean_string_mk__String_ofList" => some «cands_lean_string_mk__String_ofList»
  | "lean_string_nextwhile" => some «cands_lean_string_nextwhile»
  | "lean_string_offsetofpos" => some «cands_lean_string_offsetofpos»
  | "lean_string_pos_min" => some «cands_lean_string_pos_min»
  | "lean_string_pos_sub" => some «cands_lean_string_pos_sub»
  | "lean_string_posof" => some «cands_lean_string_posof»
  | "lean_string_push" => some «cands_lean_string_push»
  | "lean_string_pushn" => some «cands_lean_string_pushn»
  | "lean_string_trim" => some «cands_lean_string_trim»
  | "lean_string_utf8_at_end__String_Internal_atEnd" => some «cands_lean_string_utf8_at_end__String_Internal_atEnd»
  | "lean_string_utf8_at_end__String_Pos_Raw_atEnd" => some «cands_lean_string_utf8_at_end__String_Pos_Raw_atEnd»
  | "lean_string_utf8_at_end__String_atEnd" => some «cands_lean_string_utf8_at_end__String_atEnd»
  | "lean_string_utf8_byte_size" => some «cands_lean_string_utf8_byte_size»
  | "lean_string_utf8_extract__String_Internal_extract" => some «cands_lean_string_utf8_extract__String_Internal_extract»
  | "lean_string_utf8_extract__String_Pos_Raw_extract" => some «cands_lean_string_utf8_extract__String_Pos_Raw_extract»
  | "lean_string_utf8_extract_fast" => some «cands_lean_string_utf8_extract_fast»
  | "lean_string_utf8_get__String_Internal_get" => some «cands_lean_string_utf8_get__String_Internal_get»
  | "lean_string_utf8_get__String_Pos_Raw_get" => some «cands_lean_string_utf8_get__String_Pos_Raw_get»
  | "lean_string_utf8_get__String_get" => some «cands_lean_string_utf8_get__String_get»
  | "lean_string_utf8_get_bang__String_Pos_Raw_get!" => some «cands_lean_string_utf8_get_bang__String_Pos_Raw_get!»
  | "lean_string_utf8_get_bang__String_get!" => some «cands_lean_string_utf8_get_bang__String_get!»
  | "lean_string_utf8_get_fast__String_Pos_Raw_get'" => some «cands_lean_string_utf8_get_fast__String_Pos_Raw_get'»
  | "lean_string_utf8_get_fast__String_get'" => some «cands_lean_string_utf8_get_fast__String_get'»
  | "lean_string_utf8_get_opt__String_Pos_Raw_get?" => some «cands_lean_string_utf8_get_opt__String_Pos_Raw_get?»
  | "lean_string_utf8_get_opt__String_get?" => some «cands_lean_string_utf8_get_opt__String_get?»
  | "lean_string_utf8_next__String_Internal_next" => some «cands_lean_string_utf8_next__String_Internal_next»
  | "lean_string_utf8_next__String_Pos_Raw_next" => some «cands_lean_string_utf8_next__String_Pos_Raw_next»
  | "lean_string_utf8_next__String_next" => some «cands_lean_string_utf8_next__String_next»
  | "lean_string_utf8_next_fast__String_Pos_next" => some «cands_lean_string_utf8_next_fast__String_Pos_next»
  | "lean_string_utf8_next_fast__String_next'" => some «cands_lean_string_utf8_next_fast__String_next'»
  | "lean_string_utf8_prev__String_Pos_Raw_prev" => some «cands_lean_string_utf8_prev__String_Pos_Raw_prev»
  | "lean_string_utf8_prev__String_prev" => some «cands_lean_string_utf8_prev__String_prev»
  | "lean_string_utf8_set__String_Pos_Raw_set" => some «cands_lean_string_utf8_set__String_Pos_Raw_set»
  | "lean_string_utf8_set__String_Pos_set" => some «cands_lean_string_utf8_set__String_Pos_set»
  | "lean_string_utf8_set__String_set" => some «cands_lean_string_utf8_set__String_set»
  | "lean_substring_all" => some «cands_lean_substring_all»
  | "lean_substring_beq" => some «cands_lean_substring_beq»
  | "lean_substring_drop" => some «cands_lean_substring_drop»
  | "lean_substring_extract" => some «cands_lean_substring_extract»
  | "lean_substring_front" => some «cands_lean_substring_front»
  | "lean_substring_get" => some «cands_lean_substring_get»
  | "lean_substring_isempty" => some «cands_lean_substring_isempty»
  | "lean_substring_prev" => some «cands_lean_substring_prev»
  | "lean_substring_takewhile" => some «cands_lean_substring_takewhile»
  | "lean_substring_tostring" => some «cands_lean_substring_tostring»
  | _ => none

end JsOp

end MoreJs

end
