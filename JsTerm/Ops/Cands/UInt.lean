module

public import JsTerm.Ops.Op

@[expose] public section

set_option autoImplicit false

/-!
# The operations of the externs of the unsigned fixed-width integers

**Generated** by `scripts/gen_js_ops.py`; do not edit.

The candidates (`JsOp.Cand`) of every extern of the unsigned fixed-width integers (`lean_uint8_*`, …, `lean_uint64_*`, `lean_usize_*`): its
operations at their signatures, for the lookup (`JsOp.lookup`, `JsTerm.Ops.Lookup`).
-/

namespace MoreJs

namespace JsOp

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
  [⟨_, _, _, _, .imported .bigint_nat__lean_uint64_to_float32⟩, ⟨_, _, _, _, .inlined .uint53__lean_uint64_to_float32⟩]

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

/-- The candidates of the extern `name`, when it is one of the unsigned fixed-width integers. -/
def candsUInt? (name : String) : Option (List Cand) :=
  match name with
  | "lean_uint16_add" => some «cands_lean_uint16_add»
  | "lean_uint16_complement" => some «cands_lean_uint16_complement»
  | "lean_uint16_dec_eq" => some «cands_lean_uint16_dec_eq»
  | "lean_uint16_dec_le" => some «cands_lean_uint16_dec_le»
  | "lean_uint16_dec_lt" => some «cands_lean_uint16_dec_lt»
  | "lean_uint16_div" => some «cands_lean_uint16_div»
  | "lean_uint16_land" => some «cands_lean_uint16_land»
  | "lean_uint16_log2" => some «cands_lean_uint16_log2»
  | "lean_uint16_lor" => some «cands_lean_uint16_lor»
  | "lean_uint16_mod" => some «cands_lean_uint16_mod»
  | "lean_uint16_mul" => some «cands_lean_uint16_mul»
  | "lean_uint16_neg" => some «cands_lean_uint16_neg»
  | "lean_uint16_of_nat__UInt16_ofNat" => some «cands_lean_uint16_of_nat__UInt16_ofNat»
  | "lean_uint16_of_nat__UInt16_ofNatLT" => some «cands_lean_uint16_of_nat__UInt16_ofNatLT»
  | "lean_uint16_of_nat_mk" => some «cands_lean_uint16_of_nat_mk»
  | "lean_uint16_shift_left" => some «cands_lean_uint16_shift_left»
  | "lean_uint16_shift_right" => some «cands_lean_uint16_shift_right»
  | "lean_uint16_sub" => some «cands_lean_uint16_sub»
  | "lean_uint16_to_float" => some «cands_lean_uint16_to_float»
  | "lean_uint16_to_float32" => some «cands_lean_uint16_to_float32»
  | "lean_uint16_to_nat__UInt16_toBitVec" => some «cands_lean_uint16_to_nat__UInt16_toBitVec»
  | "lean_uint16_to_nat__UInt16_toNat" => some «cands_lean_uint16_to_nat__UInt16_toNat»
  | "lean_uint16_to_uint32" => some «cands_lean_uint16_to_uint32»
  | "lean_uint16_to_uint64" => some «cands_lean_uint16_to_uint64»
  | "lean_uint16_to_uint8" => some «cands_lean_uint16_to_uint8»
  | "lean_uint16_xor" => some «cands_lean_uint16_xor»
  | "lean_uint32_add" => some «cands_lean_uint32_add»
  | "lean_uint32_complement" => some «cands_lean_uint32_complement»
  | "lean_uint32_dec_eq" => some «cands_lean_uint32_dec_eq»
  | "lean_uint32_dec_le" => some «cands_lean_uint32_dec_le»
  | "lean_uint32_dec_lt" => some «cands_lean_uint32_dec_lt»
  | "lean_uint32_div" => some «cands_lean_uint32_div»
  | "lean_uint32_land" => some «cands_lean_uint32_land»
  | "lean_uint32_log2" => some «cands_lean_uint32_log2»
  | "lean_uint32_lor" => some «cands_lean_uint32_lor»
  | "lean_uint32_mod" => some «cands_lean_uint32_mod»
  | "lean_uint32_mul" => some «cands_lean_uint32_mul»
  | "lean_uint32_neg" => some «cands_lean_uint32_neg»
  | "lean_uint32_of_nat__Char_ofNatAux" => some «cands_lean_uint32_of_nat__Char_ofNatAux»
  | "lean_uint32_of_nat__UInt32_ofNat" => some «cands_lean_uint32_of_nat__UInt32_ofNat»
  | "lean_uint32_of_nat__UInt32_ofNatLT" => some «cands_lean_uint32_of_nat__UInt32_ofNatLT»
  | "lean_uint32_of_nat_mk" => some «cands_lean_uint32_of_nat_mk»
  | "lean_uint32_shift_left" => some «cands_lean_uint32_shift_left»
  | "lean_uint32_shift_right" => some «cands_lean_uint32_shift_right»
  | "lean_uint32_sub" => some «cands_lean_uint32_sub»
  | "lean_uint32_to_float" => some «cands_lean_uint32_to_float»
  | "lean_uint32_to_float32" => some «cands_lean_uint32_to_float32»
  | "lean_uint32_to_nat__UInt32_toBitVec" => some «cands_lean_uint32_to_nat__UInt32_toBitVec»
  | "lean_uint32_to_nat__UInt32_toNat" => some «cands_lean_uint32_to_nat__UInt32_toNat»
  | "lean_uint32_to_uint16" => some «cands_lean_uint32_to_uint16»
  | "lean_uint32_to_uint64" => some «cands_lean_uint32_to_uint64»
  | "lean_uint32_to_uint8" => some «cands_lean_uint32_to_uint8»
  | "lean_uint32_xor" => some «cands_lean_uint32_xor»
  | "lean_uint64_add" => some «cands_lean_uint64_add»
  | "lean_uint64_complement" => some «cands_lean_uint64_complement»
  | "lean_uint64_dec_eq" => some «cands_lean_uint64_dec_eq»
  | "lean_uint64_dec_le" => some «cands_lean_uint64_dec_le»
  | "lean_uint64_dec_lt" => some «cands_lean_uint64_dec_lt»
  | "lean_uint64_div" => some «cands_lean_uint64_div»
  | "lean_uint64_land" => some «cands_lean_uint64_land»
  | "lean_uint64_log2" => some «cands_lean_uint64_log2»
  | "lean_uint64_lor" => some «cands_lean_uint64_lor»
  | "lean_uint64_mix_hash" => some «cands_lean_uint64_mix_hash»
  | "lean_uint64_mod" => some «cands_lean_uint64_mod»
  | "lean_uint64_mul" => some «cands_lean_uint64_mul»
  | "lean_uint64_neg" => some «cands_lean_uint64_neg»
  | "lean_uint64_of_nat__UInt64_ofNat" => some «cands_lean_uint64_of_nat__UInt64_ofNat»
  | "lean_uint64_of_nat__UInt64_ofNatLT" => some «cands_lean_uint64_of_nat__UInt64_ofNatLT»
  | "lean_uint64_of_nat_mk" => some «cands_lean_uint64_of_nat_mk»
  | "lean_uint64_shift_left" => some «cands_lean_uint64_shift_left»
  | "lean_uint64_shift_right" => some «cands_lean_uint64_shift_right»
  | "lean_uint64_sub" => some «cands_lean_uint64_sub»
  | "lean_uint64_to_float" => some «cands_lean_uint64_to_float»
  | "lean_uint64_to_float32" => some «cands_lean_uint64_to_float32»
  | "lean_uint64_to_nat__UInt64_toBitVec" => some «cands_lean_uint64_to_nat__UInt64_toBitVec»
  | "lean_uint64_to_nat__UInt64_toNat" => some «cands_lean_uint64_to_nat__UInt64_toNat»
  | "lean_uint64_to_uint16" => some «cands_lean_uint64_to_uint16»
  | "lean_uint64_to_uint32" => some «cands_lean_uint64_to_uint32»
  | "lean_uint64_to_uint8" => some «cands_lean_uint64_to_uint8»
  | "lean_uint64_xor" => some «cands_lean_uint64_xor»
  | "lean_uint8_add" => some «cands_lean_uint8_add»
  | "lean_uint8_complement" => some «cands_lean_uint8_complement»
  | "lean_uint8_dec_eq" => some «cands_lean_uint8_dec_eq»
  | "lean_uint8_dec_le" => some «cands_lean_uint8_dec_le»
  | "lean_uint8_dec_lt" => some «cands_lean_uint8_dec_lt»
  | "lean_uint8_div" => some «cands_lean_uint8_div»
  | "lean_uint8_land" => some «cands_lean_uint8_land»
  | "lean_uint8_log2" => some «cands_lean_uint8_log2»
  | "lean_uint8_lor" => some «cands_lean_uint8_lor»
  | "lean_uint8_mod" => some «cands_lean_uint8_mod»
  | "lean_uint8_mul" => some «cands_lean_uint8_mul»
  | "lean_uint8_neg" => some «cands_lean_uint8_neg»
  | "lean_uint8_of_nat__UInt8_ofNat" => some «cands_lean_uint8_of_nat__UInt8_ofNat»
  | "lean_uint8_of_nat__UInt8_ofNatLT" => some «cands_lean_uint8_of_nat__UInt8_ofNatLT»
  | "lean_uint8_of_nat_mk" => some «cands_lean_uint8_of_nat_mk»
  | "lean_uint8_shift_left" => some «cands_lean_uint8_shift_left»
  | "lean_uint8_shift_right" => some «cands_lean_uint8_shift_right»
  | "lean_uint8_sub" => some «cands_lean_uint8_sub»
  | "lean_uint8_to_float" => some «cands_lean_uint8_to_float»
  | "lean_uint8_to_float32" => some «cands_lean_uint8_to_float32»
  | "lean_uint8_to_nat__UInt8_toBitVec" => some «cands_lean_uint8_to_nat__UInt8_toBitVec»
  | "lean_uint8_to_nat__UInt8_toNat" => some «cands_lean_uint8_to_nat__UInt8_toNat»
  | "lean_uint8_to_uint16" => some «cands_lean_uint8_to_uint16»
  | "lean_uint8_to_uint32" => some «cands_lean_uint8_to_uint32»
  | "lean_uint8_to_uint64" => some «cands_lean_uint8_to_uint64»
  | "lean_uint8_xor" => some «cands_lean_uint8_xor»
  | _ => none

end JsOp

end MoreJs

end
