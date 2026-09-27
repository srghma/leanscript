import {
  $lean_nat_land,
  $lean_nat_lor,
  $lean_nat_lxor,
  $lean_nat_shiftl,
  $lean_nat_shiftr,
} from "../runtime/lean_runtime_nat_num.mjs";
import { Int_not } from "../runtime/lean_runtime_int_num.mjs";
import {
  $lean_usize_complement,
  $lean_usize_land,
  $lean_usize_lor,
  $lean_usize_shift_left,
  $lean_usize_shift_right,
  $lean_usize_xor,
} from "../runtime/lean_runtime_usize_num.mjs";
import {
  $lean_uint64_complement,
  $lean_uint64_land,
  $lean_uint64_lor,
  $lean_uint64_shift_left,
  $lean_uint64_shift_right,
  $lean_uint64_xor,
} from "../runtime/lean_runtime_uint64_num.mjs";
import {
  $lean_int64_complement,
  $lean_int64_land,
  $lean_int64_lor,
  $lean_int64_shift_left,
  $lean_int64_shift_right,
  $lean_int64_xor,
} from "../runtime/lean_runtime_int64_num.mjs";
import {
  $lean_isize_complement,
  $lean_isize_land,
  $lean_isize_lor,
  $lean_isize_shift_left,
  $lean_isize_shift_right,
  $lean_isize_xor,
} from "../runtime/lean_runtime_isize_num.mjs";
export const TestUSize_xor = (v0, v1) => $lean_usize_xor(v0, v1);
export const TestUSize_shiftRight = (v0, v1) => $lean_usize_shift_right(v0, v1);
export const TestUSize_shiftLeft = (v0, v1) => $lean_usize_shift_left(v0, v1);
export const TestUSize_lor = (v0, v1) => $lean_usize_lor(v0, v1);
export const TestUSize_land = (v0, v1) => $lean_usize_land(v0, v1);
export const TestUSize_complement = (v0) => $lean_usize_complement(v0);
export const TestUInt64_xor = (v0, v1) => $lean_uint64_xor(v0, v1);
export const TestUInt64_shiftRight = (
  v0,
  v1,
) => $lean_uint64_shift_right(v0, v1);
export const TestUInt64_shiftLeft = (v0, v1) => $lean_uint64_shift_left(v0, v1);
export const TestUInt64_lor = (v0, v1) => $lean_uint64_lor(v0, v1);
export const TestUInt64_land = (v0, v1) => $lean_uint64_land(v0, v1);
export const TestUInt64_complement = (v0) => $lean_uint64_complement(v0);
export const TestNat_xor = (v0, v1) => $lean_nat_lxor(v0, v1);
export const TestNat_shiftRight = (v0, v1) => $lean_nat_shiftr(v0, v1);
export const TestNat_shiftLeft = (v0, v1) => $lean_nat_shiftl(v0, v1);
export const TestNat_lor = (v0, v1) => $lean_nat_lor(v0, v1);
export const TestNat_land = (v0, v1) => $lean_nat_land(v0, v1);
export const TestInt64_xor = (v0, v1) => $lean_int64_xor(v0, v1);
export const TestInt64_shiftRight = (v0, v1) => $lean_int64_shift_right(v0, v1);
export const TestInt64_shiftLeft = (v0, v1) => $lean_int64_shift_left(v0, v1);
export const TestInt64_lor = (v0, v1) => $lean_int64_lor(v0, v1);
export const TestInt64_land = (v0, v1) => $lean_int64_land(v0, v1);
export const TestInt64_complement = (v0) => $lean_int64_complement(v0);
export const TestInt_complement = Int_not;
export const TestISize_xor = (v0, v1) => $lean_isize_xor(v0, v1);
export const TestISize_shiftRight = (v0, v1) => $lean_isize_shift_right(v0, v1);
export const TestISize_shiftLeft = (v0, v1) => $lean_isize_shift_left(v0, v1);
export const TestISize_lor = (v0, v1) => $lean_isize_lor(v0, v1);
export const TestISize_land = (v0, v1) => $lean_isize_land(v0, v1);
export const TestISize_complement = (v0) => $lean_isize_complement(v0);
