import {
  $lean_nat_land,
  $lean_nat_lor,
  $lean_nat_lxor,
  $lean_nat_shiftl,
  $lean_nat_shiftr,
} from "../runtime/lean_runtime_nat_num.mjs";
import { $lean_int_neg, Int_not } from "../runtime/lean_runtime_int_num.mjs";
import {
  $lean_usize_complement,
  $lean_usize_land,
  $lean_usize_lor,
  $lean_usize_neg,
  $lean_usize_shift_left,
  $lean_usize_shift_right,
  $lean_usize_xor,
} from "../runtime/lean_runtime_usize_num.mjs";
import {
  $lean_uint64_complement,
  $lean_uint64_land,
  $lean_uint64_lor,
  $lean_uint64_neg,
  $lean_uint64_shift_left,
  $lean_uint64_shift_right,
  $lean_uint64_xor,
} from "../runtime/lean_runtime_uint64_num.mjs";
import {
  $lean_int64_complement,
  $lean_int64_land,
  $lean_int64_lor,
  $lean_int64_neg,
  $lean_int64_of_nat,
  $lean_int64_shift_left,
  $lean_int64_shift_right,
  $lean_int64_xor,
} from "../runtime/lean_runtime_int64_num.mjs";
import {
  $lean_isize_complement,
  $lean_isize_land,
  $lean_isize_lor,
  $lean_isize_neg,
  $lean_isize_of_nat,
  $lean_isize_shift_left,
  $lean_isize_shift_right,
  $lean_isize_xor,
} from "../runtime/lean_runtime_isize_num.mjs";
export const TestUSize_xor = $lean_usize_xor(15, 12);
export const TestUSize_shiftRight = $lean_usize_shift_right(
  $lean_usize_neg(1023),
  2,
);
export const TestUSize_shiftLeft = $lean_usize_shift_left(1023, 2);
export const TestUSize_lor = $lean_usize_lor(16, 15);
export const TestUSize_land = $lean_usize_land(1023, 8);
export const TestUSize_complement = $lean_usize_complement($lean_usize_neg(3));
export const TestUInt64_xor = $lean_uint64_xor(15, 12);
export const TestUInt64_shiftRight = $lean_uint64_shift_right(
  $lean_uint64_neg(1023),
  2,
);
export const TestUInt64_shiftLeft = $lean_uint64_shift_left(1023, 2);
export const TestUInt64_lor = $lean_uint64_lor(16, 15);
export const TestUInt64_land = $lean_uint64_land(1023, 8);
export const TestUInt64_complement = $lean_uint64_complement(
  $lean_uint64_neg(3),
);
export const TestNat_xor = $lean_nat_lxor(15, 12);
export const TestNat_shiftRight = $lean_nat_shiftr(1023, 2);
export const TestNat_shiftLeft = $lean_nat_shiftl(1023, 2);
export const TestNat_lor = $lean_nat_lor(16, 15);
export const TestNat_land = $lean_nat_land(1023, 8);
export const TestInt64_xor = $lean_int64_xor(
  $lean_int64_of_nat(15),
  $lean_int64_of_nat(12),
);
export const TestInt64_shiftRight = $lean_int64_shift_right(
  $lean_int64_neg($lean_int64_of_nat(1023)),
  $lean_int64_of_nat(2),
);
export const TestInt64_shiftLeft = $lean_int64_shift_left(
  $lean_int64_of_nat(1023),
  $lean_int64_of_nat(2),
);
export const TestInt64_lor = $lean_int64_lor(
  $lean_int64_of_nat(16),
  $lean_int64_of_nat(15),
);
export const TestInt64_land = $lean_int64_land(
  $lean_int64_of_nat(1023),
  $lean_int64_of_nat(8),
);
export const TestInt64_complement = $lean_int64_complement(
  $lean_int64_neg($lean_int64_of_nat(3)),
);
export const TestInt_complement = Int_not($lean_int_neg(3));
export const TestISize_xor = $lean_isize_xor(
  $lean_isize_of_nat(15),
  $lean_isize_of_nat(12),
);
export const TestISize_shiftRight = $lean_isize_shift_right(
  $lean_isize_neg($lean_isize_of_nat(1023)),
  $lean_isize_of_nat(2),
);
export const TestISize_shiftLeft = $lean_isize_shift_left(
  $lean_isize_of_nat(1023),
  $lean_isize_of_nat(2),
);
export const TestISize_lor = $lean_isize_lor(
  $lean_isize_of_nat(16),
  $lean_isize_of_nat(15),
);
export const TestISize_land = $lean_isize_land(
  $lean_isize_of_nat(1023),
  $lean_isize_of_nat(8),
);
export const TestISize_complement = $lean_isize_complement(
  $lean_isize_neg($lean_isize_of_nat(3)),
);
