import { $lean_int_neg } from "../runtime/lean_runtime_int_num.mjs";
import {
  $lean_usize_add,
  $lean_usize_mul,
  $lean_usize_sub,
} from "../runtime/lean_runtime_usize_num.mjs";
import { $lean_uint64_add } from "../runtime/lean_runtime_uint64_num.mjs";
import {
  $lean_int64_add,
  $lean_int64_mul,
  $lean_int64_neg,
  $lean_int64_of_nat,
  $lean_int64_sub,
} from "../runtime/lean_runtime_int64_num.mjs";
import {
  $lean_isize_add,
  $lean_isize_mul,
  $lean_isize_neg,
  $lean_isize_of_nat,
  $lean_isize_sub,
} from "../runtime/lean_runtime_isize_num.mjs";
export const TestUSize_test4 = (
  v0,
) => $lean_usize_add(
  $lean_usize_add(10000000000000000000, v0),
  10000000000000000000,
);
export const TestUSize_test3 = $lean_usize_mul(5000000000, 5000000000);
export const TestUSize_test2 = $lean_usize_sub(
  1000000000000000000,
  10000000000000000000,
);
export const TestUSize_test1 = $lean_usize_add(
  10000000000000000000,
  10000000000000000000,
);
export const TestUInt64_test4 = (
  v0,
) => $lean_uint64_add(
  $lean_uint64_add(10000000000000000000, v0),
  10000000000000000000,
);
export const TestUInt64_test3 = 6553255926290448384;
export const TestUInt64_test2 = 9446744073709551616;
export const TestUInt64_test1 = 1553255926290448384;
export const TestNat_test4 = (v0) => 2000000000 + v0 + 2000000000;
export const TestNat_test3 = 4000000000000000000;
export const TestNat_test2 = 0;
export const TestNat_test1 = 4000000000;
export const TestInt64_test4 = (v0) => {
  const v1 = $lean_int64_of_nat(5000000000000000000);
  return $lean_int64_add($lean_int64_add(v1, v0), v1);
};
export const TestInt64_test3 = (() => {
  const v0 = $lean_int64_of_nat(5000000000);
  return $lean_int64_mul(v0, v0);
})();
export const TestInt64_test2 = (() => {
  const v0 = $lean_int64_of_nat(5000000000000000000);
  return $lean_int64_sub($lean_int64_neg(v0), v0);
})();
export const TestInt64_test1 = (() => {
  const v0 = $lean_int64_of_nat(5000000000000000000);
  return $lean_int64_add(v0, v0);
})();
export const TestInt_test4 = (v0) => 2000000000 + v0 + 2000000000;
export const TestInt_test3 = 2000000000 * 2000000000;
export const TestInt_test2 = $lean_int_neg(2000000000) - 2000000000;
export const TestInt_test1 = 2000000000 + 2000000000;
export const TestISize_test4 = (v0) => {
  const v1 = $lean_isize_of_nat(5000000000000000000);
  return $lean_isize_add($lean_isize_add(v1, v0), v1);
};
export const TestISize_test3 = (() => {
  const v0 = $lean_isize_of_nat(5000000000);
  return $lean_isize_mul(v0, v0);
})();
export const TestISize_test2 = (() => {
  const v0 = $lean_isize_of_nat(5000000000000000000);
  return $lean_isize_sub($lean_isize_neg(v0), v0);
})();
export const TestISize_test1 = (() => {
  const v0 = $lean_isize_of_nat(5000000000000000000);
  return $lean_isize_add(v0, v0);
})();
