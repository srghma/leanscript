import {
  Int_instDecidableEq,
  instDecidableEqISize,
  instDecidableEqInt64,
  instDecidableEqUInt64,
  instDecidableEqUSize,
} from "../runtime/lean_runtime_non_configurable.mjs";
import { $lean_nat_div } from "../runtime/lean_runtime_nat_bigint.mjs";
import {
  $lean_int_ediv,
  $lean_int_neg,
} from "../runtime/lean_runtime_int_bigint.mjs";
import {
  $lean_usize_div,
  $lean_usize_neg,
} from "../runtime/lean_runtime_usize_bigint.mjs";
import {
  $lean_uint64_div,
  $lean_uint64_neg,
} from "../runtime/lean_runtime_uint64_bigint.mjs";
import {
  $lean_int64_div,
  $lean_int64_neg,
  $lean_int64_of_nat,
} from "../runtime/lean_runtime_int64_bigint.mjs";
import {
  $lean_isize_div,
  $lean_isize_neg,
  $lean_isize_of_nat,
} from "../runtime/lean_runtime_isize_bigint.mjs";
export const TestUSize_divNoInline = (v0, v1) => $lean_usize_div(v0, v1);
export const TestUSize_test3m2_shouldBeTrue = (() => {
  const v0 = $lean_usize_neg(2n);
  const v1 = $lean_usize_div(3n, v0);
  const v2 = instDecidableEqUSize(v1, TestUSize_divNoInline(3n, v0));
  if (v2) {
    return instDecidableEqUSize(v1, 0n);
  } else {
    return v2;
  }
})();
export const TestUSize_test3_2_shouldBeTrue = (() => {
  const v0 = $lean_usize_div(3n, 2n);
  const v1 = instDecidableEqUSize(v0, TestUSize_divNoInline(3n, 2n));
  if (v1) {
    return instDecidableEqUSize(v0, 1n);
  } else {
    return v1;
  }
})();
export const TestUSize_test1_0_shouldBeTrue = (() => {
  const v0 = $lean_usize_div(1n, 0n);
  const v1 = instDecidableEqUSize(v0, TestUSize_divNoInline(1n, 0n));
  if (v1) {
    return instDecidableEqUSize(v0, 0n);
  } else {
    return v1;
  }
})();
export const TestUInt64_divNoInline = (v0, v1) => $lean_uint64_div(v0, v1);
export const TestUInt64_test3m2_shouldBeTrue = (() => {
  const v0 = $lean_uint64_neg(2n);
  const v1 = $lean_uint64_div(3n, v0);
  const v2 = instDecidableEqUInt64(v1, TestUInt64_divNoInline(3n, v0));
  if (v2) {
    return instDecidableEqUInt64(v1, 0n);
  } else {
    return v2;
  }
})();
export const TestUInt64_test3_2_shouldBeTrue = (() => {
  const v0 = instDecidableEqUInt64(1n, TestUInt64_divNoInline(3n, 2n));
  if (v0) {
    return instDecidableEqUInt64(1n, 1n);
  } else {
    return v0;
  }
})();
export const TestUInt64_test1_0_shouldBeTrue = (() => {
  const v0 = instDecidableEqUInt64(0n, TestUInt64_divNoInline(1n, 0n));
  if (v0) {
    return instDecidableEqUInt64(0n, 0n);
  } else {
    return v0;
  }
})();
export const TestNat_divNoInline = (v0, v1) => $lean_nat_div(v0, v1);
export const TestNat_test3_2_shouldBeTrue = (() => {
  const v0 = 1n === TestNat_divNoInline(3n, 2n);
  if (v0) {
    return 1n === 1n;
  } else {
    return v0;
  }
})();
export const TestNat_test1_0_shouldBeTrue = (() => {
  const v0 = 0n === TestNat_divNoInline(1n, 0n);
  if (v0) {
    return 0n === 0n;
  } else {
    return v0;
  }
})();
export const TestInt64_divNoInline = (v0, v1) => $lean_int64_div(v0, v1);
export const TestInt64_test3m2_shouldBeTrue = (() => {
  const v0 = $lean_int64_of_nat(3n);
  const v1 = $lean_int64_neg($lean_int64_of_nat(2n));
  const v2 = $lean_int64_div(v0, v1);
  const v3 = instDecidableEqInt64(v2, TestInt64_divNoInline(v0, v1));
  if (v3) {
    return instDecidableEqInt64(v2, $lean_int64_neg($lean_int64_of_nat(1n)));
  } else {
    return v3;
  }
})();
export const TestInt64_test3_2_shouldBeTrue = (() => {
  const v0 = $lean_int64_of_nat(3n);
  const v1 = $lean_int64_of_nat(2n);
  const v2 = $lean_int64_div(v0, v1);
  const v3 = instDecidableEqInt64(v2, TestInt64_divNoInline(v0, v1));
  if (v3) {
    return instDecidableEqInt64(v2, $lean_int64_of_nat(1n));
  } else {
    return v3;
  }
})();
export const TestInt64_test1_0_shouldBeTrue = (() => {
  const v0 = $lean_int64_of_nat(1n);
  const v1 = $lean_int64_of_nat(0n);
  const v2 = $lean_int64_div(v0, v1);
  const v3 = instDecidableEqInt64(v2, TestInt64_divNoInline(v0, v1));
  if (v3) {
    return instDecidableEqInt64(v2, v1);
  } else {
    return v3;
  }
})();
export const TestInt_divNoInline = (v0, v1) => $lean_int_ediv(v0, v1);
export const TestInt_test3m2_shouldBeTrue = (() => {
  const v0 = $lean_int_neg(2n);
  const v1 = $lean_int_ediv(3n, v0);
  const v2 = Int_instDecidableEq(v1, TestInt_divNoInline(3n, v0));
  if (v2) {
    return Int_instDecidableEq(v1, $lean_int_neg(1n));
  } else {
    return v2;
  }
})();
export const TestInt_test3_2_shouldBeTrue = (() => {
  const v0 = $lean_int_ediv(3n, 2n);
  const v1 = Int_instDecidableEq(v0, TestInt_divNoInline(3n, 2n));
  if (v1) {
    return Int_instDecidableEq(v0, 1n);
  } else {
    return v1;
  }
})();
export const TestInt_test1_0_shouldBeTrue = (() => {
  const v0 = $lean_int_ediv(1n, 0n);
  const v1 = Int_instDecidableEq(v0, TestInt_divNoInline(1n, 0n));
  if (v1) {
    return Int_instDecidableEq(v0, 0n);
  } else {
    return v1;
  }
})();
export const TestISize_divNoInline = (v0, v1) => $lean_isize_div(v0, v1);
export const TestISize_test3m2_shouldBeTrue = (() => {
  const v0 = $lean_isize_of_nat(3n);
  const v1 = $lean_isize_neg($lean_isize_of_nat(2n));
  const v2 = $lean_isize_div(v0, v1);
  const v3 = instDecidableEqISize(v2, TestISize_divNoInline(v0, v1));
  if (v3) {
    return instDecidableEqISize(v2, $lean_isize_neg($lean_isize_of_nat(1n)));
  } else {
    return v3;
  }
})();
export const TestISize_test3_2_shouldBeTrue = (() => {
  const v0 = $lean_isize_of_nat(3n);
  const v1 = $lean_isize_of_nat(2n);
  const v2 = $lean_isize_div(v0, v1);
  const v3 = instDecidableEqISize(v2, TestISize_divNoInline(v0, v1));
  if (v3) {
    return instDecidableEqISize(v2, $lean_isize_of_nat(1n));
  } else {
    return v3;
  }
})();
export const TestISize_test1_0_shouldBeTrue = (() => {
  const v0 = $lean_isize_of_nat(1n);
  const v1 = $lean_isize_of_nat(0n);
  const v2 = $lean_isize_div(v0, v1);
  const v3 = instDecidableEqISize(v2, TestISize_divNoInline(v0, v1));
  if (v3) {
    return instDecidableEqISize(v2, v1);
  } else {
    return v3;
  }
})();
export const test = (v0, v1, v2, v3, v4, v5) => {
  const v6 = v1(v3, v4);
  const v7 = v0(v6, v2(v3, v4));
  if (v7) {
    return v0(v6, v5);
  } else {
    return v7;
  }
};
