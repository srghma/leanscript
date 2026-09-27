import {
  $lean_int64_dec_le,
  $lean_int64_dec_lt,
  $lean_isize_dec_le,
  $lean_isize_dec_lt,
  Int_instDecidableEq,
  instDecidableEqISize,
  instDecidableEqInt64,
  instDecidableEqUInt64,
  instDecidableEqUSize,
} from "../runtime/lean_runtime_non_configurable.mjs";
import {
  $lean_nat_div,
  $lean_nat_sub,
} from "../runtime/lean_runtime_nat_bigint.mjs";
import {
  $lean_int_ediv,
  $lean_int_neg,
} from "../runtime/lean_runtime_int_bigint.mjs";
import {
  $lean_usize_add,
  $lean_usize_div,
  $lean_usize_mul,
  $lean_usize_neg,
  $lean_usize_sub,
} from "../runtime/lean_runtime_usize_bigint.mjs";
import {
  $lean_uint64_add,
  $lean_uint64_div,
  $lean_uint64_mul,
  $lean_uint64_neg,
  $lean_uint64_sub,
} from "../runtime/lean_runtime_uint64_bigint.mjs";
import {
  $lean_int64_add,
  $lean_int64_div,
  $lean_int64_mul,
  $lean_int64_neg,
  $lean_int64_sub,
} from "../runtime/lean_runtime_int64_bigint.mjs";
import {
  $lean_isize_add,
  $lean_isize_div,
  $lean_isize_mul,
  $lean_isize_neg,
  $lean_isize_sub,
} from "../runtime/lean_runtime_isize_bigint.mjs";
export const TestUSize_sub = (v0, v1) => $lean_usize_sub(v0, v1);
export const TestUSize_neg = (v0) => $lean_usize_neg(v0);
export const TestUSize_ne = (v0, v1) => {
  if (instDecidableEqUSize(v0, v1)) {
    return false;
  } else {
    return true;
  }
};
export const TestUSize_mul = (v0, v1) => $lean_usize_mul(v0, v1);
export const TestUSize_lt = (v0, v1) => v0 < v1;
export const TestUSize_le = (v0, v1) => v0 <= v1;
export const TestUSize_gt = (v0, v1) => v1 < v0;
export const TestUSize_ge = (v0, v1) => v1 <= v0;
export const TestUSize_eq = instDecidableEqUSize;
export const TestUSize_div = (v0, v1) => $lean_usize_div(v0, v1);
export const TestUSize_add = (v0, v1) => $lean_usize_add(v0, v1);
export const TestUInt64_sub = (v0, v1) => $lean_uint64_sub(v0, v1);
export const TestUInt64_neg = (v0) => $lean_uint64_neg(v0);
export const TestUInt64_ne = (v0, v1) => {
  if (instDecidableEqUInt64(v0, v1)) {
    return false;
  } else {
    return true;
  }
};
export const TestUInt64_mul = (v0, v1) => $lean_uint64_mul(v0, v1);
export const TestUInt64_lt = (v0, v1) => v0 < v1;
export const TestUInt64_le = (v0, v1) => v0 <= v1;
export const TestUInt64_gt = (v0, v1) => v1 < v0;
export const TestUInt64_ge = (v0, v1) => v1 <= v0;
export const TestUInt64_eq = instDecidableEqUInt64;
export const TestUInt64_div = (v0, v1) => $lean_uint64_div(v0, v1);
export const TestUInt64_add = (v0, v1) => $lean_uint64_add(v0, v1);
export const TestNat_sub = (v0, v1) => $lean_nat_sub(v0, v1);
export const TestNat_ne = (v0, v1) => {
  if (v0 === v1) {
    return false;
  } else {
    return true;
  }
};
export const TestNat_mul = (v0, v1) => v0 * v1;
export const TestNat_lt = (v0, v1) => v0 < v1;
export const TestNat_le = (v0, v1) => v0 <= v1;
export const TestNat_gt = (v0, v1) => v1 < v0;
export const TestNat_ge = (v0, v1) => v1 <= v0;
export const TestNat_eq = (v0, v1) => v0 === v1;
export const TestNat_div = (v0, v1) => $lean_nat_div(v0, v1);
export const TestNat_add = (v0, v1) => v0 + v1;
export const TestInt64_sub = (v0, v1) => $lean_int64_sub(v0, v1);
export const TestInt64_neg = (v0) => $lean_int64_neg(v0);
export const TestInt64_ne = (v0, v1) => {
  if (instDecidableEqInt64(v0, v1)) {
    return false;
  } else {
    return true;
  }
};
export const TestInt64_mul = (v0, v1) => $lean_int64_mul(v0, v1);
export const TestInt64_lt = (v0, v1) => $lean_int64_dec_lt(v0, v1);
export const TestInt64_le = (v0, v1) => $lean_int64_dec_le(v0, v1);
export const TestInt64_gt = (v0, v1) => $lean_int64_dec_lt(v1, v0);
export const TestInt64_ge = (v0, v1) => $lean_int64_dec_le(v1, v0);
export const TestInt64_eq = instDecidableEqInt64;
export const TestInt64_div = (v0, v1) => $lean_int64_div(v0, v1);
export const TestInt64_add = (v0, v1) => $lean_int64_add(v0, v1);
export const TestInt_sub = (v0, v1) => v0 - v1;
export const TestInt_neg = (v0) => $lean_int_neg(v0);
export const TestInt_ne = (v0, v1) => {
  if (Int_instDecidableEq(v0, v1)) {
    return false;
  } else {
    return true;
  }
};
export const TestInt_mul = (v0, v1) => v0 * v1;
export const TestInt_lt = (v0, v1) => v0 < v1;
export const TestInt_le = (v0, v1) => v0 <= v1;
export const TestInt_gt = (v0, v1) => v1 < v0;
export const TestInt_ge = (v0, v1) => v1 <= v0;
export const TestInt_eq = Int_instDecidableEq;
export const TestInt_div = (v0, v1) => $lean_int_ediv(v0, v1);
export const TestInt_add = (v0, v1) => v0 + v1;
export const TestISize_sub = (v0, v1) => $lean_isize_sub(v0, v1);
export const TestISize_neg = (v0) => $lean_isize_neg(v0);
export const TestISize_ne = (v0, v1) => {
  if (instDecidableEqISize(v0, v1)) {
    return false;
  } else {
    return true;
  }
};
export const TestISize_mul = (v0, v1) => $lean_isize_mul(v0, v1);
export const TestISize_lt = (v0, v1) => $lean_isize_dec_lt(v0, v1);
export const TestISize_le = (v0, v1) => $lean_isize_dec_le(v0, v1);
export const TestISize_gt = (v0, v1) => $lean_isize_dec_lt(v1, v0);
export const TestISize_ge = (v0, v1) => $lean_isize_dec_le(v1, v0);
export const TestISize_eq = instDecidableEqISize;
export const TestISize_div = (v0, v1) => $lean_isize_div(v0, v1);
export const TestISize_add = (v0, v1) => $lean_isize_add(v0, v1);
