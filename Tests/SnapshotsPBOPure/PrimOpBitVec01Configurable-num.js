import {
  instDecidableEqBitVec,
  instDecidableLeBitVec,
  instDecidableLtBitVec,
} from "../runtime/lean_runtime_non_configurable.mjs";
import {
  BitVec_add,
  BitVec_mul,
  BitVec_neg,
  BitVec_sub,
  BitVec_udiv,
} from "../runtime/lean_runtime_bitvec_num.mjs";
export const TestBitVec64_sub = (v0, v1) => BitVec_sub(64, v0, v1);
export const TestBitVec64_neg = (v0) => BitVec_neg(64, v0);
export const TestBitVec64_ne = (v0, v1) => {
  if (instDecidableEqBitVec(64, v0, v1)) {
    return false;
  } else {
    return true;
  }
};
export const TestBitVec64_mul = (v0, v1) => BitVec_mul(64, v0, v1);
export const TestBitVec64_lt = (v0, v1) => instDecidableLtBitVec(64, v0, v1);
export const TestBitVec64_le = (v0, v1) => instDecidableLeBitVec(64, v0, v1);
export const TestBitVec64_gt = (v0, v1) => instDecidableLtBitVec(64, v1, v0);
export const TestBitVec64_ge = (v0, v1) => instDecidableLeBitVec(64, v1, v0);
export const TestBitVec64_eq = (v0, v1) => instDecidableEqBitVec(64, v0, v1);
export const TestBitVec64_div = (v0, v1) => BitVec_udiv(64, v0, v1);
export const TestBitVec64_add = (v0, v1) => BitVec_add(64, v0, v1);
export const TestBitVec32_sub = (v0, v1) => BitVec_sub(32, v0, v1);
export const TestBitVec32_neg = (v0) => BitVec_neg(32, v0);
export const TestBitVec32_ne = (v0, v1) => {
  if (instDecidableEqBitVec(32, v0, v1)) {
    return false;
  } else {
    return true;
  }
};
export const TestBitVec32_mul = (v0, v1) => BitVec_mul(32, v0, v1);
export const TestBitVec32_lt = (v0, v1) => instDecidableLtBitVec(32, v0, v1);
export const TestBitVec32_le = (v0, v1) => instDecidableLeBitVec(32, v0, v1);
export const TestBitVec32_gt = (v0, v1) => instDecidableLtBitVec(32, v1, v0);
export const TestBitVec32_ge = (v0, v1) => instDecidableLeBitVec(32, v1, v0);
export const TestBitVec32_eq = (v0, v1) => instDecidableEqBitVec(32, v0, v1);
export const TestBitVec32_div = (v0, v1) => BitVec_udiv(32, v0, v1);
export const TestBitVec32_add = (v0, v1) => BitVec_add(32, v0, v1);
