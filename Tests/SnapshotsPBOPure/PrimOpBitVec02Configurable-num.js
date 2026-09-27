import { BitVec_toNat } from "../runtime/lean_runtime_nat_num.mjs";
import {
  BitVec_and,
  BitVec_not,
  BitVec_or,
  BitVec_shiftLeft,
  BitVec_ushiftRight,
  BitVec_xor,
} from "../runtime/lean_runtime_bitvec_num.mjs";
export const TestBitVec64_xor = (v0, v1) => BitVec_xor(64, v0, v1);
export const TestBitVec64_shiftRight = (
  v0,
  v1,
) => BitVec_ushiftRight(64, v0, BitVec_toNat(64, v1));
export const TestBitVec64_shiftLeft = (
  v0,
  v1,
) => BitVec_shiftLeft(64, v0, BitVec_toNat(64, v1));
export const TestBitVec64_lor = (v0, v1) => BitVec_or(64, v0, v1);
export const TestBitVec64_land = (v0, v1) => BitVec_and(64, v0, v1);
export const TestBitVec64_complement = (v0) => BitVec_not(64, v0);
export const TestBitVec32_xor = (v0, v1) => BitVec_xor(32, v0, v1);
export const TestBitVec32_shiftRight = (
  v0,
  v1,
) => BitVec_ushiftRight(32, v0, BitVec_toNat(32, v1));
export const TestBitVec32_shiftLeft = (
  v0,
  v1,
) => BitVec_shiftLeft(32, v0, BitVec_toNat(32, v1));
export const TestBitVec32_lor = (v0, v1) => BitVec_or(32, v0, v1);
export const TestBitVec32_land = (v0, v1) => BitVec_and(32, v0, v1);
export const TestBitVec32_complement = (v0) => BitVec_not(32, v0);
