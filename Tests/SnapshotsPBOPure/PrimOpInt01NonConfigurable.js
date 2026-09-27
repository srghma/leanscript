import {
  $lean_int16_add,
  $lean_int16_dec_le,
  $lean_int16_dec_lt,
  $lean_int16_div,
  $lean_int16_mul,
  $lean_int16_neg,
  $lean_int16_sub,
  $lean_int32_add,
  $lean_int32_dec_le,
  $lean_int32_dec_lt,
  $lean_int32_div,
  $lean_int32_mul,
  $lean_int32_neg,
  $lean_int32_sub,
  $lean_int8_add,
  $lean_int8_dec_le,
  $lean_int8_dec_lt,
  $lean_int8_div,
  $lean_int8_mul,
  $lean_int8_neg,
  $lean_int8_sub,
  $lean_uint16_add,
  $lean_uint16_div,
  $lean_uint16_mul,
  $lean_uint16_neg,
  $lean_uint16_sub,
  $lean_uint32_add,
  $lean_uint32_div,
  $lean_uint32_mul,
  $lean_uint32_neg,
  $lean_uint32_sub,
  $lean_uint8_add,
  $lean_uint8_div,
  $lean_uint8_mul,
  $lean_uint8_neg,
  $lean_uint8_sub,
  instDecidableEqInt16,
  instDecidableEqInt32,
  instDecidableEqInt8,
  instDecidableEqUInt16,
  instDecidableEqUInt32,
  instDecidableEqUInt8,
} from "../runtime/lean_runtime_non_configurable.mjs";
export const TestUInt8_sub = (v0, v1) => $lean_uint8_sub(v0, v1);
export const TestUInt8_neg = (v0) => $lean_uint8_neg(v0);
export const TestUInt8_ne = (v0, v1) => {
  if (instDecidableEqUInt8(v0, v1)) {
    return false;
  } else {
    return true;
  }
};
export const TestUInt8_mul = (v0, v1) => $lean_uint8_mul(v0, v1);
export const TestUInt8_lt = (v0, v1) => v0 < v1;
export const TestUInt8_le = (v0, v1) => v0 <= v1;
export const TestUInt8_gt = (v0, v1) => v1 < v0;
export const TestUInt8_ge = (v0, v1) => v1 <= v0;
export const TestUInt8_eq = instDecidableEqUInt8;
export const TestUInt8_div = (v0, v1) => $lean_uint8_div(v0, v1);
export const TestUInt8_add = (v0, v1) => $lean_uint8_add(v0, v1);
export const TestUInt32_sub = (v0, v1) => $lean_uint32_sub(v0, v1);
export const TestUInt32_neg = (v0) => $lean_uint32_neg(v0);
export const TestUInt32_ne = (v0, v1) => {
  if (instDecidableEqUInt32(v0, v1)) {
    return false;
  } else {
    return true;
  }
};
export const TestUInt32_mul = (v0, v1) => $lean_uint32_mul(v0, v1);
export const TestUInt32_lt = (v0, v1) => v0 < v1;
export const TestUInt32_le = (v0, v1) => v0 <= v1;
export const TestUInt32_gt = (v0, v1) => v1 < v0;
export const TestUInt32_ge = (v0, v1) => v1 <= v0;
export const TestUInt32_eq = instDecidableEqUInt32;
export const TestUInt32_div = (v0, v1) => $lean_uint32_div(v0, v1);
export const TestUInt32_add = (v0, v1) => $lean_uint32_add(v0, v1);
export const TestUInt16_sub = (v0, v1) => $lean_uint16_sub(v0, v1);
export const TestUInt16_neg = (v0) => $lean_uint16_neg(v0);
export const TestUInt16_ne = (v0, v1) => {
  if (instDecidableEqUInt16(v0, v1)) {
    return false;
  } else {
    return true;
  }
};
export const TestUInt16_mul = (v0, v1) => $lean_uint16_mul(v0, v1);
export const TestUInt16_lt = (v0, v1) => v0 < v1;
export const TestUInt16_le = (v0, v1) => v0 <= v1;
export const TestUInt16_gt = (v0, v1) => v1 < v0;
export const TestUInt16_ge = (v0, v1) => v1 <= v0;
export const TestUInt16_eq = instDecidableEqUInt16;
export const TestUInt16_div = (v0, v1) => $lean_uint16_div(v0, v1);
export const TestUInt16_add = (v0, v1) => $lean_uint16_add(v0, v1);
export const TestInt8_sub = (v0, v1) => $lean_int8_sub(v0, v1);
export const TestInt8_neg = (v0) => $lean_int8_neg(v0);
export const TestInt8_ne = (v0, v1) => {
  if (instDecidableEqInt8(v0, v1)) {
    return false;
  } else {
    return true;
  }
};
export const TestInt8_mul = (v0, v1) => $lean_int8_mul(v0, v1);
export const TestInt8_lt = (v0, v1) => $lean_int8_dec_lt(v0, v1);
export const TestInt8_le = (v0, v1) => $lean_int8_dec_le(v0, v1);
export const TestInt8_gt = (v0, v1) => $lean_int8_dec_lt(v1, v0);
export const TestInt8_ge = (v0, v1) => $lean_int8_dec_le(v1, v0);
export const TestInt8_eq = instDecidableEqInt8;
export const TestInt8_div = (v0, v1) => $lean_int8_div(v0, v1);
export const TestInt8_add = (v0, v1) => $lean_int8_add(v0, v1);
export const TestInt32_sub = (v0, v1) => $lean_int32_sub(v0, v1);
export const TestInt32_neg = (v0) => $lean_int32_neg(v0);
export const TestInt32_ne = (v0, v1) => {
  if (instDecidableEqInt32(v0, v1)) {
    return false;
  } else {
    return true;
  }
};
export const TestInt32_mul = (v0, v1) => $lean_int32_mul(v0, v1);
export const TestInt32_lt = (v0, v1) => $lean_int32_dec_lt(v0, v1);
export const TestInt32_le = (v0, v1) => $lean_int32_dec_le(v0, v1);
export const TestInt32_gt = (v0, v1) => $lean_int32_dec_lt(v1, v0);
export const TestInt32_ge = (v0, v1) => $lean_int32_dec_le(v1, v0);
export const TestInt32_eq = instDecidableEqInt32;
export const TestInt32_div = (v0, v1) => $lean_int32_div(v0, v1);
export const TestInt32_add = (v0, v1) => $lean_int32_add(v0, v1);
export const TestInt16_sub = (v0, v1) => $lean_int16_sub(v0, v1);
export const TestInt16_neg = (v0) => $lean_int16_neg(v0);
export const TestInt16_ne = (v0, v1) => {
  if (instDecidableEqInt16(v0, v1)) {
    return false;
  } else {
    return true;
  }
};
export const TestInt16_mul = (v0, v1) => $lean_int16_mul(v0, v1);
export const TestInt16_lt = (v0, v1) => $lean_int16_dec_lt(v0, v1);
export const TestInt16_le = (v0, v1) => $lean_int16_dec_le(v0, v1);
export const TestInt16_gt = (v0, v1) => $lean_int16_dec_lt(v1, v0);
export const TestInt16_ge = (v0, v1) => $lean_int16_dec_le(v1, v0);
export const TestInt16_eq = instDecidableEqInt16;
export const TestInt16_div = (v0, v1) => $lean_int16_div(v0, v1);
export const TestInt16_add = (v0, v1) => $lean_int16_add(v0, v1);
