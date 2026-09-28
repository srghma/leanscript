import {
  $lean_int16_add,
  $lean_int16_mul,
  $lean_int16_neg,
  $lean_int16_of_nat,
  $lean_int16_sub,
  $lean_int32_add,
  $lean_int32_mul,
  $lean_int32_neg,
  $lean_int32_of_nat,
  $lean_int32_sub,
  $lean_int8_add,
  $lean_int8_mul,
  $lean_int8_neg,
  $lean_int8_of_nat,
  $lean_int8_sub,
  $lean_uint16_add,
  $lean_uint32_add,
  $lean_uint8_add,
} from "../runtime/lean_runtime_non_configurable.mjs";
export const TestUInt8_test4 = (
  v0,
) => $lean_uint8_add($lean_uint8_add(200, v0), 200);
export const TestUInt8_test3 = 144;
export const TestUInt8_test2 = 106;
export const TestUInt8_test1 = 144;
export const TestUInt32_test4 = (
  v0,
) => $lean_uint32_add($lean_uint32_add(3000000000, v0), 3000000000);
export const TestUInt32_test3 = 2643460096;
export const TestUInt32_test2 = 2294967296;
export const TestUInt32_test1 = 1705032704;
export const TestUInt16_test4 = (
  v0,
) => $lean_uint16_add($lean_uint16_add(50000, v0), 50000);
export const TestUInt16_test3 = 16960;
export const TestUInt16_test2 = 25536;
export const TestUInt16_test1 = 34464;
export const TestInt8_test4 = (v0) => {
  const v1 = 100;
  return $lean_int8_add($lean_int8_add(v1, v0), v1);
};
export const TestInt8_test3 = (() => {
  const v0 = 20;
  return $lean_int8_mul(v0, v0);
})();
export const TestInt8_test2 = (() => {
  const v0 = 100;
  return $lean_int8_sub($lean_int8_neg(v0), v0);
})();
export const TestInt8_test1 = (() => {
  const v0 = 100;
  return $lean_int8_add(v0, v0);
})();
export const TestInt32_test4 = (v0) => {
  const v1 = 2000000000;
  return $lean_int32_add($lean_int32_add(v1, v0), v1);
};
export const TestInt32_test3 = (() => {
  const v0 = 2000000001;
  return $lean_int32_mul(v0, v0);
})();
export const TestInt32_test2 = (() => {
  const v0 = 2000000000;
  return $lean_int32_sub($lean_int32_neg(v0), v0);
})();
export const TestInt32_test1 = (() => {
  const v0 = 2000000000;
  return $lean_int32_add(v0, v0);
})();
export const TestInt16_test4 = (v0) => {
  const v1 = 20000;
  return $lean_int16_add($lean_int16_add(v1, v0), v1);
};
export const TestInt16_test3 = (() => {
  const v0 = 1000;
  return $lean_int16_mul(v0, v0);
})();
export const TestInt16_test2 = (() => {
  const v0 = 20000;
  return $lean_int16_sub($lean_int16_neg(v0), v0);
})();
export const TestInt16_test1 = (() => {
  const v0 = 20000;
  return $lean_int16_add(v0, v0);
})();
