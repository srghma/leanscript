import {
  $lean_int16_div,
  $lean_int16_neg,
  $lean_int16_of_nat,
  $lean_int32_div,
  $lean_int32_neg,
  $lean_int32_of_nat,
  $lean_int8_div,
  $lean_int8_neg,
  $lean_int8_of_nat,
  $lean_uint16_div,
  $lean_uint16_neg,
  $lean_uint32_div,
  $lean_uint32_neg,
  $lean_uint8_div,
  $lean_uint8_neg,
  instDecidableEqInt16,
  instDecidableEqInt32,
  instDecidableEqInt8,
  instDecidableEqUInt16,
  instDecidableEqUInt32,
  instDecidableEqUInt8,
} from "../runtime/lean_runtime_non_configurable.mjs";
const _private_SnapshotsPBOPure_PrimOpIntDivNonConfigurable_0_TestUInt8_divNoInline = (
  v0,
  v1,
) => $lean_uint8_div(v0, v1);
export const TestUInt8_test3m2__shouldBeTrue = (() => {
  const v0 = $lean_uint8_neg(2);
  const v1 = $lean_uint8_div(3, v0);
  const v2 = instDecidableEqUInt8(
    v1,
    _private_SnapshotsPBOPure_PrimOpIntDivNonConfigurable_0_TestUInt8_divNoInline(
      3,
      v0,
    ),
  );
  if (v2) {
    return instDecidableEqUInt8(v1, 0);
  } else {
    return v2;
  }
})();
export const TestUInt8_test3_2__shouldBeTrue = (() => {
  const v0 = instDecidableEqUInt8(
    1,
    _private_SnapshotsPBOPure_PrimOpIntDivNonConfigurable_0_TestUInt8_divNoInline(
      3,
      2,
    ),
  );
  if (v0) {
    return instDecidableEqUInt8(1, 1);
  } else {
    return v0;
  }
})();
export const TestUInt8_test1_0__shouldBeTrue = (() => {
  const v0 = instDecidableEqUInt8(
    0,
    _private_SnapshotsPBOPure_PrimOpIntDivNonConfigurable_0_TestUInt8_divNoInline(
      1,
      0,
    ),
  );
  if (v0) {
    return instDecidableEqUInt8(0, 0);
  } else {
    return v0;
  }
})();
export const TestUInt32_divNoInline = (v0, v1) => $lean_uint32_div(v0, v1);
export const TestUInt32_test3m2_shouldBeTrue = (() => {
  const v0 = $lean_uint32_neg(2);
  const v1 = $lean_uint32_div(3, v0);
  const v2 = instDecidableEqUInt32(v1, TestUInt32_divNoInline(3, v0));
  if (v2) {
    return instDecidableEqUInt32(v1, 0);
  } else {
    return v2;
  }
})();
export const TestUInt32_test3_2_shouldBeTrue = (() => {
  const v0 = instDecidableEqUInt32(1, TestUInt32_divNoInline(3, 2));
  if (v0) {
    return instDecidableEqUInt32(1, 1);
  } else {
    return v0;
  }
})();
export const TestUInt32_test1_0_shouldBeTrue = (() => {
  const v0 = instDecidableEqUInt32(0, TestUInt32_divNoInline(1, 0));
  if (v0) {
    return instDecidableEqUInt32(0, 0);
  } else {
    return v0;
  }
})();
export const TestUInt16_divNoInline = (v0, v1) => $lean_uint16_div(v0, v1);
export const TestUInt16_test3m2__shouldBeTrue = (() => {
  const v0 = $lean_uint16_neg(2);
  const v1 = $lean_uint16_div(3, v0);
  const v2 = instDecidableEqUInt16(v1, TestUInt16_divNoInline(3, v0));
  if (v2) {
    return instDecidableEqUInt16(v1, 0);
  } else {
    return v2;
  }
})();
export const TestUInt16_test3_2__shouldBeTrue = (() => {
  const v0 = instDecidableEqUInt16(1, TestUInt16_divNoInline(3, 2));
  if (v0) {
    return instDecidableEqUInt16(1, 1);
  } else {
    return v0;
  }
})();
export const TestUInt16_test1_0__shouldBeTrue = (() => {
  const v0 = instDecidableEqUInt16(0, TestUInt16_divNoInline(1, 0));
  if (v0) {
    return instDecidableEqUInt16(0, 0);
  } else {
    return v0;
  }
})();
export const TestInt8_divNoInline = (v0, v1) => $lean_int8_div(v0, v1);
export const TestInt8_test3m2_shouldBeTrue = (() => {
  const v0 = 3;
  const v1 = $lean_int8_neg(2);
  const v2 = $lean_int8_div(v0, v1);
  const v3 = instDecidableEqInt8(v2, TestInt8_divNoInline(v0, v1));
  if (v3) {
    return instDecidableEqInt8(v2, $lean_int8_neg(1));
  } else {
    return v3;
  }
})();
export const TestInt8_test3_2_shouldBeTrue = (() => {
  const v0 = 3;
  const v1 = 2;
  const v2 = $lean_int8_div(v0, v1);
  const v3 = instDecidableEqInt8(v2, TestInt8_divNoInline(v0, v1));
  if (v3) {
    return instDecidableEqInt8(v2, 1);
  } else {
    return v3;
  }
})();
export const TestInt8_test1_0_shouldBeTrue = (() => {
  const v0 = 1;
  const v1 = 0;
  const v2 = $lean_int8_div(v0, v1);
  const v3 = instDecidableEqInt8(v2, TestInt8_divNoInline(v0, v1));
  if (v3) {
    return instDecidableEqInt8(v2, v1);
  } else {
    return v3;
  }
})();
export const TestInt32_divNoInline = (v0, v1) => $lean_int32_div(v0, v1);
export const TestInt32_test3m2_shouldBeTrue = (() => {
  const v0 = 3;
  const v1 = $lean_int32_neg(2);
  const v2 = $lean_int32_div(v0, v1);
  const v3 = instDecidableEqInt32(v2, TestInt32_divNoInline(v0, v1));
  if (v3) {
    return instDecidableEqInt32(v2, $lean_int32_neg(1));
  } else {
    return v3;
  }
})();
export const TestInt32_test3_2_shouldBeTrue = (() => {
  const v0 = 3;
  const v1 = 2;
  const v2 = $lean_int32_div(v0, v1);
  const v3 = instDecidableEqInt32(v2, TestInt32_divNoInline(v0, v1));
  if (v3) {
    return instDecidableEqInt32(v2, 1);
  } else {
    return v3;
  }
})();
export const TestInt32_test1_0_shouldBeTrue = (() => {
  const v0 = 1;
  const v1 = 0;
  const v2 = $lean_int32_div(v0, v1);
  const v3 = instDecidableEqInt32(v2, TestInt32_divNoInline(v0, v1));
  if (v3) {
    return instDecidableEqInt32(v2, v1);
  } else {
    return v3;
  }
})();
export const TestInt16_divNoInline = (v0, v1) => $lean_int16_div(v0, v1);
export const TestInt16_test3m2_shouldBeTrue = (() => {
  const v0 = 3;
  const v1 = $lean_int16_neg(2);
  const v2 = $lean_int16_div(v0, v1);
  const v3 = instDecidableEqInt16(v2, TestInt16_divNoInline(v0, v1));
  if (v3) {
    return instDecidableEqInt16(v2, $lean_int16_neg(1));
  } else {
    return v3;
  }
})();
export const TestInt16_test3_2_shouldBeTrue = (() => {
  const v0 = 3;
  const v1 = 2;
  const v2 = $lean_int16_div(v0, v1);
  const v3 = instDecidableEqInt16(v2, TestInt16_divNoInline(v0, v1));
  if (v3) {
    return instDecidableEqInt16(v2, 1);
  } else {
    return v3;
  }
})();
export const TestInt16_test1_0_shouldBeTrue = (() => {
  const v0 = 1;
  const v1 = 0;
  const v2 = $lean_int16_div(v0, v1);
  const v3 = instDecidableEqInt16(v2, TestInt16_divNoInline(v0, v1));
  if (v3) {
    return instDecidableEqInt16(v2, v1);
  } else {
    return v3;
  }
})();
