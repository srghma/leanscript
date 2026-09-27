import {
  $lean_int16_complement,
  $lean_int16_land,
  $lean_int16_lor,
  $lean_int16_neg,
  $lean_int16_of_nat,
  $lean_int16_shift_left,
  $lean_int16_shift_right,
  $lean_int16_xor,
  $lean_int32_complement,
  $lean_int32_land,
  $lean_int32_lor,
  $lean_int32_neg,
  $lean_int32_of_nat,
  $lean_int32_shift_left,
  $lean_int32_shift_right,
  $lean_int32_xor,
  $lean_int8_complement,
  $lean_int8_land,
  $lean_int8_lor,
  $lean_int8_neg,
  $lean_int8_of_nat,
  $lean_int8_shift_left,
  $lean_int8_shift_right,
  $lean_int8_xor,
  $lean_uint16_complement,
  $lean_uint16_land,
  $lean_uint16_lor,
  $lean_uint16_neg,
  $lean_uint16_shift_left,
  $lean_uint16_shift_right,
  $lean_uint16_xor,
  $lean_uint32_complement,
  $lean_uint32_land,
  $lean_uint32_lor,
  $lean_uint32_neg,
  $lean_uint32_shift_left,
  $lean_uint32_shift_right,
  $lean_uint32_xor,
  $lean_uint8_complement,
  $lean_uint8_land,
  $lean_uint8_lor,
  $lean_uint8_neg,
  $lean_uint8_shift_left,
  $lean_uint8_shift_right,
  $lean_uint8_xor,
} from "../runtime/lean_runtime_non_configurable.mjs";
export const TestUInt8_xor = $lean_uint8_xor(15, 12);
export const TestUInt8_shiftRight = $lean_uint8_shift_right(
  $lean_uint8_neg(255),
  2,
);
export const TestUInt8_shiftLeft = $lean_uint8_shift_left(255, 2);
export const TestUInt8_lor = $lean_uint8_lor(16, 15);
export const TestUInt8_land = $lean_uint8_land(255, 8);
export const TestUInt8_complement = $lean_uint8_complement($lean_uint8_neg(3));
export const TestUInt32_xor = $lean_uint32_xor(15, 12);
export const TestUInt32_shiftRight = $lean_uint32_shift_right(
  $lean_uint32_neg(1023),
  2,
);
export const TestUInt32_shiftLeft = $lean_uint32_shift_left(1023, 2);
export const TestUInt32_lor = $lean_uint32_lor(16, 15);
export const TestUInt32_land = $lean_uint32_land(1023, 8);
export const TestUInt32_complement = $lean_uint32_complement(
  $lean_uint32_neg(3),
);
export const TestUInt16_xor = $lean_uint16_xor(15, 12);
export const TestUInt16_shiftRight = $lean_uint16_shift_right(
  $lean_uint16_neg(1023),
  2,
);
export const TestUInt16_shiftLeft = $lean_uint16_shift_left(1023, 2);
export const TestUInt16_lor = $lean_uint16_lor(16, 15);
export const TestUInt16_land = $lean_uint16_land(1023, 8);
export const TestUInt16_complement = $lean_uint16_complement(
  $lean_uint16_neg(3),
);
export const TestInt8_xor = $lean_int8_xor(15, 12);
export const TestInt8_shiftRight = $lean_int8_shift_right(
  $lean_int8_neg(-1),
  2,
);
export const TestInt8_shiftLeft = $lean_int8_shift_left(-1, 2);
export const TestInt8_lor = $lean_int8_lor(16, 15);
export const TestInt8_land = $lean_int8_land(-1, 8);
export const TestInt8_complement = $lean_int8_complement($lean_int8_neg(3));
export const TestInt32_xor = $lean_int32_xor(15, 12);
export const TestInt32_shiftRight = $lean_int32_shift_right(
  $lean_int32_neg(1023),
  2,
);
export const TestInt32_shiftLeft = $lean_int32_shift_left(1023, 2);
export const TestInt32_lor = $lean_int32_lor(16, 15);
export const TestInt32_land = $lean_int32_land(1023, 8);
export const TestInt32_complement = $lean_int32_complement($lean_int32_neg(3));
export const TestInt16_xor = $lean_int16_xor(15, 12);
export const TestInt16_shiftRight = $lean_int16_shift_right(
  $lean_int16_neg(1023),
  2,
);
export const TestInt16_shiftLeft = $lean_int16_shift_left(1023, 2);
export const TestInt16_lor = $lean_int16_lor(16, 15);
export const TestInt16_land = $lean_int16_land(1023, 8);
export const TestInt16_complement = $lean_int16_complement($lean_int16_neg(3));
