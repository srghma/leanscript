import {
  $lean_int16_add,
  $lean_int16_dec_le,
  $lean_int16_dec_lt,
  $lean_int16_div,
  $lean_int16_mul,
  $lean_int16_neg,
  $lean_int16_of_nat,
  $lean_int16_sub,
  $lean_int32_add,
  $lean_int32_dec_le,
  $lean_int32_dec_lt,
  $lean_int32_div,
  $lean_int32_mul,
  $lean_int32_neg,
  $lean_int32_of_nat,
  $lean_int32_sub,
  $lean_int8_add,
  $lean_int8_dec_le,
  $lean_int8_dec_lt,
  $lean_int8_div,
  $lean_int8_mul,
  $lean_int8_neg,
  $lean_int8_of_nat,
  $lean_int8_sub,
  $lean_uint16_add,
  $lean_uint16_div,
  $lean_uint16_mul,
  $lean_uint16_neg,
  $lean_uint16_shift_left,
  $lean_uint16_shift_right,
  $lean_uint16_sub,
  $lean_uint32_add,
  $lean_uint32_div,
  $lean_uint32_mul,
  $lean_uint32_neg,
  $lean_uint32_shift_left,
  $lean_uint32_shift_right,
  $lean_uint32_sub,
  $lean_uint8_add,
  $lean_uint8_div,
  $lean_uint8_mul,
  $lean_uint8_neg,
  $lean_uint8_shift_left,
  $lean_uint8_shift_right,
  $lean_uint8_sub,
  instDecidableEqInt16,
  instDecidableEqInt32,
  instDecidableEqInt8,
  instDecidableEqUInt16,
  instDecidableEqUInt32,
  instDecidableEqUInt8,
} from "../runtime/lean_runtime_non_configurable.mjs";
export const TestUInt8_test9 = (() => {
  const v0 = $lean_uint8_neg(1);
  return [
    ...[
      ...[...[...[...[...[], 1], 2], 2], $lean_uint8_neg(2)],
      $lean_uint8_shift_left(v0, 1),
    ],
    $lean_uint8_mul(v0, v0),
  ];
})();
export const TestUInt8_test8 = (() => {
  const v0 = (v0, v1) => v1 <= v0;
  const v1 = $lean_uint8_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1, 1)], v0(1, 2)], v0(2, 1)],
        v0(1, $lean_uint8_neg(2)),
      ],
      v0(v1, 2),
    ],
    v0(v1, v1),
  ];
})();
export const TestUInt8_test7 = (() => {
  const v0 = (v0, v1) => v0 <= v1;
  const v1 = $lean_uint8_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1, 1)], v0(1, 2)], v0(2, 1)],
        v0(1, $lean_uint8_neg(2)),
      ],
      v0(v1, 2),
    ],
    v0(v1, v1),
  ];
})();
export const TestUInt8_test6 = (() => {
  const v0 = (v0, v1) => v1 < v0;
  const v1 = $lean_uint8_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1, 1)], v0(1, 2)], v0(2, 1)],
        v0(1, $lean_uint8_neg(2)),
      ],
      v0(v1, 2),
    ],
    v0(v1, v1),
  ];
})();
export const TestUInt8_test5 = (() => {
  const v0 = (v0, v1) => v0 < v1;
  const v1 = $lean_uint8_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1, 1)], v0(1, 2)], v0(2, 1)],
        v0(1, $lean_uint8_neg(2)),
      ],
      v0(v1, 2),
    ],
    v0(v1, v1),
  ];
})();
export const TestUInt8_test4 = (() => {
  const v0 = (v0, v1) => {
    if (instDecidableEqUInt8(v0, v1)) {
      return false;
    } else {
      return true;
    }
  };
  const v1 = $lean_uint8_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1, 1)], v0(1, 2)], v0(2, 1)],
        v0(1, $lean_uint8_neg(2)),
      ],
      v0(v1, 2),
    ],
    v0(v1, v1),
  ];
})();
export const TestUInt8_test3 = (() => {
  const v0 = (v0, v1) => instDecidableEqUInt8(v0, v1);
  const v1 = $lean_uint8_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1, 1)], v0(1, 2)], v0(2, 1)],
        v0(1, $lean_uint8_neg(2)),
      ],
      v0(v1, 2),
    ],
    v0(v1, v1),
  ];
})();
export const TestUInt8_test2 = (() => {
  const v0 = $lean_uint8_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], 0], 255], 1],
        $lean_uint8_sub(1, $lean_uint8_neg(2)),
      ],
      $lean_uint8_sub(v0, 2),
    ],
    $lean_uint8_sub(v0, v0),
  ];
})();
export const TestUInt8_test11 = (() => {
  const v0 = $lean_uint8_neg(1);
  return [...[...[], v0], $lean_uint8_neg(v0)];
})();
export const TestUInt8_test10 = (() => {
  const v0 = $lean_uint8_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], 1], 0], 2],
        $lean_uint8_div(1, $lean_uint8_neg(2)),
      ],
      $lean_uint8_shift_right(v0, 1),
    ],
    $lean_uint8_div(v0, v0),
  ];
})();
export const TestUInt8_test1 = (() => {
  const v0 = $lean_uint8_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], 2], 3], 3],
        $lean_uint8_add(1, $lean_uint8_neg(2)),
      ],
      $lean_uint8_add(v0, 2),
    ],
    $lean_uint8_add(v0, v0),
  ];
})();
export const TestUInt8_intValues = (v0) => {
  const v1 = $lean_uint8_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1, 1)], v0(1, 2)], v0(2, 1)],
        v0(1, $lean_uint8_neg(2)),
      ],
      v0(v1, 2),
    ],
    v0(v1, v1),
  ];
};
export const TestUInt32_test9 = (() => {
  const v0 = $lean_uint32_neg(1);
  return [
    ...[
      ...[...[...[...[...[], 1], 2], 2], $lean_uint32_neg(2)],
      $lean_uint32_shift_left(v0, 1),
    ],
    $lean_uint32_mul(v0, v0),
  ];
})();
export const TestUInt32_test8 = (() => {
  const v0 = (v0, v1) => v1 <= v0;
  const v1 = $lean_uint32_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1, 1)], v0(1, 2)], v0(2, 1)],
        v0(1, $lean_uint32_neg(2)),
      ],
      v0(v1, 2),
    ],
    v0(v1, v1),
  ];
})();
export const TestUInt32_test7 = (() => {
  const v0 = (v0, v1) => v0 <= v1;
  const v1 = $lean_uint32_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1, 1)], v0(1, 2)], v0(2, 1)],
        v0(1, $lean_uint32_neg(2)),
      ],
      v0(v1, 2),
    ],
    v0(v1, v1),
  ];
})();
export const TestUInt32_test6 = (() => {
  const v0 = (v0, v1) => v1 < v0;
  const v1 = $lean_uint32_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1, 1)], v0(1, 2)], v0(2, 1)],
        v0(1, $lean_uint32_neg(2)),
      ],
      v0(v1, 2),
    ],
    v0(v1, v1),
  ];
})();
export const TestUInt32_test5 = (() => {
  const v0 = (v0, v1) => v0 < v1;
  const v1 = $lean_uint32_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1, 1)], v0(1, 2)], v0(2, 1)],
        v0(1, $lean_uint32_neg(2)),
      ],
      v0(v1, 2),
    ],
    v0(v1, v1),
  ];
})();
export const TestUInt32_test4 = (() => {
  const v0 = (v0, v1) => {
    if (instDecidableEqUInt32(v0, v1)) {
      return false;
    } else {
      return true;
    }
  };
  const v1 = $lean_uint32_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1, 1)], v0(1, 2)], v0(2, 1)],
        v0(1, $lean_uint32_neg(2)),
      ],
      v0(v1, 2),
    ],
    v0(v1, v1),
  ];
})();
export const TestUInt32_test3 = (() => {
  const v0 = (v0, v1) => instDecidableEqUInt32(v0, v1);
  const v1 = $lean_uint32_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1, 1)], v0(1, 2)], v0(2, 1)],
        v0(1, $lean_uint32_neg(2)),
      ],
      v0(v1, 2),
    ],
    v0(v1, v1),
  ];
})();
export const TestUInt32_test2 = (() => {
  const v0 = $lean_uint32_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], 0], 4294967295], 1],
        $lean_uint32_sub(1, $lean_uint32_neg(2)),
      ],
      $lean_uint32_sub(v0, 2),
    ],
    $lean_uint32_sub(v0, v0),
  ];
})();
export const TestUInt32_test11 = (() => {
  const v0 = $lean_uint32_neg(1);
  return [...[...[], v0], $lean_uint32_neg(v0)];
})();
export const TestUInt32_test10 = (() => {
  const v0 = $lean_uint32_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], 1], 0], 2],
        $lean_uint32_div(1, $lean_uint32_neg(2)),
      ],
      $lean_uint32_shift_right(v0, 1),
    ],
    $lean_uint32_div(v0, v0),
  ];
})();
export const TestUInt32_test1 = (() => {
  const v0 = $lean_uint32_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], 2], 3], 3],
        $lean_uint32_add(1, $lean_uint32_neg(2)),
      ],
      $lean_uint32_add(v0, 2),
    ],
    $lean_uint32_add(v0, v0),
  ];
})();
export const TestUInt32_intValues = (v0) => {
  const v1 = $lean_uint32_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1, 1)], v0(1, 2)], v0(2, 1)],
        v0(1, $lean_uint32_neg(2)),
      ],
      v0(v1, 2),
    ],
    v0(v1, v1),
  ];
};
export const TestUInt16_test9 = (() => {
  const v0 = $lean_uint16_neg(1);
  return [
    ...[
      ...[...[...[...[...[], 1], 2], 2], $lean_uint16_neg(2)],
      $lean_uint16_shift_left(v0, 1),
    ],
    $lean_uint16_mul(v0, v0),
  ];
})();
export const TestUInt16_test8 = (() => {
  const v0 = (v0, v1) => v1 <= v0;
  const v1 = $lean_uint16_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1, 1)], v0(1, 2)], v0(2, 1)],
        v0(1, $lean_uint16_neg(2)),
      ],
      v0(v1, 2),
    ],
    v0(v1, v1),
  ];
})();
export const TestUInt16_test7 = (() => {
  const v0 = (v0, v1) => v0 <= v1;
  const v1 = $lean_uint16_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1, 1)], v0(1, 2)], v0(2, 1)],
        v0(1, $lean_uint16_neg(2)),
      ],
      v0(v1, 2),
    ],
    v0(v1, v1),
  ];
})();
export const TestUInt16_test6 = (() => {
  const v0 = (v0, v1) => v1 < v0;
  const v1 = $lean_uint16_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1, 1)], v0(1, 2)], v0(2, 1)],
        v0(1, $lean_uint16_neg(2)),
      ],
      v0(v1, 2),
    ],
    v0(v1, v1),
  ];
})();
export const TestUInt16_test5 = (() => {
  const v0 = (v0, v1) => v0 < v1;
  const v1 = $lean_uint16_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1, 1)], v0(1, 2)], v0(2, 1)],
        v0(1, $lean_uint16_neg(2)),
      ],
      v0(v1, 2),
    ],
    v0(v1, v1),
  ];
})();
export const TestUInt16_test4 = (() => {
  const v0 = (v0, v1) => {
    if (instDecidableEqUInt16(v0, v1)) {
      return false;
    } else {
      return true;
    }
  };
  const v1 = $lean_uint16_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1, 1)], v0(1, 2)], v0(2, 1)],
        v0(1, $lean_uint16_neg(2)),
      ],
      v0(v1, 2),
    ],
    v0(v1, v1),
  ];
})();
export const TestUInt16_test3 = (() => {
  const v0 = (v0, v1) => instDecidableEqUInt16(v0, v1);
  const v1 = $lean_uint16_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1, 1)], v0(1, 2)], v0(2, 1)],
        v0(1, $lean_uint16_neg(2)),
      ],
      v0(v1, 2),
    ],
    v0(v1, v1),
  ];
})();
export const TestUInt16_test2 = (() => {
  const v0 = $lean_uint16_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], 0], 65535], 1],
        $lean_uint16_sub(1, $lean_uint16_neg(2)),
      ],
      $lean_uint16_sub(v0, 2),
    ],
    $lean_uint16_sub(v0, v0),
  ];
})();
export const TestUInt16_test11 = (() => {
  const v0 = $lean_uint16_neg(1);
  return [...[...[], v0], $lean_uint16_neg(v0)];
})();
export const TestUInt16_test10 = (() => {
  const v0 = $lean_uint16_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], 1], 0], 2],
        $lean_uint16_div(1, $lean_uint16_neg(2)),
      ],
      $lean_uint16_shift_right(v0, 1),
    ],
    $lean_uint16_div(v0, v0),
  ];
})();
export const TestUInt16_test1 = (() => {
  const v0 = $lean_uint16_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], 2], 3], 3],
        $lean_uint16_add(1, $lean_uint16_neg(2)),
      ],
      $lean_uint16_add(v0, 2),
    ],
    $lean_uint16_add(v0, v0),
  ];
})();
export const TestUInt16_intValues = (v0) => {
  const v1 = $lean_uint16_neg(1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1, 1)], v0(1, 2)], v0(2, 1)],
        v0(1, $lean_uint16_neg(2)),
      ],
      v0(v1, 2),
    ],
    v0(v1, v1),
  ];
};
export const TestInt8_test9 = (() => {
  const v0 = 1;
  const v1 = 2;
  const v2 = $lean_int8_neg(v0);
  return [
    ...[
      ...[
        ...[
          ...[...[...[], $lean_int8_mul(v0, v0)], $lean_int8_mul(v0, v1)],
          $lean_int8_mul(v1, v0),
        ],
        $lean_int8_mul(v0, $lean_int8_neg(v1)),
      ],
      $lean_int8_mul(v2, v1),
    ],
    $lean_int8_mul(v2, v2),
  ];
})();
export const TestInt8_test8 = (() => {
  const v0 = (v0, v1) => $lean_int8_dec_le(v1, v0);
  const v1 = 1;
  const v2 = 2;
  const v3 = $lean_int8_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_int8_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestInt8_test7 = (() => {
  const v0 = (v0, v1) => $lean_int8_dec_le(v0, v1);
  const v1 = 1;
  const v2 = 2;
  const v3 = $lean_int8_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_int8_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestInt8_test6 = (() => {
  const v0 = (v0, v1) => $lean_int8_dec_lt(v1, v0);
  const v1 = 1;
  const v2 = 2;
  const v3 = $lean_int8_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_int8_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestInt8_test5 = (() => {
  const v0 = (v0, v1) => $lean_int8_dec_lt(v0, v1);
  const v1 = 1;
  const v2 = 2;
  const v3 = $lean_int8_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_int8_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestInt8_test4 = (() => {
  const v0 = (v0, v1) => {
    if (instDecidableEqInt8(v0, v1)) {
      return false;
    } else {
      return true;
    }
  };
  const v1 = 1;
  const v2 = 2;
  const v3 = $lean_int8_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_int8_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestInt8_test3 = (() => {
  const v0 = (v0, v1) => instDecidableEqInt8(v0, v1);
  const v1 = 1;
  const v2 = 2;
  const v3 = $lean_int8_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_int8_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestInt8_test2 = (() => {
  const v0 = 1;
  const v1 = 2;
  const v2 = $lean_int8_neg(v0);
  return [
    ...[
      ...[
        ...[
          ...[...[...[], $lean_int8_sub(v0, v0)], $lean_int8_sub(v0, v1)],
          $lean_int8_sub(v1, v0),
        ],
        $lean_int8_sub(v0, $lean_int8_neg(v1)),
      ],
      $lean_int8_sub(v2, v1),
    ],
    $lean_int8_sub(v2, v2),
  ];
})();
export const TestInt8_test11 = (() => {
  const v0 = $lean_int8_neg(1);
  return [...[...[], v0], $lean_int8_neg(v0)];
})();
export const TestInt8_test10 = (() => {
  const v0 = 1;
  const v1 = 2;
  const v2 = $lean_int8_neg(v0);
  return [
    ...[
      ...[
        ...[
          ...[...[...[], $lean_int8_div(v0, v0)], $lean_int8_div(v0, v1)],
          $lean_int8_div(v1, v0),
        ],
        $lean_int8_div(v0, $lean_int8_neg(v1)),
      ],
      $lean_int8_div(v2, v1),
    ],
    $lean_int8_div(v2, v2),
  ];
})();
export const TestInt8_test1 = (() => {
  const v0 = 1;
  const v1 = 2;
  const v2 = $lean_int8_neg(v0);
  return [
    ...[
      ...[
        ...[
          ...[...[...[], $lean_int8_add(v0, v0)], $lean_int8_add(v0, v1)],
          $lean_int8_add(v1, v0),
        ],
        $lean_int8_add(v0, $lean_int8_neg(v1)),
      ],
      $lean_int8_add(v2, v1),
    ],
    $lean_int8_add(v2, v2),
  ];
})();
export const TestInt8_intValues = (v0) => {
  const v1 = 1;
  const v2 = 2;
  const v3 = $lean_int8_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_int8_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
};
export const TestInt32_test9 = (() => {
  const v0 = 1;
  const v1 = 2;
  const v2 = $lean_int32_neg(v0);
  return [
    ...[
      ...[
        ...[
          ...[...[...[], $lean_int32_mul(v0, v0)], $lean_int32_mul(v0, v1)],
          $lean_int32_mul(v1, v0),
        ],
        $lean_int32_mul(v0, $lean_int32_neg(v1)),
      ],
      $lean_int32_mul(v2, v1),
    ],
    $lean_int32_mul(v2, v2),
  ];
})();
export const TestInt32_test8 = (() => {
  const v0 = (v0, v1) => $lean_int32_dec_le(v1, v0);
  const v1 = 1;
  const v2 = 2;
  const v3 = $lean_int32_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_int32_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestInt32_test7 = (() => {
  const v0 = (v0, v1) => $lean_int32_dec_le(v0, v1);
  const v1 = 1;
  const v2 = 2;
  const v3 = $lean_int32_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_int32_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestInt32_test6 = (() => {
  const v0 = (v0, v1) => $lean_int32_dec_lt(v1, v0);
  const v1 = 1;
  const v2 = 2;
  const v3 = $lean_int32_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_int32_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestInt32_test5 = (() => {
  const v0 = (v0, v1) => $lean_int32_dec_lt(v0, v1);
  const v1 = 1;
  const v2 = 2;
  const v3 = $lean_int32_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_int32_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestInt32_test4 = (() => {
  const v0 = (v0, v1) => {
    if (instDecidableEqInt32(v0, v1)) {
      return false;
    } else {
      return true;
    }
  };
  const v1 = 1;
  const v2 = 2;
  const v3 = $lean_int32_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_int32_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestInt32_test3 = (() => {
  const v0 = (v0, v1) => instDecidableEqInt32(v0, v1);
  const v1 = 1;
  const v2 = 2;
  const v3 = $lean_int32_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_int32_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestInt32_test2 = (() => {
  const v0 = 1;
  const v1 = 2;
  const v2 = $lean_int32_neg(v0);
  return [
    ...[
      ...[
        ...[
          ...[...[...[], $lean_int32_sub(v0, v0)], $lean_int32_sub(v0, v1)],
          $lean_int32_sub(v1, v0),
        ],
        $lean_int32_sub(v0, $lean_int32_neg(v1)),
      ],
      $lean_int32_sub(v2, v1),
    ],
    $lean_int32_sub(v2, v2),
  ];
})();
export const TestInt32_test11 = (() => {
  const v0 = $lean_int32_neg(1);
  return [...[...[], v0], $lean_int32_neg(v0)];
})();
export const TestInt32_test10 = (() => {
  const v0 = 1;
  const v1 = 2;
  const v2 = $lean_int32_neg(v0);
  return [
    ...[
      ...[
        ...[
          ...[...[...[], $lean_int32_div(v0, v0)], $lean_int32_div(v0, v1)],
          $lean_int32_div(v1, v0),
        ],
        $lean_int32_div(v0, $lean_int32_neg(v1)),
      ],
      $lean_int32_div(v2, v1),
    ],
    $lean_int32_div(v2, v2),
  ];
})();
export const TestInt32_test1 = (() => {
  const v0 = 1;
  const v1 = 2;
  const v2 = $lean_int32_neg(v0);
  return [
    ...[
      ...[
        ...[
          ...[...[...[], $lean_int32_add(v0, v0)], $lean_int32_add(v0, v1)],
          $lean_int32_add(v1, v0),
        ],
        $lean_int32_add(v0, $lean_int32_neg(v1)),
      ],
      $lean_int32_add(v2, v1),
    ],
    $lean_int32_add(v2, v2),
  ];
})();
export const TestInt32_intValues = (v0) => {
  const v1 = 1;
  const v2 = 2;
  const v3 = $lean_int32_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_int32_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
};
export const TestInt16_test9 = (() => {
  const v0 = 1;
  const v1 = 2;
  const v2 = $lean_int16_neg(v0);
  return [
    ...[
      ...[
        ...[
          ...[...[...[], $lean_int16_mul(v0, v0)], $lean_int16_mul(v0, v1)],
          $lean_int16_mul(v1, v0),
        ],
        $lean_int16_mul(v0, $lean_int16_neg(v1)),
      ],
      $lean_int16_mul(v2, v1),
    ],
    $lean_int16_mul(v2, v2),
  ];
})();
export const TestInt16_test8 = (() => {
  const v0 = (v0, v1) => $lean_int16_dec_le(v1, v0);
  const v1 = 1;
  const v2 = 2;
  const v3 = $lean_int16_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_int16_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestInt16_test7 = (() => {
  const v0 = (v0, v1) => $lean_int16_dec_le(v0, v1);
  const v1 = 1;
  const v2 = 2;
  const v3 = $lean_int16_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_int16_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestInt16_test6 = (() => {
  const v0 = (v0, v1) => $lean_int16_dec_lt(v1, v0);
  const v1 = 1;
  const v2 = 2;
  const v3 = $lean_int16_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_int16_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestInt16_test5 = (() => {
  const v0 = (v0, v1) => $lean_int16_dec_lt(v0, v1);
  const v1 = 1;
  const v2 = 2;
  const v3 = $lean_int16_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_int16_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestInt16_test4 = (() => {
  const v0 = (v0, v1) => {
    if (instDecidableEqInt16(v0, v1)) {
      return false;
    } else {
      return true;
    }
  };
  const v1 = 1;
  const v2 = 2;
  const v3 = $lean_int16_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_int16_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestInt16_test3 = (() => {
  const v0 = (v0, v1) => instDecidableEqInt16(v0, v1);
  const v1 = 1;
  const v2 = 2;
  const v3 = $lean_int16_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_int16_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestInt16_test2 = (() => {
  const v0 = 1;
  const v1 = 2;
  const v2 = $lean_int16_neg(v0);
  return [
    ...[
      ...[
        ...[
          ...[...[...[], $lean_int16_sub(v0, v0)], $lean_int16_sub(v0, v1)],
          $lean_int16_sub(v1, v0),
        ],
        $lean_int16_sub(v0, $lean_int16_neg(v1)),
      ],
      $lean_int16_sub(v2, v1),
    ],
    $lean_int16_sub(v2, v2),
  ];
})();
export const TestInt16_test11 = (() => {
  const v0 = $lean_int16_neg(1);
  return [...[...[], v0], $lean_int16_neg(v0)];
})();
export const TestInt16_test10 = (() => {
  const v0 = 1;
  const v1 = 2;
  const v2 = $lean_int16_neg(v0);
  return [
    ...[
      ...[
        ...[
          ...[...[...[], $lean_int16_div(v0, v0)], $lean_int16_div(v0, v1)],
          $lean_int16_div(v1, v0),
        ],
        $lean_int16_div(v0, $lean_int16_neg(v1)),
      ],
      $lean_int16_div(v2, v1),
    ],
    $lean_int16_div(v2, v2),
  ];
})();
export const TestInt16_test1 = (() => {
  const v0 = 1;
  const v1 = 2;
  const v2 = $lean_int16_neg(v0);
  return [
    ...[
      ...[
        ...[
          ...[...[...[], $lean_int16_add(v0, v0)], $lean_int16_add(v0, v1)],
          $lean_int16_add(v1, v0),
        ],
        $lean_int16_add(v0, $lean_int16_neg(v1)),
      ],
      $lean_int16_add(v2, v1),
    ],
    $lean_int16_add(v2, v2),
  ];
})();
export const TestInt16_intValues = (v0) => {
  const v1 = 1;
  const v2 = 2;
  const v3 = $lean_int16_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_int16_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
};
