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
  $lean_uint64_shift_left,
  $lean_uint64_shift_right,
  $lean_uint64_sub,
} from "../runtime/lean_runtime_uint64_bigint.mjs";
import {
  $lean_int64_add,
  $lean_int64_div,
  $lean_int64_mul,
  $lean_int64_neg,
  $lean_int64_of_nat,
  $lean_int64_sub,
} from "../runtime/lean_runtime_int64_bigint.mjs";
import {
  $lean_isize_add,
  $lean_isize_div,
  $lean_isize_mul,
  $lean_isize_neg,
  $lean_isize_of_nat,
  $lean_isize_sub,
} from "../runtime/lean_runtime_isize_bigint.mjs";
export const TestUSize_test9 = (() => {
  const v0 = $lean_usize_neg(1n);
  return [
    ...[
      ...[
        ...[
          ...[...[...[], $lean_usize_mul(1n, 1n)], $lean_usize_mul(1n, 2n)],
          $lean_usize_mul(2n, 1n),
        ],
        $lean_usize_mul(1n, $lean_usize_neg(2n)),
      ],
      $lean_usize_mul(v0, 2n),
    ],
    $lean_usize_mul(v0, v0),
  ];
})();
export const TestUSize_test8 = (() => {
  const v0 = (v0, v1) => v1 <= v0;
  const v1 = $lean_usize_neg(1n);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1n, 1n)], v0(1n, 2n)], v0(2n, 1n)],
        v0(1n, $lean_usize_neg(2n)),
      ],
      v0(v1, 2n),
    ],
    v0(v1, v1),
  ];
})();
export const TestUSize_test7 = (() => {
  const v0 = (v0, v1) => v0 <= v1;
  const v1 = $lean_usize_neg(1n);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1n, 1n)], v0(1n, 2n)], v0(2n, 1n)],
        v0(1n, $lean_usize_neg(2n)),
      ],
      v0(v1, 2n),
    ],
    v0(v1, v1),
  ];
})();
export const TestUSize_test6 = (() => {
  const v0 = (v0, v1) => v1 < v0;
  const v1 = $lean_usize_neg(1n);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1n, 1n)], v0(1n, 2n)], v0(2n, 1n)],
        v0(1n, $lean_usize_neg(2n)),
      ],
      v0(v1, 2n),
    ],
    v0(v1, v1),
  ];
})();
export const TestUSize_test5 = (() => {
  const v0 = (v0, v1) => v0 < v1;
  const v1 = $lean_usize_neg(1n);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1n, 1n)], v0(1n, 2n)], v0(2n, 1n)],
        v0(1n, $lean_usize_neg(2n)),
      ],
      v0(v1, 2n),
    ],
    v0(v1, v1),
  ];
})();
export const TestUSize_test4 = (() => {
  const v0 = (v0, v1) => {
    if (instDecidableEqUSize(v0, v1)) {
      return false;
    } else {
      return true;
    }
  };
  const v1 = $lean_usize_neg(1n);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1n, 1n)], v0(1n, 2n)], v0(2n, 1n)],
        v0(1n, $lean_usize_neg(2n)),
      ],
      v0(v1, 2n),
    ],
    v0(v1, v1),
  ];
})();
export const TestUSize_test3 = (() => {
  const v0 = (v0, v1) => instDecidableEqUSize(v0, v1);
  const v1 = $lean_usize_neg(1n);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1n, 1n)], v0(1n, 2n)], v0(2n, 1n)],
        v0(1n, $lean_usize_neg(2n)),
      ],
      v0(v1, 2n),
    ],
    v0(v1, v1),
  ];
})();
export const TestUSize_test2 = (() => {
  const v0 = $lean_usize_neg(1n);
  return [
    ...[
      ...[
        ...[
          ...[...[...[], $lean_usize_sub(1n, 1n)], $lean_usize_sub(1n, 2n)],
          $lean_usize_sub(2n, 1n),
        ],
        $lean_usize_sub(1n, $lean_usize_neg(2n)),
      ],
      $lean_usize_sub(v0, 2n),
    ],
    $lean_usize_sub(v0, v0),
  ];
})();
export const TestUSize_test11 = (() => {
  const v0 = $lean_usize_neg(1n);
  return [...[...[], v0], $lean_usize_neg(v0)];
})();
export const TestUSize_test10 = (() => {
  const v0 = $lean_usize_neg(1n);
  return [
    ...[
      ...[
        ...[
          ...[...[...[], $lean_usize_div(1n, 1n)], $lean_usize_div(1n, 2n)],
          $lean_usize_div(2n, 1n),
        ],
        $lean_usize_div(1n, $lean_usize_neg(2n)),
      ],
      $lean_usize_div(v0, 2n),
    ],
    $lean_usize_div(v0, v0),
  ];
})();
export const TestUSize_test1 = (() => {
  const v0 = $lean_usize_neg(1n);
  return [
    ...[
      ...[
        ...[
          ...[...[...[], $lean_usize_add(1n, 1n)], $lean_usize_add(1n, 2n)],
          $lean_usize_add(2n, 1n),
        ],
        $lean_usize_add(1n, $lean_usize_neg(2n)),
      ],
      $lean_usize_add(v0, 2n),
    ],
    $lean_usize_add(v0, v0),
  ];
})();
export const TestUSize_intValues = (v0) => {
  const v1 = $lean_usize_neg(1n);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1n, 1n)], v0(1n, 2n)], v0(2n, 1n)],
        v0(1n, $lean_usize_neg(2n)),
      ],
      v0(v1, 2n),
    ],
    v0(v1, v1),
  ];
};
export const TestUInt64_test9 = (() => {
  const v0 = $lean_uint64_neg(1n);
  return [
    ...[
      ...[...[...[...[...[], 1n], 2n], 2n], $lean_uint64_neg(2n)],
      $lean_uint64_shift_left(v0, 1n),
    ],
    $lean_uint64_mul(v0, v0),
  ];
})();
export const TestUInt64_test8 = (() => {
  const v0 = (v0, v1) => v1 <= v0;
  const v1 = $lean_uint64_neg(1n);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1n, 1n)], v0(1n, 2n)], v0(2n, 1n)],
        v0(1n, $lean_uint64_neg(2n)),
      ],
      v0(v1, 2n),
    ],
    v0(v1, v1),
  ];
})();
export const TestUInt64_test7 = (() => {
  const v0 = (v0, v1) => v0 <= v1;
  const v1 = $lean_uint64_neg(1n);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1n, 1n)], v0(1n, 2n)], v0(2n, 1n)],
        v0(1n, $lean_uint64_neg(2n)),
      ],
      v0(v1, 2n),
    ],
    v0(v1, v1),
  ];
})();
export const TestUInt64_test6 = (() => {
  const v0 = (v0, v1) => v1 < v0;
  const v1 = $lean_uint64_neg(1n);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1n, 1n)], v0(1n, 2n)], v0(2n, 1n)],
        v0(1n, $lean_uint64_neg(2n)),
      ],
      v0(v1, 2n),
    ],
    v0(v1, v1),
  ];
})();
export const TestUInt64_test5 = (() => {
  const v0 = (v0, v1) => v0 < v1;
  const v1 = $lean_uint64_neg(1n);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1n, 1n)], v0(1n, 2n)], v0(2n, 1n)],
        v0(1n, $lean_uint64_neg(2n)),
      ],
      v0(v1, 2n),
    ],
    v0(v1, v1),
  ];
})();
export const TestUInt64_test4 = (() => {
  const v0 = (v0, v1) => {
    if (instDecidableEqUInt64(v0, v1)) {
      return false;
    } else {
      return true;
    }
  };
  const v1 = $lean_uint64_neg(1n);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1n, 1n)], v0(1n, 2n)], v0(2n, 1n)],
        v0(1n, $lean_uint64_neg(2n)),
      ],
      v0(v1, 2n),
    ],
    v0(v1, v1),
  ];
})();
export const TestUInt64_test3 = (() => {
  const v0 = (v0, v1) => instDecidableEqUInt64(v0, v1);
  const v1 = $lean_uint64_neg(1n);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1n, 1n)], v0(1n, 2n)], v0(2n, 1n)],
        v0(1n, $lean_uint64_neg(2n)),
      ],
      v0(v1, 2n),
    ],
    v0(v1, v1),
  ];
})();
export const TestUInt64_test2 = (() => {
  const v0 = $lean_uint64_neg(1n);
  return [
    ...[
      ...[
        ...[...[...[...[], 0n], 18446744073709551615n], 1n],
        $lean_uint64_sub(1n, $lean_uint64_neg(2n)),
      ],
      $lean_uint64_sub(v0, 2n),
    ],
    $lean_uint64_sub(v0, v0),
  ];
})();
export const TestUInt64_test11 = (() => {
  const v0 = $lean_uint64_neg(1n);
  return [...[...[], v0], $lean_uint64_neg(v0)];
})();
export const TestUInt64_test10 = (() => {
  const v0 = $lean_uint64_neg(1n);
  return [
    ...[
      ...[
        ...[...[...[...[], 1n], 0n], 2n],
        $lean_uint64_div(1n, $lean_uint64_neg(2n)),
      ],
      $lean_uint64_shift_right(v0, 1n),
    ],
    $lean_uint64_div(v0, v0),
  ];
})();
export const TestUInt64_test1 = (() => {
  const v0 = $lean_uint64_neg(1n);
  return [
    ...[
      ...[
        ...[...[...[...[], 2n], 3n], 3n],
        $lean_uint64_add(1n, $lean_uint64_neg(2n)),
      ],
      $lean_uint64_add(v0, 2n),
    ],
    $lean_uint64_add(v0, v0),
  ];
})();
export const TestUInt64_intValues = (v0) => {
  const v1 = $lean_uint64_neg(1n);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1n, 1n)], v0(1n, 2n)], v0(2n, 1n)],
        v0(1n, $lean_uint64_neg(2n)),
      ],
      v0(v1, 2n),
    ],
    v0(v1, v1),
  ];
};
export const TestNat_test9 = [
  ...[...[...[...[...[...[], 1n], 2n], 2n], 0n], 0n],
  0n,
];
export const TestNat_test8 = (() => {
  const v0 = (v0, v1) => v1 <= v0;
  return [
    ...[
      ...[...[...[...[...[], v0(1n, 1n)], v0(1n, 2n)], v0(2n, 1n)], v0(1n, 0n)],
      v0(0n, 2n),
    ],
    v0(0n, 0n),
  ];
})();
export const TestNat_test7 = (() => {
  const v0 = (v0, v1) => v0 <= v1;
  return [
    ...[
      ...[...[...[...[...[], v0(1n, 1n)], v0(1n, 2n)], v0(2n, 1n)], v0(1n, 0n)],
      v0(0n, 2n),
    ],
    v0(0n, 0n),
  ];
})();
export const TestNat_test6 = (() => {
  const v0 = (v0, v1) => v1 < v0;
  return [
    ...[
      ...[...[...[...[...[], v0(1n, 1n)], v0(1n, 2n)], v0(2n, 1n)], v0(1n, 0n)],
      v0(0n, 2n),
    ],
    v0(0n, 0n),
  ];
})();
export const TestNat_test5 = (() => {
  const v0 = (v0, v1) => v0 < v1;
  return [
    ...[
      ...[...[...[...[...[], v0(1n, 1n)], v0(1n, 2n)], v0(2n, 1n)], v0(1n, 0n)],
      v0(0n, 2n),
    ],
    v0(0n, 0n),
  ];
})();
export const TestNat_test4 = (() => {
  const v0 = (v0, v1) => {
    if (v0 === v1) {
      return false;
    } else {
      return true;
    }
  };
  return [
    ...[
      ...[...[...[...[...[], v0(1n, 1n)], v0(1n, 2n)], v0(2n, 1n)], v0(1n, 0n)],
      v0(0n, 2n),
    ],
    v0(0n, 0n),
  ];
})();
export const TestNat_test3 = (() => {
  const v0 = (v0, v1) => v0 === v1;
  return [
    ...[
      ...[...[...[...[...[], v0(1n, 1n)], v0(1n, 2n)], v0(2n, 1n)], v0(1n, 0n)],
      v0(0n, 2n),
    ],
    v0(0n, 0n),
  ];
})();
export const TestNat_test2 = [
  ...[...[...[...[...[...[], 0n], 0n], 1n], 1n], 0n],
  0n,
];
export const TestNat_test10 = [
  ...[...[...[...[...[...[], 1n], 0n], 2n], 0n], 0n],
  0n,
];
export const TestNat_test1 = [
  ...[...[...[...[...[...[], 2n], 3n], 3n], 1n], 2n],
  0n,
];
export const TestNat_intValues = (
  v0,
) => [
  ...[
    ...[...[...[...[...[], v0(1n, 1n)], v0(1n, 2n)], v0(2n, 1n)], v0(1n, 0n)],
    v0(0n, 2n),
  ],
  v0(0n, 0n),
];
export const TestInt64_test9 = (() => {
  const v0 = $lean_int64_of_nat(1n);
  const v1 = $lean_int64_of_nat(2n);
  const v2 = $lean_int64_neg(v0);
  return [
    ...[
      ...[
        ...[
          ...[...[...[], $lean_int64_mul(v0, v0)], $lean_int64_mul(v0, v1)],
          $lean_int64_mul(v1, v0),
        ],
        $lean_int64_mul(v0, $lean_int64_neg(v1)),
      ],
      $lean_int64_mul(v2, v1),
    ],
    $lean_int64_mul(v2, v2),
  ];
})();
export const TestInt64_test8 = (() => {
  const v0 = (v0, v1) => $lean_int64_dec_le(v1, v0);
  const v1 = $lean_int64_of_nat(1n);
  const v2 = $lean_int64_of_nat(2n);
  const v3 = $lean_int64_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_int64_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestInt64_test7 = (() => {
  const v0 = (v0, v1) => $lean_int64_dec_le(v0, v1);
  const v1 = $lean_int64_of_nat(1n);
  const v2 = $lean_int64_of_nat(2n);
  const v3 = $lean_int64_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_int64_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestInt64_test6 = (() => {
  const v0 = (v0, v1) => $lean_int64_dec_lt(v1, v0);
  const v1 = $lean_int64_of_nat(1n);
  const v2 = $lean_int64_of_nat(2n);
  const v3 = $lean_int64_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_int64_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestInt64_test5 = (() => {
  const v0 = (v0, v1) => $lean_int64_dec_lt(v0, v1);
  const v1 = $lean_int64_of_nat(1n);
  const v2 = $lean_int64_of_nat(2n);
  const v3 = $lean_int64_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_int64_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestInt64_test4 = (() => {
  const v0 = (v0, v1) => {
    if (instDecidableEqInt64(v0, v1)) {
      return false;
    } else {
      return true;
    }
  };
  const v1 = $lean_int64_of_nat(1n);
  const v2 = $lean_int64_of_nat(2n);
  const v3 = $lean_int64_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_int64_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestInt64_test3 = (() => {
  const v0 = (v0, v1) => instDecidableEqInt64(v0, v1);
  const v1 = $lean_int64_of_nat(1n);
  const v2 = $lean_int64_of_nat(2n);
  const v3 = $lean_int64_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_int64_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestInt64_test2 = (() => {
  const v0 = $lean_int64_of_nat(1n);
  const v1 = $lean_int64_of_nat(2n);
  const v2 = $lean_int64_neg(v0);
  return [
    ...[
      ...[
        ...[
          ...[...[...[], $lean_int64_sub(v0, v0)], $lean_int64_sub(v0, v1)],
          $lean_int64_sub(v1, v0),
        ],
        $lean_int64_sub(v0, $lean_int64_neg(v1)),
      ],
      $lean_int64_sub(v2, v1),
    ],
    $lean_int64_sub(v2, v2),
  ];
})();
export const TestInt64_test11 = (() => {
  const v0 = $lean_int64_neg($lean_int64_of_nat(1n));
  return [...[...[], v0], $lean_int64_neg(v0)];
})();
export const TestInt64_test10 = (() => {
  const v0 = $lean_int64_of_nat(1n);
  const v1 = $lean_int64_of_nat(2n);
  const v2 = $lean_int64_neg(v0);
  return [
    ...[
      ...[
        ...[
          ...[...[...[], $lean_int64_div(v0, v0)], $lean_int64_div(v0, v1)],
          $lean_int64_div(v1, v0),
        ],
        $lean_int64_div(v0, $lean_int64_neg(v1)),
      ],
      $lean_int64_div(v2, v1),
    ],
    $lean_int64_div(v2, v2),
  ];
})();
export const TestInt64_test1 = (() => {
  const v0 = $lean_int64_of_nat(1n);
  const v1 = $lean_int64_of_nat(2n);
  const v2 = $lean_int64_neg(v0);
  return [
    ...[
      ...[
        ...[
          ...[...[...[], $lean_int64_add(v0, v0)], $lean_int64_add(v0, v1)],
          $lean_int64_add(v1, v0),
        ],
        $lean_int64_add(v0, $lean_int64_neg(v1)),
      ],
      $lean_int64_add(v2, v1),
    ],
    $lean_int64_add(v2, v2),
  ];
})();
export const TestInt64_intValues = (v0) => {
  const v1 = $lean_int64_of_nat(1n);
  const v2 = $lean_int64_of_nat(2n);
  const v3 = $lean_int64_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_int64_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
};
export const TestInt_test9 = (() => {
  const v0 = $lean_int_neg(1n);
  return [
    ...[
      ...[
        ...[...[...[...[], 1n * 1n], 1n * 2n], 2n * 1n],
        1n * $lean_int_neg(2n),
      ],
      v0 * 2n,
    ],
    v0 * v0,
  ];
})();
export const TestInt_test8 = (() => {
  const v0 = (v0, v1) => v1 <= v0;
  const v1 = $lean_int_neg(1n);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1n, 1n)], v0(1n, 2n)], v0(2n, 1n)],
        v0(1n, $lean_int_neg(2n)),
      ],
      v0(v1, 2n),
    ],
    v0(v1, v1),
  ];
})();
export const TestInt_test7 = (() => {
  const v0 = (v0, v1) => v0 <= v1;
  const v1 = $lean_int_neg(1n);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1n, 1n)], v0(1n, 2n)], v0(2n, 1n)],
        v0(1n, $lean_int_neg(2n)),
      ],
      v0(v1, 2n),
    ],
    v0(v1, v1),
  ];
})();
export const TestInt_test6 = (() => {
  const v0 = (v0, v1) => v1 < v0;
  const v1 = $lean_int_neg(1n);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1n, 1n)], v0(1n, 2n)], v0(2n, 1n)],
        v0(1n, $lean_int_neg(2n)),
      ],
      v0(v1, 2n),
    ],
    v0(v1, v1),
  ];
})();
export const TestInt_test5 = (() => {
  const v0 = (v0, v1) => v0 < v1;
  const v1 = $lean_int_neg(1n);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1n, 1n)], v0(1n, 2n)], v0(2n, 1n)],
        v0(1n, $lean_int_neg(2n)),
      ],
      v0(v1, 2n),
    ],
    v0(v1, v1),
  ];
})();
export const TestInt_test4 = (() => {
  const v0 = (v0, v1) => {
    if (Int_instDecidableEq(v0, v1)) {
      return false;
    } else {
      return true;
    }
  };
  const v1 = $lean_int_neg(1n);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1n, 1n)], v0(1n, 2n)], v0(2n, 1n)],
        v0(1n, $lean_int_neg(2n)),
      ],
      v0(v1, 2n),
    ],
    v0(v1, v1),
  ];
})();
export const TestInt_test3 = (() => {
  const v0 = (v0, v1) => Int_instDecidableEq(v0, v1);
  const v1 = $lean_int_neg(1n);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1n, 1n)], v0(1n, 2n)], v0(2n, 1n)],
        v0(1n, $lean_int_neg(2n)),
      ],
      v0(v1, 2n),
    ],
    v0(v1, v1),
  ];
})();
export const TestInt_test2 = (() => {
  const v0 = $lean_int_neg(1n);
  return [
    ...[
      ...[
        ...[...[...[...[], 1n - 1n], 1n - 2n], 2n - 1n],
        1n - $lean_int_neg(2n),
      ],
      v0 - 2n,
    ],
    v0 - v0,
  ];
})();
export const TestInt_test11 = (() => {
  const v0 = $lean_int_neg(1n);
  return [...[...[], v0], $lean_int_neg(v0)];
})();
export const TestInt_test10 = (() => {
  const v0 = $lean_int_neg(1n);
  return [
    ...[
      ...[
        ...[
          ...[...[...[], $lean_int_ediv(1n, 1n)], $lean_int_ediv(1n, 2n)],
          $lean_int_ediv(2n, 1n),
        ],
        $lean_int_ediv(1n, $lean_int_neg(2n)),
      ],
      $lean_int_ediv(v0, 2n),
    ],
    $lean_int_ediv(v0, v0),
  ];
})();
export const TestInt_test1 = (() => {
  const v0 = $lean_int_neg(1n);
  return [
    ...[
      ...[
        ...[...[...[...[], 1n + 1n], 1n + 2n], 2n + 1n],
        1n + $lean_int_neg(2n),
      ],
      v0 + 2n,
    ],
    v0 + v0,
  ];
})();
export const TestInt_intValues = (v0) => {
  const v1 = $lean_int_neg(1n);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(1n, 1n)], v0(1n, 2n)], v0(2n, 1n)],
        v0(1n, $lean_int_neg(2n)),
      ],
      v0(v1, 2n),
    ],
    v0(v1, v1),
  ];
};
export const TestISize_test9 = (() => {
  const v0 = $lean_isize_of_nat(1n);
  const v1 = $lean_isize_of_nat(2n);
  const v2 = $lean_isize_neg(v0);
  return [
    ...[
      ...[
        ...[
          ...[...[...[], $lean_isize_mul(v0, v0)], $lean_isize_mul(v0, v1)],
          $lean_isize_mul(v1, v0),
        ],
        $lean_isize_mul(v0, $lean_isize_neg(v1)),
      ],
      $lean_isize_mul(v2, v1),
    ],
    $lean_isize_mul(v2, v2),
  ];
})();
export const TestISize_test8 = (() => {
  const v0 = (v0, v1) => $lean_isize_dec_le(v1, v0);
  const v1 = $lean_isize_of_nat(1n);
  const v2 = $lean_isize_of_nat(2n);
  const v3 = $lean_isize_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_isize_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestISize_test7 = (() => {
  const v0 = (v0, v1) => $lean_isize_dec_le(v0, v1);
  const v1 = $lean_isize_of_nat(1n);
  const v2 = $lean_isize_of_nat(2n);
  const v3 = $lean_isize_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_isize_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestISize_test6 = (() => {
  const v0 = (v0, v1) => $lean_isize_dec_lt(v1, v0);
  const v1 = $lean_isize_of_nat(1n);
  const v2 = $lean_isize_of_nat(2n);
  const v3 = $lean_isize_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_isize_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestISize_test5 = (() => {
  const v0 = (v0, v1) => $lean_isize_dec_lt(v0, v1);
  const v1 = $lean_isize_of_nat(1n);
  const v2 = $lean_isize_of_nat(2n);
  const v3 = $lean_isize_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_isize_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestISize_test4 = (() => {
  const v0 = (v0, v1) => {
    if (instDecidableEqISize(v0, v1)) {
      return false;
    } else {
      return true;
    }
  };
  const v1 = $lean_isize_of_nat(1n);
  const v2 = $lean_isize_of_nat(2n);
  const v3 = $lean_isize_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_isize_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestISize_test3 = (() => {
  const v0 = (v0, v1) => instDecidableEqISize(v0, v1);
  const v1 = $lean_isize_of_nat(1n);
  const v2 = $lean_isize_of_nat(2n);
  const v3 = $lean_isize_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_isize_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
})();
export const TestISize_test2 = (() => {
  const v0 = $lean_isize_of_nat(1n);
  const v1 = $lean_isize_of_nat(2n);
  const v2 = $lean_isize_neg(v0);
  return [
    ...[
      ...[
        ...[
          ...[...[...[], $lean_isize_sub(v0, v0)], $lean_isize_sub(v0, v1)],
          $lean_isize_sub(v1, v0),
        ],
        $lean_isize_sub(v0, $lean_isize_neg(v1)),
      ],
      $lean_isize_sub(v2, v1),
    ],
    $lean_isize_sub(v2, v2),
  ];
})();
export const TestISize_test11 = (() => {
  const v0 = $lean_isize_neg($lean_isize_of_nat(1n));
  return [...[...[], v0], $lean_isize_neg(v0)];
})();
export const TestISize_test10 = (() => {
  const v0 = $lean_isize_of_nat(1n);
  const v1 = $lean_isize_of_nat(2n);
  const v2 = $lean_isize_neg(v0);
  return [
    ...[
      ...[
        ...[
          ...[...[...[], $lean_isize_div(v0, v0)], $lean_isize_div(v0, v1)],
          $lean_isize_div(v1, v0),
        ],
        $lean_isize_div(v0, $lean_isize_neg(v1)),
      ],
      $lean_isize_div(v2, v1),
    ],
    $lean_isize_div(v2, v2),
  ];
})();
export const TestISize_test1 = (() => {
  const v0 = $lean_isize_of_nat(1n);
  const v1 = $lean_isize_of_nat(2n);
  const v2 = $lean_isize_neg(v0);
  return [
    ...[
      ...[
        ...[
          ...[...[...[], $lean_isize_add(v0, v0)], $lean_isize_add(v0, v1)],
          $lean_isize_add(v1, v0),
        ],
        $lean_isize_add(v0, $lean_isize_neg(v1)),
      ],
      $lean_isize_add(v2, v1),
    ],
    $lean_isize_add(v2, v2),
  ];
})();
export const TestISize_intValues = (v0) => {
  const v1 = $lean_isize_of_nat(1n);
  const v2 = $lean_isize_of_nat(2n);
  const v3 = $lean_isize_neg(v1);
  return [
    ...[
      ...[
        ...[...[...[...[], v0(v1, v1)], v0(v1, v2)], v0(v2, v1)],
        v0(v1, $lean_isize_neg(v2)),
      ],
      v0(v3, v2),
    ],
    v0(v3, v3),
  ];
};
