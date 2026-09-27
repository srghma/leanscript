import {
  $lean_string_pos_raw_at_end,
  $lean_string_pos_raw_get,
  $lean_string_pos_raw_next,
  $lean_string_push,
} from "../runtime/lean_runtime_non_configurable.mjs";
import {
  $lean_string_utf8_byte_size,
} from "../runtime/lean_runtime_nat_num.mjs";
const _private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0 = (
  v0,
  v1,
  v2,
) => {
  let v3 = v0, v4 = v1._1, v5 = v1._2, v6 = v2;
  while (true) {
    if (v6 < v3._2) {
      const t$3$3 = v6 + v3._3;
      v4 = v4 + $lean_string_utf8_byte_size(v5);
      v5 = $lean_string_push(v5, "x");
      v6 = t$3$3;
      continue;
    } else {
      return { tag: 0, _1: v4, _2: v5 };
    }
  }
};
export const test4_go = (v0, v1, v2) => {
  let v3 = v0, v4 = v1, v5 = v2;
  while (true) {
    if (v4 < v3.length) {
      const t$3$2 = v5 + v4;
      v4 = v4 + 1;
      v5 = t$3$2;
      continue;
    } else {
      return v5;
    }
  }
};
export const test2_go = (v0, v1, v2) => {
  let v3 = v0, v4 = v1, v5 = v2;
  while (true) {
    if ($lean_string_pos_raw_at_end(v3, v5)) {
      return v5;
    } else {
      if ($lean_string_pos_raw_get(v3, v5) === v4) {
        return v5;
      } else {
        const t$3$2 = $lean_string_pos_raw_next(v3, v5);
        v5 = t$3$2;
        continue;
      }
    }
  }
};
export const test1_go = (v0, v1, v2, v3) => {
  let v4 = v0, v5 = v1, v6 = v2, v7 = v3;
  while (true) {
    if ($lean_string_pos_raw_at_end(v4, v6)) {
      return v7;
    } else {
      const v8 = $lean_string_pos_raw_next(v4, v6);
      if ($lean_string_pos_raw_get(v4, v6) === v5) {
        v6 = v8;
        v7 = v7 + 1;
        continue;
      } else {
        v6 = v8;
        continue;
      }
    }
  }
};
export const test4 = (v0) => test4_go(v0, 0, 0);
export const test3 = (
  v0,
  v1,
) => _private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0(
  { tag: 0, _1: 0, _2: v1, _3: 1 },
  { tag: 0, _1: 0, _2: v0 },
  0,
)._1;
export const test2 = (v0, v1) => test2_go(v0, v1, 0);
export const test1 = (v0, v1) => test1_go(v0, v1, 0, 0);
