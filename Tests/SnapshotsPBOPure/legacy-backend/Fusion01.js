import {
  $lean_array_mk,
  $lean_array_uget,
  $lean_string_memcmp,
  Id_instMonad,
  Nat_reprFast,
  String_Slice_Pos_nextn,
  String_Slice_toString,
  _private_Init_Data_Array_Basic_0_Array_foldrMUnsafe_fold,
  instDecidableEqUSize,
} from "../runtime/lean_runtime_non_configurable.mjs";
import {
  $lean_string_utf8_byte_size,
} from "../runtime/lean_runtime_nat_num.mjs";
import {
  $lean_usize_of_nat,
  $lean_usize_sub,
} from "../runtime/lean_runtime_usize_num.mjs";
const _private_Init_Data_Array_Basic_0_Array_foldrMUnsafe_fold__at__test_spec_0 = (
  v0,
  v1,
  v2,
  v3,
) => {
  let v4 = v0, v5 = v1, v6 = v2, v7 = v3;
  while (true) {
    const v8 = (v8, v9) => {
      const v10 = $lean_string_utf8_byte_size(v8);
      const v11 = $lean_string_utf8_byte_size("1");
      if (v11 <= v10) {
        if ($lean_string_memcmp(v8, "1", 0, 0, v11)) {
          const v12 = "2" +
            String_Slice_toString(
              {
                tag: 0,
                _1: v8,
                _2: String_Slice_Pos_nextn(
                  { tag: 0, _1: v8, _2: 0, _3: v10 },
                  0,
                  1,
                ),
                _3: v10,
              },
            );
          if (v12 === "wat") {
            return v9;
          } else {
            return { tag: 1, _1: v12 + "1", _2: v9 };
          }
        } else {
          return v9;
        }
      } else {
        return v9;
      }
    };
    if (instDecidableEqUSize(v5, v6)) {
      return v7;
    } else {
      const v9 = $lean_usize_sub(v5, 1);
      const v10 = $lean_array_uget(v4, v9) + 1;
      if (v10 < 0) {
        v5 = v9;
        v7 = v8("-" + Nat_reprFast(-1 - v10 + 1), v7);
        continue;
      } else {
        v5 = v9;
        v7 = v8(Nat_reprFast(v10), v7);
        continue;
      }
    }
  }
};
export const toArray = (
  v0,
) => $lean_array_mk(v0((v1, v2) => ({ tag: 1, _1: v1, _2: v2 }), { tag: 0 }));
export const test = (v0) => {
  const v1 = { tag: 0 };
  const v2 = v0.length;
  if (0 < v2) {
    return $lean_array_mk(
      _private_Init_Data_Array_Basic_0_Array_foldrMUnsafe_fold__at__test_spec_0(
        v0,
        $lean_usize_of_nat(v2),
        0,
        v1,
      ),
    );
  } else {
    return $lean_array_mk(v1);
  }
};
export const overArray = (
  v0,
  v1,
) => $lean_array_mk(
  v0(
    (v2, v3) => {
      const v4 = v1.length;
      if (0 < v4) {
        return _private_Init_Data_Array_Basic_0_Array_foldrMUnsafe_fold(
          Id_instMonad,
          (v5, v6) => v2(v5, v6),
          v1,
          $lean_usize_of_nat(v4),
          0,
          v3,
        );
      } else {
        return v3;
      }
    },
  )((v2, v3) => ({ tag: 1, _1: v2, _2: v3 }), { tag: 0 }),
);
export const mapF = (v0, v1) => (v2, v3) => v1((v4, v5) => v2(v0(v4), v5), v3);
export const fromArray = (v0) => (v1, v2) => {
  const v3 = (v3, v4) => v1(v3, v4);
  const v4 = v0.length;
  if (v4 <= v4) {
    if (0 < v4) {
      return _private_Init_Data_Array_Basic_0_Array_foldrMUnsafe_fold(
        Id_instMonad,
        v3,
        v0,
        $lean_usize_of_nat(v4),
        0,
        v2,
      );
    } else {
      return v2;
    }
  } else {
    if (0 < v4) {
      return _private_Init_Data_Array_Basic_0_Array_foldrMUnsafe_fold(
        Id_instMonad,
        v3,
        v0,
        $lean_usize_of_nat(v4),
        0,
        v2,
      );
    } else {
      return v2;
    }
  }
};
export const filterMapF = (
  v0,
  v1,
) => (
  v2,
  v3,
) => v1(
  (v4, v5) => {
    const v6 = v0(v4);
    if (v6.tag === 0) {
      return v5;
    } else {
      return v2(v6._1, v5);
    }
  },
  v3,
);
export const filterF = (
  v0,
  v1,
) => (
  v2,
  v3,
) => v1(
  (v4, v5) => {
    if (v0(v4)) {
      return v2(v4, v5);
    } else {
      return v5;
    }
  },
  v3,
);
export const dropPrefix1 = (v0) => {
  const v1 = $lean_string_utf8_byte_size(v0);
  const v2 = $lean_string_utf8_byte_size("1");
  if (v2 <= v1) {
    if ($lean_string_memcmp(v0, "1", 0, 0, v2)) {
      return {
        tag: 1,
        _1: String_Slice_toString(
          {
            tag: 0,
            _1: v0,
            _2: String_Slice_Pos_nextn({ tag: 0, _1: v0, _2: 0, _3: v1 }, 0, 1),
            _3: v1,
          },
        ),
      };
    } else {
      return { tag: 0 };
    }
  } else {
    return { tag: 0 };
  }
};
