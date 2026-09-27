import {
  $lean_array_fset,
  $lean_array_uget,
  $lean_array_uset,
  $lean_mk_array,
  List_reverse,
  instBEqOfDecidableEq,
  instDecidableEqUSize,
} from "../runtime/lean_runtime_non_configurable.mjs";
import {
  $lean_uint64_to_usize,
  $lean_usize_land,
  $lean_usize_of_nat,
  $lean_usize_sub,
} from "../runtime/lean_runtime_usize_num.mjs";
import {
  $lean_string_hash,
  $lean_uint64_of_nat,
  $lean_uint64_shift_right,
  $lean_uint64_xor,
  instHashableNat,
  instHashableString,
} from "../runtime/lean_runtime_uint64_num.mjs";
const Std_DHashMap_Internal_AssocList_foldlM__at___private_Std_Data_DHashMap_Internal_Defs_0_Std_DHashMap_Internal_Raw__expand_go__at__Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test2_spec_0_spec_1_spec_2_spec_5 = (
  v0,
  v1,
) => {
  let v2 = v0, v3 = v1;
  while (true) {
    if (v3.tag === 0) {
      return v2;
    } else {
      const v4 = v3._1;
      const v5 = $lean_uint64_of_nat(v4);
      const v6 = $lean_uint64_xor(v5, $lean_uint64_shift_right(v5, 32));
      const v7 = $lean_usize_land(
        $lean_uint64_to_usize(
          $lean_uint64_xor(v6, $lean_uint64_shift_right(v6, 16)),
        ),
        $lean_usize_sub($lean_usize_of_nat(v2.length), 1),
      );
      v2 = $lean_array_uset(
        v2,
        v7,
        { tag: 1, _1: v4, _2: v3._2, _3: $lean_array_uget(v2, v7) },
      );
      v3 = v3._3;
      continue;
    }
  }
};
const Std_DHashMap_Internal_AssocList_foldlM__at___private_Std_Data_DHashMap_Internal_Defs_0_Std_DHashMap_Internal_Raw__expand_go__at__Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_3_spec_4_spec_6 = (
  v0,
  v1,
) => {
  let v2 = v0, v3 = v1;
  while (true) {
    if (v3.tag === 0) {
      return v2;
    } else {
      const v4 = v3._1;
      const v5 = $lean_string_hash(v4);
      const v6 = $lean_uint64_xor(v5, $lean_uint64_shift_right(v5, 32));
      const v7 = $lean_usize_land(
        $lean_uint64_to_usize(
          $lean_uint64_xor(v6, $lean_uint64_shift_right(v6, 16)),
        ),
        $lean_usize_sub($lean_usize_of_nat(v2.length), 1),
      );
      v2 = $lean_array_uset(
        v2,
        v7,
        { tag: 1, _1: v4, _2: v3._2, _3: $lean_array_uget(v2, v7) },
      );
      v3 = v3._3;
      continue;
    }
  }
};
const _private_Std_Data_DHashMap_Internal_Defs_0_Std_DHashMap_Internal_Raw__expand_go__at__Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test2_spec_0_spec_1_spec_2 = (
  v0,
  v1,
  v2,
) => {
  let v3 = v0, v4 = v1, v5 = v2;
  while (true) {
    if (v3 < v4.length) {
      const t$3$1 = $lean_array_fset(v4, v3, { tag: 0 });
      const t$3$2 = Std_DHashMap_Internal_AssocList_foldlM__at___private_Std_Data_DHashMap_Internal_Defs_0_Std_DHashMap_Internal_Raw__expand_go__at__Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test2_spec_0_spec_1_spec_2_spec_5(
        v5,
        v4[v3],
      );
      v3 = v3 + 1;
      v4 = t$3$1;
      v5 = t$3$2;
      continue;
    } else {
      return v5;
    }
  }
};
const _private_Std_Data_DHashMap_Internal_Defs_0_Std_DHashMap_Internal_Raw__expand_go__at__Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_3_spec_4 = (
  v0,
  v1,
  v2,
) => {
  let v3 = v0, v4 = v1, v5 = v2;
  while (true) {
    if (v3 < v4.length) {
      const t$3$1 = $lean_array_fset(v4, v3, { tag: 0 });
      const t$3$2 = Std_DHashMap_Internal_AssocList_foldlM__at___private_Std_Data_DHashMap_Internal_Defs_0_Std_DHashMap_Internal_Raw__expand_go__at__Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_3_spec_4_spec_6(
        v5,
        v4[v3],
      );
      v3 = v3 + 1;
      v4 = t$3$1;
      v5 = t$3$2;
      continue;
    } else {
      return v5;
    }
  }
};
const Std_DHashMap_Internal_AssocList_contains__at__Std_DHashMap_Internal_Raw__insert__at__test2_spec_0_spec_0 = (
  v0,
  v1,
) => {
  let v2 = v0, v3 = v1;
  while (true) {
    if (v3.tag === 0) {
      return false;
    } else {
      const v4 = v3._1 === v2;
      if (v4) {
        return v4;
      } else {
        v3 = v3._3;
        continue;
      }
    }
  }
};
const Std_DHashMap_Internal_AssocList_replace__at__Std_DHashMap_Internal_Raw__insert__at__test2_spec_0_spec_2 = (
  v0,
  v1,
  v2,
) => {
  if (v2.tag === 0) {
    return v2;
  } else {
    const v3 = v2._1;
    const v4 = v2._3;
    if (v3 === v0) {
      return { tag: 1, _1: v0, _2: v1, _3: v4 };
    } else {
      return {
        tag: 1,
        _1: v3,
        _2: v2._2,
        _3: Std_DHashMap_Internal_AssocList_replace__at__Std_DHashMap_Internal_Raw__insert__at__test2_spec_0_spec_2(
          v0,
          v1,
          v4,
        ),
      };
    }
  }
};
const Std_DHashMap_Internal_AssocList_replace__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_4 = (
  v0,
  v1,
  v2,
) => {
  if (v2.tag === 0) {
    return v2;
  } else {
    const v3 = v2._1;
    const v4 = v2._3;
    if (v3 === v0) {
      return { tag: 1, _1: v0, _2: v1, _3: v4 };
    } else {
      return {
        tag: 1,
        _1: v3,
        _2: v2._2,
        _3: Std_DHashMap_Internal_AssocList_replace__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_4(
          v0,
          v1,
          v4,
        ),
      };
    }
  }
};
const Std_DHashMap_Internal_AssocList_getD__at__Std_DHashMap_Internal_Raw__Const_getD__at__test1_spec_0_spec_0 = (
  v0,
  v1,
  v2,
) => {
  let v3 = v0, v4 = v1, v5 = v2;
  while (true) {
    if (v5.tag === 0) {
      return v4;
    } else {
      if (v5._1 === v3) {
        return v5._2;
      } else {
        v5 = v5._3;
        continue;
      }
    }
  }
};
const Std_DHashMap_Internal_AssocList_foldrM__at__test6_spec_1 = (v0, v1) => {
  if (v1.tag === 0) {
    return v0;
  } else {
    return {
      tag: 1,
      _1: { tag: 0, _1: v1._1, _2: v1._2 },
      _2: Std_DHashMap_Internal_AssocList_foldrM__at__test6_spec_1(v0, v1._3),
    };
  }
};
const Std_DHashMap_Internal_AssocList_erase__at__Std_DHashMap_Internal_Raw__erase__at__test5_spec_0_spec_0 = (
  v0,
  v1,
) => {
  if (v1.tag === 0) {
    return v1;
  } else {
    const v2 = v1._1;
    const v3 = v1._3;
    if (v2 === v0) {
      return v3;
    } else {
      return {
        tag: 1,
        _1: v2,
        _2: v1._2,
        _3: Std_DHashMap_Internal_AssocList_erase__at__Std_DHashMap_Internal_Raw__erase__at__test5_spec_0_spec_0(
          v0,
          v3,
        ),
      };
    }
  }
};
const Std_DHashMap_Internal_AssocList_contains__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_2 = (
  v0,
  v1,
) => {
  let v2 = v0, v3 = v1;
  while (true) {
    if (v3.tag === 0) {
      return false;
    } else {
      const v4 = v3._1 === v2;
      if (v4) {
        return v4;
      } else {
        v3 = v3._3;
        continue;
      }
    }
  }
};
const Std_DHashMap_Internal_Raw__insertIfNew__at__test3_spec_0 = (
  v0,
  v1,
  v2,
) => {
  const v3 = v0._2;
  const v4 = $lean_string_hash(v1);
  const v5 = $lean_uint64_xor(v4, $lean_uint64_shift_right(v4, 32));
  const v6 = $lean_usize_land(
    $lean_uint64_to_usize(
      $lean_uint64_xor(v5, $lean_uint64_shift_right(v5, 16)),
    ),
    $lean_usize_sub($lean_usize_of_nat(v3.length), 1),
  );
  const v7 = $lean_array_uget(v3, v6);
  if (Std_DHashMap_Internal_AssocList_contains__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_2(
    v1,
    v7,
  )) {
    return v0;
  } else {
    const v8 = v0._1 + 1;
    const v9 = $lean_array_uset(v3, v6, { tag: 1, _1: v1, _2: v2, _3: v7 });
    if (Math.trunc(v8 * 4 / 3) <= v9.length) {
      return { tag: 0, _1: v8, _2: v9 };
    } else {
      return {
        tag: 0,
        _1: v8,
        _2: _private_Std_Data_DHashMap_Internal_Defs_0_Std_DHashMap_Internal_Raw__expand_go__at__Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_3_spec_4(
          0,
          v9,
          $lean_mk_array(v9.length * 2, { tag: 0 }),
        ),
      };
    }
  }
};
const Std_DHashMap_Internal_Raw__insert__at__test2_spec_0 = (v0, v1, v2) => {
  const v3 = v0._1;
  const v4 = v0._2;
  const v5 = $lean_uint64_of_nat(v1);
  const v6 = $lean_uint64_xor(v5, $lean_uint64_shift_right(v5, 32));
  const v7 = $lean_usize_land(
    $lean_uint64_to_usize(
      $lean_uint64_xor(v6, $lean_uint64_shift_right(v6, 16)),
    ),
    $lean_usize_sub($lean_usize_of_nat(v4.length), 1),
  );
  const v8 = $lean_array_uget(v4, v7);
  if (Std_DHashMap_Internal_AssocList_contains__at__Std_DHashMap_Internal_Raw__insert__at__test2_spec_0_spec_0(
    v1,
    v8,
  )) {
    return {
      tag: 0,
      _1: v3,
      _2: $lean_array_uset(
        $lean_array_uset(v4, v7, { tag: 0 }),
        v7,
        Std_DHashMap_Internal_AssocList_replace__at__Std_DHashMap_Internal_Raw__insert__at__test2_spec_0_spec_2(
          v1,
          v2,
          v8,
        ),
      ),
    };
  } else {
    const v9 = v3 + 1;
    const v10 = $lean_array_uset(v4, v7, { tag: 1, _1: v1, _2: v2, _3: v8 });
    if (Math.trunc(v9 * 4 / 3) <= v10.length) {
      return { tag: 0, _1: v9, _2: v10 };
    } else {
      return {
        tag: 0,
        _1: v9,
        _2: _private_Std_Data_DHashMap_Internal_Defs_0_Std_DHashMap_Internal_Raw__expand_go__at__Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test2_spec_0_spec_1_spec_2(
          0,
          v10,
          $lean_mk_array(v10.length * 2, { tag: 0 }),
        ),
      };
    }
  }
};
const Std_DHashMap_Internal_AssocList_get___at__Std_DHashMap_Internal_Raw__Const_get___at__test2_spec_2_spec_5 = (
  v0,
  v1,
) => {
  let v2 = v0, v3 = v1;
  while (true) {
    if (v3.tag === 0) {
      return { tag: 0 };
    } else {
      if (v3._1 === v2) {
        return { tag: 1, _1: v3._2 };
      } else {
        v3 = v3._3;
        continue;
      }
    }
  }
};
const Std_DHashMap_Internal_Raw__insert__at__test1_spec_1 = (v0, v1, v2) => {
  const v3 = v0._1;
  const v4 = v0._2;
  const v5 = $lean_string_hash(v1);
  const v6 = $lean_uint64_xor(v5, $lean_uint64_shift_right(v5, 32));
  const v7 = $lean_usize_land(
    $lean_uint64_to_usize(
      $lean_uint64_xor(v6, $lean_uint64_shift_right(v6, 16)),
    ),
    $lean_usize_sub($lean_usize_of_nat(v4.length), 1),
  );
  const v8 = $lean_array_uget(v4, v7);
  if (Std_DHashMap_Internal_AssocList_contains__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_2(
    v1,
    v8,
  )) {
    return {
      tag: 0,
      _1: v3,
      _2: $lean_array_uset(
        $lean_array_uset(v4, v7, { tag: 0 }),
        v7,
        Std_DHashMap_Internal_AssocList_replace__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_4(
          v1,
          v2,
          v8,
        ),
      ),
    };
  } else {
    const v9 = v3 + 1;
    const v10 = $lean_array_uset(v4, v7, { tag: 1, _1: v1, _2: v2, _3: v8 });
    if (Math.trunc(v9 * 4 / 3) <= v10.length) {
      return { tag: 0, _1: v9, _2: v10 };
    } else {
      return {
        tag: 0,
        _1: v9,
        _2: _private_Std_Data_DHashMap_Internal_Defs_0_Std_DHashMap_Internal_Raw__expand_go__at__Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_3_spec_4(
          0,
          v10,
          $lean_mk_array(v10.length * 2, { tag: 0 }),
        ),
      };
    }
  }
};
const List_forIn__loop__at__test7_spec_0 = (v0, v1, v2, v3, v4) => {
  let v5 = v3, v6 = v4;
  while (true) {
    if (v5.tag === 0) {
      return v6;
    } else {
      const v7 = v5._1;
      v5 = v5._2;
      v6 = Std_DHashMap_Internal_Raw__insert__at__test1_spec_1(
        v6,
        v7,
        v7.length,
      );
      continue;
    }
  }
};
const Std_DHashMap_Internal_Raw__Const_getD__at__test1_spec_0 = (
  v0,
  v1,
  v2,
) => {
  const v3 = v0._2;
  const v4 = $lean_string_hash(v1);
  const v5 = $lean_uint64_xor(v4, $lean_uint64_shift_right(v4, 32));
  return Std_DHashMap_Internal_AssocList_getD__at__Std_DHashMap_Internal_Raw__Const_getD__at__test1_spec_0_spec_0(
    v1,
    v2,
    $lean_array_uget(
      v3,
      $lean_usize_land(
        $lean_uint64_to_usize(
          $lean_uint64_xor(v5, $lean_uint64_shift_right(v5, 16)),
        ),
        $lean_usize_sub($lean_usize_of_nat(v3.length), 1),
      ),
    ),
  );
};
const _private_Init_Data_Array_Basic_0_Array_foldrMUnsafe_fold__at__test6_spec_2 = (
  v0,
  v1,
  v2,
  v3,
) => {
  let v4 = v0, v5 = v1, v6 = v2, v7 = v3;
  while (true) {
    if (instDecidableEqUSize(v5, v6)) {
      return v7;
    } else {
      const v8 = $lean_usize_sub(v5, 1);
      const t$4$3 = Std_DHashMap_Internal_AssocList_foldrM__at__test6_spec_1(
        v7,
        $lean_array_uget(v4, v8),
      );
      v5 = v8;
      v7 = t$4$3;
      continue;
    }
  }
};
const List_mapTR_loop__at__test6_spec_0 = (v0, v1) => {
  let v2 = v0, v3 = v1;
  while (true) {
    if (v2.tag === 0) {
      return List_reverse(v3);
    } else {
      const t$2$1 = { tag: 1, _1: v2._1._1, _2: v3 };
      v2 = v2._2;
      v3 = t$2$1;
      continue;
    }
  }
};
const Std_DHashMap_Internal_Raw__erase__at__test5_spec_0 = (v0, v1) => {
  const v2 = v0._2;
  const v3 = $lean_string_hash(v1);
  const v4 = $lean_uint64_xor(v3, $lean_uint64_shift_right(v3, 32));
  const v5 = $lean_usize_land(
    $lean_uint64_to_usize(
      $lean_uint64_xor(v4, $lean_uint64_shift_right(v4, 16)),
    ),
    $lean_usize_sub($lean_usize_of_nat(v2.length), 1),
  );
  const v6 = $lean_array_uget(v2, v5);
  if (Std_DHashMap_Internal_AssocList_contains__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_2(
    v1,
    v6,
  )) {
    return {
      tag: 0,
      _1: Math.max(0, v0._1 - 1),
      _2: $lean_array_uset(
        $lean_array_uset(v2, v5, { tag: 0 }),
        v5,
        Std_DHashMap_Internal_AssocList_erase__at__Std_DHashMap_Internal_Raw__erase__at__test5_spec_0_spec_0(
          v1,
          v6,
        ),
      ),
    };
  } else {
    return v0;
  }
};
const List_forIn__loop__at__test4_spec_0 = (v0, v1, v2, v3, v4) => {
  let v5 = v3, v6 = v4;
  while (true) {
    if (v5.tag === 0) {
      return v6;
    } else {
      const t$5$1 = Std_DHashMap_Internal_Raw__insert__at__test1_spec_1(
        v6,
        v5._1,
        1,
      );
      v5 = v5._2;
      v6 = t$5$1;
      continue;
    }
  }
};
const List_forIn__loop__at__test4_spec_1 = (v0, v1, v2, v3, v4) => {
  let v5 = v3, v6 = v4;
  while (true) {
    if (v5.tag === 0) {
      return v6;
    } else {
      const t$5$1 = Std_DHashMap_Internal_Raw__insertIfNew__at__test3_spec_0(
        v6,
        v5._1 + "!",
        0,
      );
      v5 = v5._2;
      v6 = t$5$1;
      continue;
    }
  }
};
const Std_DHashMap_Internal_Raw__contains__at__test3_spec_2 = (v0, v1) => {
  const v2 = v0._2;
  const v3 = $lean_string_hash(v1);
  const v4 = $lean_uint64_xor(v3, $lean_uint64_shift_right(v3, 32));
  return Std_DHashMap_Internal_AssocList_contains__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_2(
    v1,
    $lean_array_uget(
      v2,
      $lean_usize_land(
        $lean_uint64_to_usize(
          $lean_uint64_xor(v4, $lean_uint64_shift_right(v4, 16)),
        ),
        $lean_usize_sub($lean_usize_of_nat(v2.length), 1),
      ),
    ),
  );
};
const List_forIn__loop__at__test3_spec_1 = (v0, v1, v2, v3, v4) => {
  let v5 = v3, v6 = v4;
  while (true) {
    if (v5.tag === 0) {
      return v6;
    } else {
      const t$5$1 = Std_DHashMap_Internal_Raw__insertIfNew__at__test3_spec_0(
        v6,
        v5._1,
        0,
      );
      v5 = v5._2;
      v6 = t$5$1;
      continue;
    }
  }
};
const List_forIn__loop__at__test2_spec_1 = (v0, v1, v2, v3, v4) => {
  let v5 = v3, v6 = v4;
  while (true) {
    if (v5.tag === 0) {
      return v6;
    } else {
      const v7 = v5._1;
      v5 = v5._2;
      v6 = Std_DHashMap_Internal_Raw__insert__at__test2_spec_0(v6, v7, v7 * v7);
      continue;
    }
  }
};
const Std_DHashMap_Internal_Raw__Const_get___at__test2_spec_2 = (v0, v1) => {
  const v2 = v0._2;
  const v3 = $lean_uint64_of_nat(v1);
  const v4 = $lean_uint64_xor(v3, $lean_uint64_shift_right(v3, 32));
  return Std_DHashMap_Internal_AssocList_get___at__Std_DHashMap_Internal_Raw__Const_get___at__test2_spec_2_spec_5(
    v1,
    $lean_array_uget(
      v2,
      $lean_usize_land(
        $lean_uint64_to_usize(
          $lean_uint64_xor(v4, $lean_uint64_shift_right(v4, 16)),
        ),
        $lean_usize_sub($lean_usize_of_nat(v2.length), 1),
      ),
    ),
  );
};
const List_forIn__loop__at__test1_spec_2 = (v0, v1, v2, v3, v4) => {
  let v5 = v3, v6 = v4;
  while (true) {
    if (v5.tag === 0) {
      return v6;
    } else {
      const v7 = v5._1;
      v5 = v5._2;
      v6 = Std_DHashMap_Internal_Raw__insert__at__test1_spec_1(
        v6,
        v7,
        Std_DHashMap_Internal_Raw__Const_getD__at__test1_spec_0(v6, v7, 0) + 1,
      );
      continue;
    }
  }
};
export const test7 = (
  v0,
  v1,
) => Std_DHashMap_Internal_Raw__Const_getD__at__test1_spec_0(
  List_forIn__loop__at__test7_spec_0(
    instBEqOfDecidableEq((v2, v3) => v2 === v3),
    instHashableString,
    v0,
    v0,
    { tag: 0, _1: 0, _2: $lean_mk_array(16, { tag: 0 }) },
  ),
  v1,
  0,
);
export const test6 = (v0) => {
  const v1 = { tag: 0 };
  const v2 = List_forIn__loop__at__test4_spec_0(
    instBEqOfDecidableEq((v2, v3) => v2 === v3),
    instHashableString,
    v0,
    v0,
    { tag: 0, _1: 0, _2: $lean_mk_array(16, { tag: 0 }) },
  )._2;
  const v3 = v2.length;
  if (0 < v3) {
    return List_mapTR_loop__at__test6_spec_0(
      _private_Init_Data_Array_Basic_0_Array_foldrMUnsafe_fold__at__test6_spec_2(
        v2,
        $lean_usize_of_nat(v3),
        0,
        v1,
      ),
      { tag: 0 },
    );
  } else {
    return List_mapTR_loop__at__test6_spec_0(v1, { tag: 0 });
  }
};
export const test5 = (v0) => {
  const v1 = List_forIn__loop__at__test4_spec_0(
    instBEqOfDecidableEq((v1, v2) => v1 === v2),
    instHashableString,
    v0,
    v0,
    { tag: 0, _1: 0, _2: $lean_mk_array(16, { tag: 0 }) },
  );
  return Std_DHashMap_Internal_Raw__erase__at__test5_spec_0(v1, "a")._1 * 100 +
    Std_DHashMap_Internal_Raw__erase__at__test5_spec_0(v1, "b")._1;
};
export const test4 = (v0) => {
  const v1 = instBEqOfDecidableEq((v1, v2) => v1 === v2);
  return List_forIn__loop__at__test4_spec_0(
    v1,
    instHashableString,
    v0,
    v0,
    { tag: 0, _1: 0, _2: $lean_mk_array(16, { tag: 0 }) },
  )._1 +
    List_forIn__loop__at__test4_spec_1(
      v1,
      instHashableString,
      v0,
      v0,
      { tag: 0, _1: 0, _2: $lean_mk_array(16, { tag: 0 }) },
    )._1;
};
export const test3 = (v0) => {
  const v1 = List_forIn__loop__at__test3_spec_1(
    instBEqOfDecidableEq((v1, v2) => v1 === v2),
    instHashableString,
    v0,
    v0,
    { tag: 0, _1: 0, _2: $lean_mk_array(16, { tag: 0 }) },
  );
  const v2 = v1._1;
  if (Std_DHashMap_Internal_Raw__contains__at__test3_spec_2(v1, "a")) {
    return v2 + 1;
  } else {
    return v2;
  }
};
export const test2 = (
  v0,
) => Std_DHashMap_Internal_Raw__Const_get___at__test2_spec_2(
  List_forIn__loop__at__test2_spec_1(
    instBEqOfDecidableEq((v1, v2) => v1 === v2),
    instHashableNat,
    v0,
    v0,
    { tag: 0, _1: 0, _2: $lean_mk_array(16, { tag: 0 }) },
  ),
  3,
);
export const test1 = (
  v0,
) => List_forIn__loop__at__test1_spec_2(
  instBEqOfDecidableEq((v1, v2) => v1 === v2),
  instHashableString,
  v0,
  v0,
  { tag: 0, _1: 0, _2: $lean_mk_array(16, { tag: 0 }) },
)._1;
