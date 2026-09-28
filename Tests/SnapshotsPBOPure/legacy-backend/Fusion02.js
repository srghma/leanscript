import {
  $lean_string_memcmp,
  Nat_reprFast,
  String_Slice_Pos_nextn,
  String_Slice_toString,
} from "../runtime/lean_runtime_non_configurable.mjs";
import {
  $lean_string_utf8_byte_size,
} from "../runtime/lean_runtime_nat_num.mjs";
export const toArrayLoop = (v0, v1, v2) => {
  let v3 = v0, v4 = v1, v5 = v2;
  while (true) {
    const v6 = v3._2(v4);
    if (v6.tag === 0) {
      return v5;
    } else {
      const v7 = v6._1;
      v4 = v7._1;
      v5 = [...v5, v7._2];
      continue;
    }
  }
};
export const toArray = (v0) => {
  let v1 = v0, v2 = v0._1, v3 = [];
  while (true) {
    const v4 = v1._2(v2);
    if (v4.tag === 0) {
      return v3;
    } else {
      const v5 = v4._1;
      v2 = v5._1;
      v3 = [...v3, v5._2];
      continue;
    }
  }
};
export const overArray = (v0, v1) => {
  const v2 = v0(
    {
      tag: 0,
      _1: 0,
      _2: (v2) => {
        if (v2 < v1.length) {
          return { tag: 1, _1: { tag: 0, _1: v2 + 1, _2: v1[v2] } };
        } else {
          return { tag: 0 };
        }
      },
      _3: (v2) => Math.max(0, v1.length - v2),
    },
  );
  let v3 = v2, v4 = v2._1, v5 = [];
  while (true) {
    const v6 = v3._2(v4);
    if (v6.tag === 0) {
      return v5;
    } else {
      const v7 = v6._1;
      v4 = v7._1;
      v5 = [...v5, v7._2];
      continue;
    }
  }
};
export const mapU = (
  v0,
  v1,
) => ({
  tag: 0,
  _1: v1._1,
  _2: (v2) => {
    const v3 = v1._2(v2);
    if (v3.tag === 0) {
      return { tag: 0 };
    } else {
      const v4 = v3._1;
      return { tag: 1, _1: { tag: 0, _1: v4._1, _2: v0(v4._2) } };
    }
  },
  _3: v1._3,
});
export const fromArray = (
  v0,
) => ({
  tag: 0,
  _1: 0,
  _2: (v1) => {
    if (v1 < v0.length) {
      return { tag: 1, _1: { tag: 0, _1: v1 + 1, _2: v0[v1] } };
    } else {
      return { tag: 0 };
    }
  },
  _3: (v1) => Math.max(0, v0.length - v1),
});
export const filterU = (v0, v1) => {
  const v2 = (v2) => {
    if (v0(v2)) {
      return { tag: 1, _1: v2 };
    } else {
      return { tag: 0 };
    }
  };
  return {
    tag: 0,
    _1: v1._1,
    _2: (v3) => {
      let v4 = v1, v5 = v2, v6 = v3;
      while (true) {
        const v7 = v4._2(v6);
        if (v7.tag === 0) {
          return { tag: 0 };
        } else {
          const v8 = v7._1;
          const v9 = v8._1;
          const v10 = v5(v8._2);
          if (v10.tag === 0) {
            v6 = v9;
            continue;
          } else {
            return { tag: 1, _1: { tag: 0, _1: v9, _2: v10._1 } };
          }
        }
      }
    },
    _3: v1._3,
  };
};
export const filterMapU = (
  v0,
  v1,
) => ({
  tag: 0,
  _1: v1._1,
  _2: (v2) => {
    let v3 = v1, v4 = v0, v5 = v2;
    while (true) {
      const v6 = v3._2(v5);
      if (v6.tag === 0) {
        return { tag: 0 };
      } else {
        const v7 = v6._1;
        const v8 = v7._1;
        const v9 = v4(v7._2);
        if (v9.tag === 0) {
          v5 = v8;
          continue;
        } else {
          return { tag: 1, _1: { tag: 0, _1: v8, _2: v9._1 } };
        }
      }
    }
  },
  _3: v1._3,
});
export const filterMapStep = (v0, v1, v2) => {
  let v3 = v0, v4 = v1, v5 = v2;
  while (true) {
    const v6 = v3._2(v5);
    if (v6.tag === 0) {
      return { tag: 0 };
    } else {
      const v7 = v6._1;
      const v8 = v7._1;
      const v9 = v4(v7._2);
      if (v9.tag === 0) {
        v5 = v8;
        continue;
      } else {
        return { tag: 1, _1: { tag: 0, _1: v8, _2: v9._1 } };
      }
    }
  }
};
export const test = (v0) => {
  const v1 = (v1) => Math.max(0, v0.length - v1);
  const v2 = (v2) => {
    if (v2 === "wat") {
      return { tag: 0 };
    } else {
      return { tag: 1, _1: v2 };
    }
  };
  const v3 = (v3) => {
    const v4 = $lean_string_utf8_byte_size(v3);
    const v5 = $lean_string_utf8_byte_size("1");
    if (v5 <= v4) {
      if ($lean_string_memcmp(v3, "1", 0, 0, v5)) {
        return {
          tag: 1,
          _1: String_Slice_toString(
            {
              tag: 0,
              _1: v3,
              _2: String_Slice_Pos_nextn(
                { tag: 0, _1: v3, _2: 0, _3: v4 },
                0,
                1,
              ),
              _3: v4,
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
  const v4 = {
    tag: 0,
    _1: 0,
    _2: (v4) => {
      if (v4 < v0.length) {
        const v5 = v4 + 1;
        const v6 = v0[v4] + 1;
        if (v6 < 0) {
          return {
            tag: 1,
            _1: { tag: 0, _1: v5, _2: "-" + Nat_reprFast(-1 - v6 + 1) },
          };
        } else {
          return { tag: 1, _1: { tag: 0, _1: v5, _2: Nat_reprFast(v6) } };
        }
      } else {
        return { tag: 0 };
      }
    },
    _3: v1,
  };
  const v5 = {
    tag: 0,
    _1: 0,
    _2: (v5) => {
      const v6 = filterMapStep(v4, v3, v5);
      if (v6.tag === 0) {
        return v6;
      } else {
        const v7 = v6._1;
        return { tag: 1, _1: { tag: 0, _1: v7._1, _2: "2" + v7._2 } };
      }
    },
    _3: v1,
  };
  return toArrayLoop(
    {
      tag: 0,
      _1: 0,
      _2: (v6) => {
        const v7 = filterMapStep(v5, v2, v6);
        if (v7.tag === 0) {
          return v7;
        } else {
          const v8 = v7._1;
          return { tag: 1, _1: { tag: 0, _1: v8._1, _2: v8._2 + "1" } };
        }
      },
      _3: v1,
    },
    0,
    [],
  );
};
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
