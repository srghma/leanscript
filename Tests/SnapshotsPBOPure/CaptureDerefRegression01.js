const _spec$testEven = (v0, v1) => {
  let v2 = v0, v3 = v1._1, v4 = v1._2;
  while (true) {
    if (v2 === 0) {
      return { tag: 0, _1: v3, _2: v4 };
    } else {
      const v5 = v2 - 1;
      const v6 = v4 + 1;
      const v7 = v3 + 2;
      if (v5 === 0) {
        return { tag: 0, _1: v6, _2: v7 };
      } else {
        v2 = v5 - 1;
        v3 = v7 + 3;
        v4 = v6 + 4;
        continue;
      }
    }
  }
};
export const testEven = _spec$testEven;
export const testOdd = (v0, v1) => {
  if (v0 === 0) {
    return v1;
  } else {
    return _spec$testEven(v0 - 1, { tag: 0, _1: v1._2 + 3, _2: v1._1 + 4 });
  }
};
export const test5 = (
  v0,
) => ({ tag: 0, _1: (v1) => v0._1 + v1, _2: (v1) => v0._2 + v1 });
export const test4 = (
  v0,
) => ({ tag: 0, _1: (v1) => v0._1 + v1, _2: (v1) => v0._2 + v1 });
export const test3 = (v0) => (v1) => v0._1 + v1;
export const test2 = (v0, v1) => v0._1 + v1;
export const test1 = (v0, v1) => v0._1 + v1;
