export const span_go = (v0, v1, v2) => {
  let v3 = v0, v4 = v1, v5 = v2;
  while (true) {
    if (v5 < v4.length) {
      if (v3(v4[v5])) {
        v5 = v5 + 1;
        continue;
      } else {
        return { tag: 1, _1: v5 };
      }
    } else {
      return { tag: 0 };
    }
  }
};
export const span = (v0, v1) => span_go(v0, v1, 0);
