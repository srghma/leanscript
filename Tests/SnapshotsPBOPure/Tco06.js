const _spec$f = (v0, v1, v2) => {
  let v3 = v0, v4 = v1, v5 = v2;
  while (true) {
    if (v3 === 0) {
      return v4 + v5;
    } else {
      const v6 = v3 - 1;
      const v7 = v4 + v5;
      if (v6 === 0) {
        return v7;
      } else {
        v3 = v6 - 1;
        v4 = v7;
        v5 = v7 + 1;
        continue;
      }
    }
  }
};
export const f = _spec$f;
export const g = (v0, v1) => {
  if (v0 === 0) {
    return v1;
  } else {
    return _spec$f(v0 - 1, v1, v1 + 1);
  }
};
