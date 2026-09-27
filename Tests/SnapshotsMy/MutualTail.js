const _spec$test3 = (v0, v1, v2) => {
  let v3 = v0, v4 = v1;
  while (true) {
    if (v3 === 0) {
      return v4;
    } else {
      const v5 = v3 - 1;
      const v6 = v4 + 1;
      if (v5 === 0) {
        return v6;
      } else {
        const v7 = v5 - 1;
        const v8 = v6 + 2;
        if (v7 === 0) {
          return v8;
        } else {
          v3 = v7 - 1;
          v4 = v8 + 3;
          continue;
        }
      }
    }
  }
};
export const test3 = (v0, v1) => _spec$test3(v0, v1, 0);
export const test4 = (v0, v1, v2) => {
  if (v0 === 0) {
    return v1;
  } else {
    const v3 = v0 - 1;
    const v4 = v1 + v2;
    if (v3 === 0) {
      return v4;
    } else {
      return _spec$test3(v3 - 1, v4 + 3, v2);
    }
  }
};
export const test5 = (v0, v1) => {
  if (v0 === 0) {
    return v1;
  } else {
    return _spec$test3(v0 - 1, v1 + 3, 0);
  }
};
const _spec$test1 = (v0) => {
  let v1 = v0;
  while (true) {
    if (v1 === 0) {
      return true;
    } else {
      const v2 = v1 - 1;
      if (v2 === 0) {
        return false;
      } else {
        v1 = v2 - 1;
        continue;
      }
    }
  }
};
export const test1 = _spec$test1;
export const test2 = (v0) => {
  if (v0 === 0) {
    return false;
  } else {
    return _spec$test1(v0 - 1);
  }
};
