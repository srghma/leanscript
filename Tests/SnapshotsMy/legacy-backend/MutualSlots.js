const _spec$walkNat = (v0, v1, v2) => {
  let v3 = v0, v4 = v1;
  while (true) {
    if (v3 === 0) {
      return v4;
    } else {
      const v5 = v3 - 1;
      if (v4 === 0) {
        if (v5 === 0) {
          return "".length;
        } else {
          v3 = v5 - 1;
          v4 = "".length + 1;
          continue;
        }
      } else {
        if (v5 === 0) {
          return "xy".length;
        } else {
          v3 = v5 - 1;
          v4 = "xy".length + 1;
          continue;
        }
      }
    }
  }
};
export const walkNat = (v0, v1) => _spec$walkNat(v0, v1, "");
export const walkStr = (v0, v1) => {
  if (v0 === 0) {
    return v1.length;
  } else {
    return _spec$walkNat(v0 - 1, v1.length + 1, v1);
  }
};
