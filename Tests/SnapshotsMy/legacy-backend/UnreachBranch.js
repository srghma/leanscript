export const small = (v0) => {
  if (v0 === 0) {
    return 10;
  } else {
    if (v0 - 1 === 0) {
      return 20;
    } else {
      return 30;
    }
  }
};
export const test = (v0) => {
  if (v0 < 3) {
    return small(v0) + v0;
  } else {
    return 0;
  }
};
export const headOf = (v0) => v0._1;
