const test1 = (v_a, v_b, v_c) => {
  if (v_a === 1) {
    return "0";
  }
  if (v_b === 1) {
    return "1";
  }
  if (v_c === 1) {
    return "2";
  }
  if (v_a === 2 && v_b === 2) {
    return "3";
  }
  return "catch";
};
const test2 = (v_a_b, v_a_c, v_d_e, v_d_f) => {
  if (v_a_c === 2) {
    if (v_d_e === 1 && v_d_f === 2) {
      if (v_a_b === 1) {
        return 1;
      }
      return 2;
    }
    if (v_a_b === 1) {
      return 3;
    }
  }
  return 4;
};
const test3 = (v_a, v_b) => {
  if (v_a > 0) {
    return v_a;
  }
  if (v_b > 1) {
    return v_b;
  }
  return 3;
};
const test4 = (v_a, v_b) => {
  if (v_a > 0) {
    return v_a;
  }
  if (v_b > 1) {
    return v_b;
  }
  return 3;
};
const test5 = (v_a, v_b) => {
  if (v_a > 0) {
    return v_a;
  }
  if (v_b > 0) {
    return v_b;
  }
  return 0;
};
const test6 = (v_a, v_b) => {
  if (v_a > 0) {
    return v_a;
  }
  if (v_b > 0) {
    return v_b;
  }
  return 0;
};
export { test1, test2, test3, test4, test5, test6 };
