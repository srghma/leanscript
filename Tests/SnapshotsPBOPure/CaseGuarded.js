const test1 = (v) => {
  if (v < 1) {
    return "n: " + v;
  }
  if (v > 1 && v < 100) {
    return "1 < x < 100: " + v;
  }
  if (v > 1 && v < 50) {
    return "1 < x < 50: " + v;
  }
  return "catch";
};
const test2 = (v) => {
  if (v < 1) {
    return v;
  }
  if (v > 1) {
    return v;
  }
  if (v === 1) {
    return 1;
  }
  return 0;
};
const test3 = (v_1, v_2, v_3) => {
  if (v_1 === v_2) {
    return v_1;
  }
  if (v_3 === v_2) {
    return v_1;
  }
  if (v_1 === v_3) {
    return v_3;
  }
  return v_2;
};
const test4 = (v_a, v_b, v_c) => (v1_d, v1_e, v1_f) => {
  if (v_a === 1) {
    if (v1_d === 1) {
      return 1;
    }
    if (v1_d === 2) {
      return 2;
    }
    if (v1_d === 3) {
      return 3;
    }
    if (v1_d === 4) {
      return 4;
    }
    if (v1_d === 5) {
      return 5;
    }
    return (((11 + v_c) | 0) + v1_f) | 0;
  }
  if (v1_d === 2) {
    return 2;
  }
  if (v1_d === 3) {
    return 3;
  }
  if (v_a === 2) {
    if (v1_d === 1) {
      return 6;
    }
    if (v1_d === 4) {
      if (v_c === v1_e) {
        return 7;
      }
      if (v_c < v1_e) {
        return 8;
      }
      if (v_c > v1_e) {
        return 9;
      }
    }
    return (((11 + v_c) | 0) + v1_f) | 0;
  }
  if (v1_d === 4) {
    if (v_c === v1_e) {
      return 7;
    }
    if (v_c < v1_e) {
      return 8;
    }
    if (v_c > v1_e) {
      return 9;
    }
    return (((11 + v_c) | 0) + v1_f) | 0;
  }
  if (v_b === 2 && v1_d === 1 && v1_f === 10) {
    return 10;
  }
  return (((11 + v_c) | 0) + v1_f) | 0;
};
const test5 = (v) => {
  if (v.tag === "some" && v._val.tag === "ok") {
    return v._val._val;
  }
  if (v.tag === "some" && v._val.tag === "error" && v._val._1 === 2) {
    return 4;
  }
  return 5;
};
export { test1, test2, test3, test4, test5 };
