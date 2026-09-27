const test1 = (v_a, v_b, v_c) => {
  if (v_a === 1) {
    if (v_c === 3 && v_b === 2) {
      return "1";
    }
    if (v_b === 4) {
      return "2";
    }
    return "catch";
  }
  if (v_b === 4) {
    return "2";
  }
  if (v_a === 4 && v_b === 5 && v_c === 6) {
    return "3";
  }
  return "catch";
};
export { test1 };
