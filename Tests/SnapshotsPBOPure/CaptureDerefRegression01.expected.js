const test1 = (v_fst, v_snd) => (b) => (v_fst + b) | 0;
const test2 = (v_fst, v_snd) => (b) => (v_fst + b) | 0;
const test3 = (v_fst, v_snd) => (b) => (v_fst + b) | 0;
const test4 = (v_fst, v_snd) => ({
  _1: (b) => (v_fst + b) | 0,
  _2: (b) => (v_snd + b) | 0,
});
const test5 = (v_1, v_2) => ({
  _1: (b) => (v_1 + b) | 0,
  _2: (b) => (v_2 + b) | 0,
});
const testEven = (n) => (b_1, b_2) => {
  while (true) {
    if (n === 0) {
      return { _1: b_1, _2: b_2 };
    }
    const next_b_1 = (b_2 + 1) | 0;
    const next_b_2 = (b_1 + 2) | 0;
    const next_n = n - 1;
    if (next_n === 0) {
      return { _1: next_b_1, _2: next_b_2 };
    }
    b_1 = (next_b_2 + 3) | 0;
    b_2 = (next_b_1 + 4) | 0;
    n = next_n - 1;
  }
};
const testOdd = (n) => (b_1, b_2) => {
  if (n === 0) {
    return { _1: b_1, _2: b_2 };
  }
  return testEven(n - 1, (b_2 + 3) | 0, (b_1 + 4) | 0);
};
export { test1, test2, test3, test4, test5, testEven, testOdd };
