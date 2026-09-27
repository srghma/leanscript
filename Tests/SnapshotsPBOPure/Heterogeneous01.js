const test1 = {
  a: 13,
  b: {
    fst: "bar",
    snd: 42.0,
  },
  c: false,
};
const test2 = (r1) => ({
  a: (1 + r1.a) | 0,
  b: {
    fst: "bar",
    snd: r1.b,
  },
  c: !r1.c,
});
export { test1, test2 };
