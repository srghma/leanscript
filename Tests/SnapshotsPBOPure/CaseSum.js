const $SumType$L = (n) => ({
  tag: "L",
  _n: n,
});
const $SumType$R = (n) => ({
  tag: "R",
  _n: n,
});
const test1 = (v) => {
  if (v.tag === "L") {
    if (v._n === 1) {
      return "1";
    }
    if (v._n === 2) {
      return "2";
    }
    return "3";
  }
  if (v.tag === "R") {
    return "4";
  }
  throw new Error("UNREACHABLE");
};
export { $SumType$L, $SumType$R, test1 };
