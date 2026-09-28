const test1 = (v) => {
  const $0 = v.toString();
  if (v === 1) {
    return $0 + $0 + $0;
  }
  if (v === 2) {
    return $0;
  }
  return "any: " + $0 + $0 + $0;
};
const test2 = (v) => {
  const $0 = v._1.toString();
  const $1 = v._2.toString();
  const $2 = v._3.toString();
  if (v._1 === 1) {
    return $1 + $2 + $0;
  }
  if (v._2 === 1) {
    return $0 + $2 + $1;
  }
  if (v._3 === 1) {
    return $0 + $1 + $2;
  }
  return $0 + $0 + $1 + $1 + $2 + $2;
};
export { test1, test2 };
