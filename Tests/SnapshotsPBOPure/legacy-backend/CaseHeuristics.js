const $Column$zero = {
  tag: "zero",
};
const $Column$one = (value0) => ({
  tag: "one",
  _n: value0,
});
const $Column$two = (value0) => (value1) => ({
  tag: "two",
  _a: value0,
  _b: value1,
});
const testP = (v) => (v1) => (v2) => {
  if (v1 === 2) {
    if (v === 1) {
      if (v2 === 1) {
        return 1;
      }
      if (v2 === 2) {
        return 2;
      }
      if (v2 === 3) {
        return 3;
      }
      if (v2 === 4) {
        return 4;
      }
      return 5;
    }
    if (v2 === 3) {
      return 3;
    }
    return 5;
  }
  if (v === 1 && v2 === 4) {
    return 4;
  }
  return 5;
};
const testPB = (v) => (v1) => {
  if (v.tag === "one") {
    if (v._n === 1 && v1.tag === "one") {
      if (v1._n === 1) {
        return 1;
      }
      return 4;
    }
    if (v1.tag === "zero") {
      return 3;
    }
    return 4;
  }
  if (v.tag === "two" && v._a === 2 && v._b === 3 && v1.tag === "two") {
    if (v1._a === 2 && v1._b === 3) {
      return 2;
    }
    return 4;
  }
  if (v1.tag === "zero") {
    return 3;
  }
  return 4;
};
const testPBA = (v) => (v1) => {
  if (v1.tag === "one") {
    if (v.tag === "one") {
      if (v._n === 1) {
        if (v1._n === 1) {
          return 1;
        }
        return 4;
      }
      if (v._n === 2 && v1._n === 2) {
        return 2;
      }
    }
    return 4;
  }
  if (v.tag === "two" && v._a === 1 && v1.tag === "two") {
    return 3;
  }
  return 4;
};
const testPBAN = (v) => (v1) => {
  if (v.tag === "one") {
    if (v1.tag === "one") {
      if (v._n === 1) {
        if (v1._n === 1) {
          return 1;
        }
        return 4;
      }
      if (v._n === 2 && v1._n === 2) {
        return 2;
      }
    }
    return 4;
  }
  if (v.tag === "two" && v1.tag === "two") {
    return 3;
  }
  return 4;
};
export {
  $Column$one,
  $Column$two,
  $Column$zero,
  testP,
  testPB,
  testPBA,
  testPBAN,
};
