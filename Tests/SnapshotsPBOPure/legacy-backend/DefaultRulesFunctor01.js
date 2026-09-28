const $Option$none = {
  tag: "none",
};
const $Option$some = (value0) => ({
  tag: "some",
  _val: value0,
});
const test1 = (mb) => {
  if (mb.tag === "some") {
    return $Option$some(mb._val);
  }
  return $Option$none;
};
const test2 = (mb) => {
  if (mb.tag === "some") {
    return $Option$some(undefined);
  }
  return $Option$none;
};
const test3 = (mb) => {
  if (mb.tag === "some") {
    return $Option$some(42);
  }
  return $Option$none;
};
const test4 = (mb) => {
  if (mb.tag === "some") {
    return $Option$some(42);
  }
  return $Option$none;
};
const test5 = (mb) => {
  if (mb.tag === "some") {
    return $Option$some(mb._val);
  }
  return $Option$none;
};
export { test1, test2, test3, test4, test5 };
