// @inline export fromString arity=1
const $Test = (tag) => tag;
const Foo = /* #__PURE__ */ $Test("Foo");
const Bar = /* #__PURE__ */ $Test("Bar");
const Baz = /* #__PURE__ */ $Test("Baz");
const Qux = /* #__PURE__ */ $Test("Qux");
const fromString = (v) => {
  if (v === "foo") {
    return $Option$some(Foo);
  }
  if (v === "bar") {
    return $Option$some(Bar);
  }
  if (v === "baz") {
    return $Option$some(Baz);
  }
  if (v === "qux") {
    return $Option$some(Qux);
  }
  return $Option$none;
};
const test = (a) => {
  if (a === "foo") {
    return 1;
  }
  if (a === "bar") {
    return 2;
  }
  if (a === "baz") {
    return 3;
  }
  if (a === "qux") {
    return 4;
  }
  return 0;
};
export { $Test, Bar, Baz, Foo, Qux, fromString, test };
