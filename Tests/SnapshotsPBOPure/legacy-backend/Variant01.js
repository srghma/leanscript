import * as Partial from "../Partial/index.js";
const test1 = (r) => {
  if (r.type === "baz") {
    return r.value;
  }
  if (r.type === "bar") {
    if (r.value) {
      return "true";
    }
    return "false";
  }
  if (r.type === "foo") {
    return r.value.toString();
  }
  return Partial._crashWith(
    "Data.Variant: pattern match failure [" + r.type + "]",
  );
};
const test2 = (x, r) => {
  if (r.type === "foo") {
    return r.value.toString();
  }
  if (r.type === "bar") {
    if (r.value) {
      return "true";
    }
    return "false";
  }
  if (r.type === "baz") {
    return r.value;
  }
  return x(r);
};
const test3 = {
  type: "foo",
  value: 42,
};
export { test1, test2, test3 };
