const test1 = (x) => {
  if (x > 42) {
    return ["Hello, World", "Hello, Universe"];
  }
  throw new Error("UNREACHABLE");
};
const test2 = (f, x) => {
  if (x > 42) {
    return f("Hello, World")("Hello, Universe");
  }
  throw new Error("UNREACHABLE");
};
const test3 = (x) => {
  if (x > 42) {
    return false;
  }
  throw new Error("UNREACHABLE");
};
export { test1, test2, test3 };
