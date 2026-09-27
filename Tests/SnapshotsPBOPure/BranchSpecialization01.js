const instBEqTestEnum_beq = (x) => (y) => {
  if (x === "foo") {
    return y === "foo";
  }
  if (x === "bar") {
    return y === "bar";
  }
  if (x === "baz") {
    return y === "baz";
  }
  return x === "qux" && y === "qux";
};
const test1 = (a) => a === "baz";
const test2 = (a) => a === "baz";
export { instBEqTestEnum_beq, test1, test2 };
