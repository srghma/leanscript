const test1 = (f, g) => {
  const $0 = f();
  const $1 = g();
  return (x) => $0($1(x));
};
const test2 = (f, g) => {
  const $0 = g();
  const $1 = f();
  return (x) => $0($1($0(x)));
};
const test3 = (f, g) => {
  const $0 = f();
  const $1 = g();
  return (x) => $0($1($0($1(x))));
};
const test4 = (f, g) => {
  const $0 = g();
  const $1 = f();
  return (x) => $0($1($0($1($0(x)))));
};
export { test1, test2, test3, test4 };
