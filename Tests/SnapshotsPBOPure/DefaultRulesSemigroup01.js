const test1 = (f) => (g) => (x) => f(x) + g(x);
const test2 = (f) => (g) => (x) => {
  const fx = f(x);
  const gx = g(x);
  return fx + gx + fx + gx;
};
export { test1, test2 };
