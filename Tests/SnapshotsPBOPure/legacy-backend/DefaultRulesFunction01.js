const test1 = (f) => (g) => (_unit) => f(1)(g("foo")());
const test2 = (f) => (g) => (_unit) => f(1)(g("foo")());
const test3 = (f) => (g) => (_ignored) => f(g(1)(2))(3);
const test4 = (f) => (b) => (a) => f(a)(b);
const test5 = (a) => (_ignored) => a;
const test6 = (a) => a;
export { test1, test2, test3, test4, test5, test6 };
