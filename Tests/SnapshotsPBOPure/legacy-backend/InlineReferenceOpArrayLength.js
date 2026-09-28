const test1 = (fn) => [1, 2, fn(undefined)];
const test2 = (fn) => [[1, 2, fn(undefined)], [3, 4], [fn(undefined)]];
const fn$p = (v) => 0;
const extern1 = [1, 2, /* #__PURE__ */ fn$p(undefined)];
const extern2 = [extern1, [3], [/* #__PURE__ */ fn$p(undefined)]];
const test3 = extern1;
const test4 = extern2;
export { extern1, extern2, fn$p, test1, test2, test3, test4 };
