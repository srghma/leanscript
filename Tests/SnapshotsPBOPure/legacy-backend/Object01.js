const test1 = (a) => a.foo;
const test2 = (a) => a["foo.bar"];
const test3 = (a) => (b) => a[b];
const test4 = (obj) => Object.keys(obj);
const test5 = (obj) => Object.hasOwn(obj, "wat");
export { test1, test2, test3, test4, test5 };
