const test1 = (x) => ["a", "b", ...x, ...x, ...x, ...x, "c", "d"];
const test2 = (x) => ["a", "b", ...x, ...x, ...x, ...x, "c", "d"];
const test3 = (x) => [
  "a",
  "b",
  ...x,
  ...x,
  ...x,
  ...x,
  "c",
  "d",
  "e",
  ...x,
  ...x,
  ...x,
  ...x,
  "f",
  "g",
];
export { test1, test2, test3 };
