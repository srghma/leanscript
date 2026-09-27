const test = (comp) => (a) => (b) => {
  return comp(a)(b) !== "eq";
};
export { test };
