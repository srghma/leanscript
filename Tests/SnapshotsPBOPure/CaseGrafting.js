const test1 = (v) => (v1) => (v2) => {
  if (!v1) {
    if (v2) {
      return 1;
    }
    return 3;
  }
  if (!v && v1) {
    return 2;
  }
  if (!v2) {
    return 3;
  }
  if (v2) {
    return 4;
  }
  throw new Error("UNREACHABLE");
};
export { test1 };
