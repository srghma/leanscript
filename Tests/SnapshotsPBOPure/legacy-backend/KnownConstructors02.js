const test = (a) => {
  if (a.tag === "error") {
    return a._1;
  }
  if (a.tag === "ok") {
    return a._1;
  }
  throw new Error("UNREACHABLE");
};
export { test };
