const identity = (x) => x;
const fold = (dictFoldable) => (dictMonoid) =>
  dictFoldable.foldMap(dictMonoid)(identity);
const test = (v1) => {
  if (v1.tag === "none") {
    return "";
  }
  if (v1.tag === "some") {
    return v1._val;
  }
  throw new Error("UNREACHABLE");
};
export { fold, identity, test };
