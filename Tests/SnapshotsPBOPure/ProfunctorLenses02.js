// @inline Data.Lens.Internal.Forget.choiceForget(..).left arity=1
// @inline Data.Lens.Internal.Forget.choiceForget(..).right arity=1

const test1 = (v2) => {
  if (v2.tag === "error") {
    return $Option$some(v2._1);
  }
  if (v2.tag === "ok") {
    return $Option$none;
  }
  throw new Error("UNREACHABLE");
};
const test2 = (a) => {
  if (a.tag === "error") {
    return $Option$some(a._1);
  }
  if (a.tag === "ok") {
    return $Option$none;
  }
  throw new Error("UNREACHABLE");
};
const test3 = (v2) => {
  if (v2.tag === "error") {
    if (v2._1.tag === "error") {
      return $Option$none;
    }
    if (v2._1.tag === "ok") {
      return $Option$some(v2._1._1);
    }
    throw new Error("UNREACHABLE");
  }
  if (v2.tag === "ok") {
    return $Option$none;
  }
  throw new Error("UNREACHABLE");
};
const test4 = (a) => {
  if (a.tag === "error") {
    if (a._1.tag === "error") {
      return $Option$none;
    }
    if (a._1.tag === "ok") {
      return $Option$some(a._1._1);
    }
    throw new Error("UNREACHABLE");
  }
  if (a.tag === "ok") {
    return $Option$none;
  }
  throw new Error("UNREACHABLE");
};
export { test1, test2, test3, test4 };
