const test1 = f => {
  const $0 = f();
  return v2 => {
    if (v2.tag === "none") { return $0; }
    if (v2.tag === "some") { return 1 + v2._val | 0; }
    throw new Error("UNREACHABLE");
  };
};
const test2 = f => g => {
  const $0 = f();
  const $1 = g(1);
  return v2 => {
    if (v2.tag === "none") { return $0; }
    if (v2.tag === "some") { return $1(v2._val); }
    throw new Error("UNREACHABLE");
  };
};
const test3 = f => v2 => {
  if (v2.tag === "none") { return f(); }
  if (v2.tag === "some") { return 1 + v2._val | 0; }
  throw new Error("UNREACHABLE");
};
const test4 = f => g => {
  const $0 = g(1);
  return v2 => {
    if (v2.tag === "none") { return f(); }
    if (v2.tag === "some") { return $0(v2._val); }
    throw new Error("UNREACHABLE");
  };
};
const test5 = a => g => {
  const $0 = g(1);
  return v2 => {
    if (v2.tag === "none") { return a + 1 | 0; }
    if (v2.tag === "some") { return $0(v2._val); }
    throw new Error("UNREACHABLE");
  };
};
export { test1, test2, test3, test4, test5 };
