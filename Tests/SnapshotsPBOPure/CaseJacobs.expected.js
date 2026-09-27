const $Expr$add = (value0) => (value1) => ({
  tag: "add",
  _a: value0,
  _b: value1,
});
const $Expr$mul = (value0) => (value1) => ({
  tag: "mul",
  _a: value0,
  _b: value1,
});
const $Expr$succ = (value0) => ({
  tag: "succ",
  _a: value0,
});
const $Expr$zero = {
  tag: "zero",
};
const renderExpr = (v) => {
  if (v.tag === "add") {
    return "Add(" + renderExpr(v._a) + " " + renderExpr(v._b) + ")";
  }
  if (v.tag === "mul") {
    return "Mul(" + renderExpr(v._a) + " " + renderExpr(v._b) + ")";
  }
  if (v.tag === "succ") {
    return "Succ(" + renderExpr(v._a) + ")";
  }
  if (v.tag === "zero") {
    return "Zero";
  }
  throw new Error("UNREACHABLE");
};
const instToStringExpr_toString = renderExpr;
const test1 = (v) => {
  if (v.tag === "add") {
    if (v._b.tag === "zero") {
      if (v._a.tag === "zero") {
        return "e1";
      }
      if (v._a.tag === "succ") {
        return "e3: " + renderExpr(v._a._a) + " " + renderExpr(v._b);
      }
      return "e6: " + renderExpr(v._a);
    }
    if (v._a.tag === "succ") {
      return "e3: " + renderExpr(v._a._a) + " " + renderExpr(v._b);
    }
    return "e7: " + renderExpr(v);
  }
  if (v.tag === "mul") {
    if (v._a.tag === "zero") {
      return "e2: " + renderExpr(v._b);
    }
    if (v._b.tag === "zero") {
      return "e4: " + renderExpr(v._a);
    }
    if (v._a.tag === "add") {
      return (
        "e5: " +
        renderExpr(v._a._a) +
        " " +
        renderExpr(v._a._b) +
        " " +
        renderExpr(v._b)
      );
    }
  }
  return "e7: " + renderExpr(v);
};
export {
  $Expr$add,
  $Expr$mul,
  $Expr$succ,
  $Expr$zero,
  instToStringExpr_toString,
  test1,
};
