// Tests of `CaseJacobs.js`.  An `Expr` is `{ tag, _1, _2 }`, the constructor number in
// declaration order: 0 = `add`, 1 = `mul`, 2 = `succ`, 3 = `zero`.  The expected answers
// below are the ones Lean itself gives for the same arguments.
import assert from "node:assert/strict";
import test from "node:test";

import { instToStringExpr_toString, renderExpr, test1 } from "./CaseJacobs.js";

const add = (a, b) => ({ tag: 0, _1: a, _2: b });
const mul = (a, b) => ({ tag: 1, _1: a, _2: b });
const succ = (a) => ({ tag: 2, _1: a });
const zero = { tag: 3 };

test("renderExpr prints the tree", () => {
  assert.equal(renderExpr(zero), "Zero");
  assert.equal(renderExpr(succ(zero)), "Succ(Zero)");
  assert.equal(
    renderExpr(add(mul(succ(zero), zero), succ(succ(zero)))),
    "Add(Mul(Succ(Zero) Zero) Succ(Succ(Zero)))",
  );
});

test("test1 takes the branch the overlapping patterns select", () => {
  assert.equal(test1(add(zero, zero)), "e1");
  assert.equal(test1(mul(zero, succ(zero))), "e2: Succ(Zero)");
  assert.equal(test1(add(succ(zero), mul(zero, zero))), "e3: Zero Mul(Zero Zero)");
  assert.equal(test1(mul(succ(zero), zero)), "e4: Succ(Zero)");
  assert.equal(test1(mul(add(zero, succ(zero)), succ(zero))), "e5: Zero Succ(Zero) Succ(Zero)");
  assert.equal(test1(add(mul(zero, zero), zero)), "e6: Mul(Zero Zero)");
  assert.equal(test1(succ(zero)), "e7: Succ(Zero)");
  assert.equal(test1(zero), "e7: Zero");
});

test("the ToString instance is the renderer itself", () => {
  assert.equal(instToStringExpr_toString, renderExpr);
});
