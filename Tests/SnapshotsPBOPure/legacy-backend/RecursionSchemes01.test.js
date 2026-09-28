// Tests of `RecursionSchemes01.js`.  `FixExpr` is a structure with one runtime field, so
// the wrapper is erased: a `FixExpr` is just its `ExprF FixExpr`, that is
// `{ tag: 0, _1: n }` for `Lit`, `{ tag: 1, _1, _2 }` for `Add` and `{ tag: 2, _1, _2 }`
// for `Mul`.  The expected answers are the ones Lean gives for the same trees.
import assert from "node:assert/strict";
import test from "node:test";

import {
  bump,
  cata,
  eval$,
  instFunctorExprF_mapConst,
  mapExprF,
  test1,
  test2,
} from "./RecursionSchemes01.js";

const lit = (n) => ({ tag: 0, _1: n });
const addE = (a, b) => ({ tag: 1, _1: a, _2: b });
const mulE = (a, b) => ({ tag: 2, _1: a, _2: b });

// 2 + 3 * 4
const sample = addE(lit(2), mulE(lit(3), lit(4)));
// (1 + 2) * (-5)
const sample2 = mulE(addE(lit(1), lit(2)), lit(-5));

test("test1 folds the tree with eval", () => {
  assert.equal(test1(sample), 14);
  assert.equal(test1(lit(7)), 7);
  assert.equal(test1(sample2), -15);
});

test("test2 folds with eval after bumping every literal", () => {
  assert.equal(test2(sample), 23);
  assert.equal(test2(lit(7)), 8);
  assert.equal(test2(sample2), -20);
});

test("eval is the one-layer algebra", () => {
  assert.equal(eval$(lit(9)), 9);
  assert.equal(eval$(addE(3, 4)), 7);
  assert.equal(eval$(mulE(3, 4)), 12);
});

test("bump adds one to a literal and leaves the other nodes alone", () => {
  assert.deepEqual(bump(lit(9)), lit(10));
  assert.deepEqual(bump(addE(3, 4)), addE(3, 4));
});

test("mapExprF maps the children, and cata takes any algebra", () => {
  assert.deepEqual(mapExprF((x) => x + 1, addE(3, 4)), addE(4, 5));
  assert.deepEqual(mapExprF((x) => x + 1, lit(3)), lit(3));
  // the algebra that counts the nodes of the tree
  const size = (e) => (e.tag === 0 ? 1 : e._1 + e._2 + 1);
  assert.equal(cata(size, sample), 5);
});

test("the Functor instance's mapConst replaces every child", () => {
  assert.deepEqual(instFunctorExprF_mapConst(5, addE(1, 2)), addE(5, 5));
  assert.deepEqual(instFunctorExprF_mapConst(5, lit(1)), lit(1));
});
