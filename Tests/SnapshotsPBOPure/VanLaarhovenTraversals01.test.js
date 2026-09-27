// Tests of `VanLaarhovenTraversals01.js`.
//
// `Fun` has two constructors and both are recursive (`Abs : String → Fun → Fun` and
// `App : Fun → Fun → Fun`), so the type has no closed value at all: in Lean, `Fun → False`
// is provable.  Nothing can therefore be handed to `Fun_size`, `rewriteBottomUp` or the
// `DecidableEq` instance, and the tests below check what *is* observable: the shape of
// the module, and the one-layer traversal, which never looks inside the children it is
// given and so can be run on a node whose child is an opaque marker.
//
// A `Fun` node is `{ tag: 0, _1: name, _2: body }` for `Abs` and `{ tag: 1, _1, _2 }` for
// `App`.  The `Applicative` argument is unboxed into its five fields, in order: the
// `Functor` sub-dictionary (itself `{ _1: map, _2: mapConst }`), `pure`, `seq`, `seqLeft`
// and `seqRight`.
import assert from "node:assert/strict";
import test from "node:test";

import * as mod from "./VanLaarhovenTraversals01.js";

// The identity applicative, in the backend's calling convention.
const functorId = { _1: (f, x) => f(x), _2: (a, _x) => a };
const pureId = (x) => x;
const seqId = (f, thunk) => f(thunk());
const seqLeftId = (a, _thunk) => a;
const seqRightId = (_a, thunk) => thunk();
const idDict = [functorId, pureId, seqId, seqLeftId, seqRightId];

test("the module binds the declarations of the Lean file", () => {
  for (const name of [
    "Fun_size",
    "traverseFun1",
    "traverseFun1D",
    "rewriteBottomUp",
    "rewriteBottomUpM",
    "instReprFun_repr",
    "instReprFun_reprPrec",
    "instDecidableEqFun",
    "instDecidableEqFun_decEq",
  ]) {
    assert.equal(typeof mod[name], "function", `${name} is not exported as a function`);
  }
  // the `Applicative` dictionary is five arguments, then the callback and the node
  assert.equal(mod.traverseFun1.length, 7);
  assert.equal(mod.traverseFun1D.length, 7);
  // `reprPrec` and `decEq` are the instances themselves, with no wrapper
  assert.equal(mod.instReprFun_reprPrec, mod.instReprFun_repr);
  assert.equal(mod.instDecidableEqFun, mod.instDecidableEqFun_decEq);
});

test("traverseFun1 rebuilds an Abs node around the answer of the callback", () => {
  const k = (child) => `k(${child})`;
  const out = mod.traverseFun1(...idDict, k, { tag: 0, _1: "x", _2: "body" });
  assert.deepEqual(out, { tag: 0, _1: "x", _2: "k(body)" });
});

test("traverseFun1D is traverseFun1 with the size proof erased", () => {
  // the dependent version takes the node before the callback, and the proof the callback
  // is handed carries nothing at run time, so the callback still takes one argument
  const k = (child) => `k(${child})`;
  const out = mod.traverseFun1D(...idDict, { tag: 0, _1: "x", _2: "body" }, k);
  assert.deepEqual(out, mod.traverseFun1(...idDict, k, { tag: 0, _1: "x", _2: "body" }));
});
