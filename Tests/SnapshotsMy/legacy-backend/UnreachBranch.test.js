// Tests of `UnreachBranch.js`.  The proof arguments of `small` and `headOf` are erased,
// so each takes one argument; the branch Lean can only rule out by a proof carries no
// value and is not emitted at all.
import assert from "node:assert/strict";
import test from "node:test";

import { headOf, small, test as testFn } from "./UnreachBranch.js";
import { list } from "../runtime/lean_values.mjs";

test("small answers on the three reachable arguments", () => {
  assert.equal(small(0), 10);
  assert.equal(small(1), 20);
  assert.equal(small(2), 30);
});

test("headOf reads the head of a non-empty list", () => {
  assert.equal(headOf(list([7])), 7);
  assert.equal(headOf(list([1, 2, 3])), 1);
});

test("test uses both, and answers 0 outside the range of small", () => {
  assert.equal(testFn(0), 10);
  assert.equal(testFn(1), 21);
  assert.equal(testFn(2), 32);
  assert.equal(testFn(3), 0);
  assert.equal(testFn(10), 0);
});
