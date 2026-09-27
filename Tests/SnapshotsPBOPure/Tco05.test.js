// Tests of `Tco05.js`: `span p arr` answers with the position of the first element the
// predicate rejects, and `none` when it accepts all of them.  An `Array Int` is a
// JavaScript array of numbers and an `Option Nat` is `{ tag: 0 }` / `{ tag: 1, _1: n }`.
import assert from "node:assert/strict";
import test from "node:test";

import { span, span_go } from "./Tco05.js";
import { none, some } from "../runtime/lean_values.mjs";

const positive = (x) => x > 0;

test("span finds the first element the predicate rejects", () => {
  assert.deepEqual(span(positive, [1, 2, 3]), none);
  assert.deepEqual(span(positive, [1, -2, 3]), some(1));
  assert.deepEqual(span(positive, []), none);
  assert.deepEqual(span((x) => x < 0, [1]), some(0));
});

test("span_go starts the walk wherever it is told to", () => {
  assert.deepEqual(span_go(positive, [1, -2, 3], 2), none);
  assert.deepEqual(span_go(positive, [1, -2, 3], 0), some(1));
});

test("the loop does not grow the stack", () => {
  const big = new Array(200000).fill(1);
  assert.deepEqual(span(positive, big), none);
});
