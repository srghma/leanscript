// Tests of `Tco01.js`: a self-tail-recursive function, compiled into a `while` loop.
import assert from "node:assert/strict";
import test from "node:test";

import { test as testFn } from "./Tco01.js";

test("test counts down to zero", () => {
  assert.equal(testFn(0), 0);
  assert.equal(testFn(5), 0);
  assert.equal(testFn(100), 0);
});

test("the loop does not grow the stack", () => {
  assert.equal(testFn(10000000), 0);
});
