// Tests of `Tco04.js`: a mutually recursive pair over `Int` whose termination Lean
// proves from a hypothesis that the argument is valid.  The proof is erased, so each
// function takes the number alone — but it may only be called where Lean could: `test1`
// on an `n ≥ 1` with `n % 3 ∈ {0, 1}`, `test2` on an `m ≥ 2` with `m % 3 ∈ {0, 2}`.
import assert from "node:assert/strict";
import test from "node:test";

import { test1, test2 } from "./Tco04.js";

test("test1 walks down to 1, or to 2 when the walk lands on test2's base case", () => {
  assert.equal(test1(1), 1);
  // 3 is `test2 2`, which is `test2`'s own base case, so the answer is 2 and not 1
  assert.equal(test1(3), 2);
  assert.equal(test1(4), 1);
  assert.equal(test1(7), 1);
  assert.equal(test1(10), 1);
});

test("test2 walks down to 2", () => {
  assert.equal(test2(2), 2);
  assert.equal(test2(5), 2);
  assert.equal(test2(11), 2);
});
