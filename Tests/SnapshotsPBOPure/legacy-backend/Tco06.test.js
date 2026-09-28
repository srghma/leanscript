// Tests of `Tco06.js`: `f` and `g` are mutually tail-recursive on a fuel argument and
// share one loop; `g` enters it with the member tag and a padding argument.
import assert from "node:assert/strict";
import test from "node:test";

import { f, g } from "./Tco06.js";

test("f and g answer as Lean does", () => {
  assert.equal(f(0, 3, 4), 7);
  assert.equal(f(1, 3, 4), 7);
  assert.equal(f(5, 1, 1), 11);
  assert.equal(g(0, 7), 7);
  assert.equal(g(1, 7), 15);
  assert.equal(g(4, 2), 11);
});

test("the shared loop does not grow the stack", () => {
  assert.equal(typeof f(1000000, 0, 0), "number");
});
