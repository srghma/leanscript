// Tests of `Tco03.js`: two mutually tail-recursive functions, merged into one loop.
// The proof argument of `k` is erased, so `k` takes one argument in JavaScript.
import assert from "node:assert/strict";
import test from "node:test";

import { go, k } from "./Tco03.js";

test("go counts down, and answers 42 only through the 900 of k", () => {
  assert.equal(go(0), 0);
  assert.equal(go(5), 0);
  assert.equal(go(100), 0);
  assert.equal(go(101), 0);
  assert.equal(go(1000), 42);
});

test("k counts down to 100 and then hands over to go", () => {
  assert.equal(k(100), 0);
  assert.equal(k(101), 0);
  assert.equal(k(900), 42);
  assert.equal(k(1000), 42);
});
