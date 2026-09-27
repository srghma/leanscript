// Tests of the JavaScript `GcdEntry.js` the backend emits from `GcdEntry.lean`.
// The expected values are the ones Lean itself answers with (`#eval`, see
// `scripts/expectations/GcdEntry.lean`).
import assert from "node:assert/strict";
import test from "node:test";

import { gcd2, run } from "./GcdEntry.js";

test("run is gcd2 48 18, computed once at load time", () => {
  assert.equal(run, 6);
});

test("gcd2 is Nat.gcd", () => {
  assert.equal(gcd2(48, 18), 6);
  assert.equal(gcd2(0, 7), 7);
  assert.equal(gcd2(12, 18), 6);
  assert.equal(gcd2(7, 0), 7);
  assert.equal(gcd2(0, 0), 0);
});
