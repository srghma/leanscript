// Tests of `MutualSlots.js`: a mutually tail-recursive pair whose parameters disagree on
// their types, so the merged loop gives them three slots — `Nat`, `Nat`, `String` — and
// shares a slot only where the two agree.  The answers are Lean's own
// (`scripts/expectations/MutualSlots.lean`).
import assert from "node:assert/strict";
import test from "node:test";

import { walkStr, walkNat } from "./MutualSlots.js";

test("walkStr answers as Lean does", () => {
  assert.equal(walkStr(0, "abc"), 3);
  assert.equal(walkStr(1, "abc"), 4);
  assert.equal(walkStr(2, "abc"), 2);
  assert.equal(walkStr(3, "abc"), 3);
  assert.equal(walkStr(8, "hello"), 2);
});

test("walkNat answers as Lean does", () => {
  assert.equal(walkNat(0, 5), 5);
  assert.equal(walkNat(1, 0), 0);
  assert.equal(walkNat(1, 3), 2);
  assert.equal(walkNat(2, 3), 3);
  assert.equal(walkNat(9, 7), 2);
});

test("the loop does not grow the stack", () => {
  assert.equal(walkStr(1000000, "abc"), 2);
  assert.equal(walkNat(1000001, 0), 2);
});
