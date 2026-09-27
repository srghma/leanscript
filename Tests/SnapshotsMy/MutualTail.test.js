// Tests of `MutualTail.js`: two mutually tail-recursive groups, each compiled into one
// dispatch loop that every member of the group enters with its own tag.  The loop must
// not grow the JavaScript stack, which the large arguments below check.
import assert from "node:assert/strict";
import test from "node:test";

import { test1, test2, test3, test4, test5 } from "./MutualTail.js";

test("test1 and test2 decide the parity of their argument", () => {
  assert.equal(test1(0), true);
  assert.equal(test1(1), false);
  assert.equal(test1(2), true);
  assert.equal(test1(7), false);
  assert.equal(test2(0), false);
  assert.equal(test2(1), true);
  assert.equal(test2(2), false);
  assert.equal(test2(7), true);
});

test("the three-member group answers as Lean does", () => {
  assert.equal(test3(0, 5), 5);
  assert.equal(test3(1, 0), 1);
  assert.equal(test3(5, 0), 9);
  assert.equal(test3(10, 1), 20);
  assert.equal(test4(0, 5, 2), 5);
  assert.equal(test4(3, 0, 4), 8);
  assert.equal(test4(7, 1, 2), 15);
  assert.equal(test5(0, 9), 9);
  assert.equal(test5(4, 0), 9);
  assert.equal(test5(9, 2), 20);
});

test("the dispatch loop does not grow the stack", () => {
  // Lean's own interpreter overflows on these: it does not eliminate the tail calls.
  // `test3` adds 1, then 2, then 3, once per step, so a million steps add
  // 333333 * 6 + 1.
  assert.equal(test1(1000000), true);
  assert.equal(test3(1000000, 0), 1999999);
});
