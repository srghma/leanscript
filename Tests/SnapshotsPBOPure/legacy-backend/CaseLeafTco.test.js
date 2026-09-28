// Tests of `CaseLeafTco.js`.  An `Array Int` is a JavaScript array of numbers, and
// `test1Fuel` is a `while` loop: it walks until the fuel runs out or the array's first
// and last elements are 1 and 2.  `test1FuelCalled` is the same with a fuel of 1000000.
// The expected answers are the ones Lean gives for the same arguments.
import assert from "node:assert/strict";
import test from "node:test";

import { test1Fuel, test1FuelCalled } from "./CaseLeafTco.js";

// One step of the Lean definition, for the arguments where it does not recur.
const prefixOf = (x, y) => [y, x, 3, y, 5, 6, 7, 8, 9, 10, x, 12, 13, 14, 15, 16, 17];

test("no fuel answers with the array itself", () => {
  assert.deepEqual(test1Fuel(0, false, [1, 2, 3]), [1, 2, 3]);
  assert.deepEqual(test1Fuel(0, true, []), []);
});

test("the empty array is a fixed point, and 1 … 2 stops the walk", () => {
  assert.deepEqual(test1Fuel(3, false, []), []);
  assert.deepEqual(test1Fuel(3, false, [1, 2]), [1, 2]);
  assert.deepEqual(test1FuelCalled(false, [1, 9, 2]), [1, 9, 2]);
});

test("the flag answers with the empty array at the first step", () => {
  assert.deepEqual(test1Fuel(1, true, [5, 6]), []);
  assert.deepEqual(test1FuelCalled(true, [5, 6]), []);
});

test("without the flag a step prepends the seventeen-element block", () => {
  assert.deepEqual(test1Fuel(1, false, [5, 6]), [...prefixOf(5, 6), 5, 6]);
  assert.deepEqual(test1Fuel(5, false, [7]), [
    ...prefixOf(7, 7),
    ...prefixOf(7, 7),
    ...prefixOf(7, 7),
    ...prefixOf(7, 7),
    ...prefixOf(7, 7),
    7,
  ]);
  // each step adds seventeen elements
  assert.equal(test1Fuel(2, false, [5, 6]).length, 36);
});

test("the walk is a loop: a large fuel does not grow the stack", () => {
  // `[1, …, 2]` stops at once, whatever the fuel is
  assert.deepEqual(test1Fuel(1000000000, false, [1, 2]), [1, 2]);
  // 2000 steps of the growing walk, all in the one `while` loop
  assert.equal(test1Fuel(2000, false, [7]).length, 2000 * 17 + 1);
});
