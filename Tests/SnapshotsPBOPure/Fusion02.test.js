// Tests of `Fusion02.js`, the unfold-based (pull) stream pipeline.  An `Unfold` is
// `{ tag: 0, _1: seed, _2: step, _3: measure }` — its `State` field is a type and its
// `decreasing` field is a proof, so both are erased — and `step` answers
// `{ tag: 0 }` or `{ tag: 1, _1: { tag: 0, _1: nextState, _2: element } }`.  The
// expected answers are the ones Lean gives for the same arguments.
import assert from "node:assert/strict";
import test from "node:test";

import {
  dropPrefix1,
  filterU,
  fromArray,
  mapU,
  test as pipeline,
  toArray,
} from "./Fusion02.js";
import { none, some } from "../runtime/lean_values.mjs";

test("dropPrefix1 strips a leading '1' and rejects anything else", () => {
  assert.deepEqual(dropPrefix1("123"), some("23"));
  assert.deepEqual(dropPrefix1("1"), some(""));
  assert.deepEqual(dropPrefix1("23"), none);
});

test("the pipeline agrees with Lean", () => {
  assert.deepEqual(pipeline([0, 9, 10, 1]), ["21", "201", "211"]);
  assert.deepEqual(pipeline([0, 1, 9, 10, 99, 111]), ["21", "201", "211", "2001", "2121"]);
  assert.deepEqual(pipeline([]), []);
  assert.deepEqual(pipeline([5, 6, 7]), []);
});

test("the pipeline is the composition it is meant to be", () => {
  const reference = (arr) =>
    arr
      .map((x) => x + 1)
      .map((x) => String(x))
      .flatMap((s) => (s.startsWith("1") ? [s.slice(1)] : []))
      .map((s) => "2" + s)
      .filter((s) => s !== "wat")
      .map((s) => s + "1");
  for (const arr of [[], [0], [9, 10, 11], [-1, 0, 1, 2, 3], [100, 199, 200]]) {
    assert.deepEqual(pipeline(arr), reference(arr));
  }
});

test("fromArray and toArray are inverse, and the combinators do their job", () => {
  const arr = [1, 2, 3, 4, 5];
  assert.deepEqual(toArray(fromArray(arr)), arr);
  assert.deepEqual(toArray(mapU((x) => x * 2, fromArray(arr))), [2, 4, 6, 8, 10]);
  assert.deepEqual(toArray(filterU((x) => x % 2 === 1, fromArray(arr))), [1, 3, 5]);
  assert.deepEqual(toArray(fromArray([])), []);
});

// `toArrayLoop` is a `while` loop, so the length below is bounded by time and not by the
// stack: the loop copies the accumulator on every push, so the walk is quadratic.
test("toArray walks a long stream without growing the stack", () => {
  const big = Array.from({ length: 2000 }, (_, i) => i);
  const out = toArray(mapU((x) => x + 1, fromArray(big)));
  assert.equal(out.length, 2000);
  assert.equal(out[1999], 2000);
});
