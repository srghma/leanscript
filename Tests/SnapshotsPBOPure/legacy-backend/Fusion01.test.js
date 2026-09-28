// Tests of `Fusion01.js`, the fold-based (Church-encoded) stream pipeline.  An
// `Array Int` is a JavaScript array of numbers, an `Array String` one of strings, and an
// `Option String` is `{ tag: 0 }` / `{ tag: 1, _1: s }`.  The expected answers are the
// ones Lean gives for the same arguments.
import assert from "node:assert/strict";
import test from "node:test";

import { dropPrefix1, test as pipeline } from "./Fusion01.js";
import { none, some } from "../runtime/lean_values.mjs";

test("dropPrefix1 strips a leading '1' and rejects anything else", () => {
  assert.deepEqual(dropPrefix1("123"), some("23"));
  assert.deepEqual(dropPrefix1("1"), some(""));
  assert.deepEqual(dropPrefix1("23"), none);
  assert.deepEqual(dropPrefix1(""), none);
});

// The pipeline is: add one, render, keep the renderings that start with '1' and drop that
// '1', prefix "2", keep everything but "wat", append "1".
test("the fused pipeline agrees with Lean", () => {
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
