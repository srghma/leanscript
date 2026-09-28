// Tests of `CaptureDerefRegression01.js`.  An `Int × Int` and a `Box2 Int` are both
// `{ tag: 0, _1, _2 }`, and `Box`, which has one field, is erased: `test3` answers with
// the function itself.  `testEven` and `testOdd` are one merged dispatch loop, entered
// through a wrapper each, so neither uses the stack.
import assert from "node:assert/strict";
import test from "node:test";

import {
  test1,
  test2,
  test3,
  test4,
  test5,
  testEven,
  testOdd,
} from "./CaptureDerefRegression01.js";

const pair = (a, b) => ({ tag: 0, _1: a, _2: b });

test("test1, test2 and test3 all add the first component to their argument", () => {
  assert.equal(test1(pair(3, 4), 10), 13);
  assert.equal(test2(pair(3, 4), 10), 13);
  // test3 answers with a `Box` of the function, and the `Box` wrapper is erased
  assert.equal(test3(pair(3, 4))(10), 13);
  assert.equal(test1(pair(-3, 4), 10), 7);
});

test("test4 and test5 answer with a pair of the two closures", () => {
  for (const f of [test4, test5]) {
    const b = f(pair(3, 4));
    assert.equal(b.tag, 0);
    assert.equal(b._1(10), 13);
    assert.equal(b._2(10), 14);
  }
});

// `testEven n (x, y)` swaps the components and adds (1, 2) at an even step and (3, 4) at
// an odd one; `testOdd` is the same walk started at the odd step.
const reference = (even, n, x, y) => {
  while (n > 0) {
    [x, y] = even ? [y + 1, x + 2] : [y + 3, x + 4];
    even = !even;
    n -= 1;
  }
  return [x, y];
};

test("testEven and testOdd agree with the Lean recursion", () => {
  assert.deepEqual(testEven(0, pair(10, 20)), pair(10, 20));
  assert.deepEqual(testEven(1, pair(10, 20)), pair(21, 12));
  assert.deepEqual(testEven(2, pair(10, 20)), pair(15, 25));
  assert.deepEqual(testOdd(1, pair(10, 20)), pair(23, 14));
  assert.deepEqual(testEven(3, pair(0, 0)), pair(6, 7));
});

test("the two mutually recursive functions agree with the reference walk", () => {
  for (const n of [0, 1, 2, 3, 7, 40]) {
    for (const [x, y] of [[0, 0], [10, 20], [-5, 7]]) {
      const [ex, ey] = reference(true, n, x, y);
      assert.deepEqual(testEven(n, pair(x, y)), pair(ex, ey));
      const [ox, oy] = reference(false, n, x, y);
      assert.deepEqual(testOdd(n, pair(x, y)), pair(ox, oy));
    }
  }
});

test("the merged loop does not grow the stack", () => {
  const [x, y] = reference(true, 100000, 0, 0);
  assert.deepEqual(testEven(100000, pair(0, 0)), pair(x, y));
});
