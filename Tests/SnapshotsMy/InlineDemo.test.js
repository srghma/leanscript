// Tests of `InlineDemo.js`.  Inlining a call must not change what the module computes:
// `useScale`, whose calls were inlined, and `useTriple`, whose calls were not, answer
// the same as the Lean declarations they come from.
import assert from "node:assert/strict";
import test from "node:test";

import { bar, foo, triple, useScale, useTriple } from "./InlineDemo.js";
import { readFileSync } from "node:fs";

const source = readFileSync(new URL("./InlineDemo.js", import.meta.url), "utf8");

test("bar is `foo 1 2`, computed at compile time", () => {
  assert.equal(bar, 3);
});

test("foo is still exported, and is still a * b + a", () => {
  assert.equal(foo(1, 2), 3);
  assert.equal(foo(4, 5), 24);
});

test("useScale answers as `scale n + scale (n + 1)` does", () => {
  for (const n of [0, 1, 2, 7, 100]) {
    assert.equal(useScale(n), n * 2 + (n + 1) * 2);
  }
});

test("useTriple answers as `triple n + triple (n + 1)` does", () => {
  for (const n of [0, 1, 2, 7, 100]) {
    assert.equal(useTriple(n), triple(n) + triple(n + 1));
    assert.equal(useTriple(n), n * 3 + (n + 1) * 3);
  }
});

test("the module does not bind `scale`: every call site took a copy of its body", () => {
  assert.ok(!source.includes("scale = ") || source.includes("useScale = "));
  assert.ok(!/\bconst scale\b/.test(source));
});

test("a call of the `@[noinline]` declaration is still a call", () => {
  assert.ok(source.includes("triple(v0)"));
});
