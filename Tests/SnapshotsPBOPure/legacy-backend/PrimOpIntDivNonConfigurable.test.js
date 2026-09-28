// Tests of `PrimOpIntDivNonConfigurable.js`.  `UInt8/16/32` and `Int8/16/32` are
// representable exactly as JavaScript numbers whatever the configuration says, so this
// module has one output rather than two, and no `BigInt` appears in it.
//
// Every export is a `Bool` that Lean evaluates to `true`: the division the optimiser
// inlined and folded agrees both with the `@[noinline]` division and with the answer
// written in the Lean source.
import assert from "node:assert/strict";
import test from "node:test";
import { readFileSync } from "node:fs";

import * as m from "./PrimOpIntDivNonConfigurable.js";

const answers = Object.entries(m).filter(([k]) => k.endsWith("_shouldBeTrue"));

test("the module exports the answers of every namespace", () => {
  assert.equal(answers.length, 18);
});

for (const [name, value] of answers) {
  test(`${name} is true`, () => {
    assert.equal(value, true);
  });
}

test("no BigInt is used", () => {
  const src = readFileSync(new URL("./PrimOpIntDivNonConfigurable.js", import.meta.url), "utf8");
  assert.equal(/\d+n\b/.test(src), false);
  assert.equal(src.includes("BigInt"), false);
});
