// Tests of `PrimOpIntDivConfigurable-bigint.js`: `PrimOpIntDivConfigurable.lean` compiled
// with `--config=faithful`, where `Nat`, `Int`, `USize`, `UInt64`, `Int64` and `ISize` are
// `BigInt`s.
//
// Every export of that module is a `Bool` that Lean evaluates to `true`: it says that
// the division the optimiser inlined and folded agrees both with the `@[noinline]`
// division and with the answer written in the Lean source.  So the whole suite is the
// one assertion that every `…_shouldBeTrue` is `true` — a disagreement between the
// generated code and Lean shows up as a `false`.
import assert from "node:assert/strict";
import test from "node:test";

import * as m from "./PrimOpIntDivConfigurable-bigint.js";

const answers = Object.entries(m).filter(([k]) => k.endsWith("_shouldBeTrue"));

test("the module exports the answers of every namespace", () => {
  assert.equal(answers.length, 17);
});

for (const [name, value] of answers) {
  test(`${name} is true`, () => {
    assert.equal(value, true);
  });
}
