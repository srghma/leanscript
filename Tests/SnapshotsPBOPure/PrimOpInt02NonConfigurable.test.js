// Tests of `PrimOpInt02NonConfigurable.js`: `PrimOpInt02NonConfigurable.lean` compiled with the default
// configuration.  `UInt8/16/32` and `Int8/16/32` fit in a JavaScript number exactly, so
// no knob of `LeanScript/Config.lean` can change how this module is represented: it has one
// output rather than a `-num` and a `-bigint` one, and no `BigInt` appears in it.
//
// Every export is checked against what Lean answers for it, which
// `scripts/expectations/PrimOpInt02NonConfigurable.json` holds and Lean itself wrote
// (`scripts/regen-primop-expectations.sh`).  Nothing here is inexact: every value of
// these types is one a number holds.
import assert from "node:assert/strict";
import test from "node:test";
import { readFileSync } from "node:fs";

import { checkModule } from "../scripts/primop-check.mjs";

import * as m from "./PrimOpInt02NonConfigurable.js";

checkModule(m, "PrimOpInt02NonConfigurable", "num", { inexact: 0, divergent: [] });

test("no BigInt is used", () => {
  const src = readFileSync(new URL("./PrimOpInt02NonConfigurable.js", import.meta.url), "utf8");
  assert.equal(/\d+n\b/.test(src), false);
  assert.equal(src.includes("BigInt"), false);
});
