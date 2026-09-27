// Tests of `PrimOpIntBit02Configurable-num.js`: `PrimOpIntBit02Configurable.lean` compiled with
// `--config=pbo`, where `Nat`, `Int`, `USize`, `UInt64`, `Int64` and `ISize` are
// JavaScript numbers.
//
// Every export is checked against what Lean answers for it, which
// `scripts/expectations/PrimOpIntBit02Configurable.json` holds and Lean itself wrote
// (`scripts/regen-primop-expectations.sh`).  The last argument is how many of those
// answers this representation cannot hold exactly; see `scripts/primop-check.mjs`.
import { checkModule } from "../scripts/primop-check.mjs";

import * as m from "./PrimOpIntBit02Configurable-num.js";

checkModule(m, "PrimOpIntBit02Configurable", "num", {
  inexact: 2,
  // `~~~(-3)` at 64 bits: `-3` is `2^64 - 3`, which a number cannot hold, so the
  // complement of it is not Lean's `2`
  divergent: ["TestUInt64_complement", "TestUSize_complement"],
});
