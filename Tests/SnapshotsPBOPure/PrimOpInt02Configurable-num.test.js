// Tests of `PrimOpInt02Configurable-num.js`: `PrimOpInt02Configurable.lean` compiled with
// `--config=pbo`, where `Nat`, `Int`, `USize`, `UInt64`, `Int64` and `ISize` are
// JavaScript numbers.
//
// Every export is checked against what Lean answers for it, which
// `scripts/expectations/PrimOpInt02Configurable.json` holds and Lean itself wrote
// (`scripts/regen-primop-expectations.sh`).  The last argument is how many of those
// answers this representation cannot hold exactly; see `scripts/primop-check.mjs`.
import { checkModule } from "../scripts/primop-check.mjs";

import * as m from "./PrimOpInt02Configurable-num.js";

checkModule(m, "PrimOpInt02Configurable", "num", { inexact: 10, divergent: [] });
