// Tests of `PrimOpBitVec02Configurable-num.js`: `PrimOpBitVec02Configurable.lean` compiled with
// `--config=pbo`, where a bit vector of at least 32 bits is a JavaScript number.
//
// Every export is checked against what Lean answers for it, which
// `scripts/expectations/PrimOpBitVec02Configurable.json` holds and Lean itself wrote
// (`scripts/regen-primop-expectations.sh`).  The last argument is how many of those
// answers this representation cannot hold exactly; see `scripts/primop-check.mjs`.
import { checkModule } from "../scripts/primop-check.mjs";

import * as m from "./PrimOpBitVec02Configurable-num.js";

checkModule(m, "PrimOpBitVec02Configurable", "num", { inexact: 3, divergent: [] });
