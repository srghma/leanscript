// Tests of `PrimOpBitVec02Configurable-bigint.js`: `PrimOpBitVec02Configurable.lean` compiled with
// `--config=faithful`, where a bit vector of at least 32 bits is a `BigInt`.
//
// Every export is checked against what Lean answers for it, which
// `scripts/expectations/PrimOpBitVec02Configurable.json` holds and Lean itself wrote
// (`scripts/regen-primop-expectations.sh`).  The last argument is how many of those
// answers this representation cannot hold exactly; see `scripts/primop-check.mjs`.
import { checkModule } from "../scripts/primop-check.mjs";

import * as m from "./PrimOpBitVec02Configurable-bigint.js";

checkModule(m, "PrimOpBitVec02Configurable", "bigint", { inexact: 0 });
