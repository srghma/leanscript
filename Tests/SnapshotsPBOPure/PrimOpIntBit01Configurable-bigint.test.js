// Tests of `PrimOpIntBit01Configurable-bigint.js`: `PrimOpIntBit01Configurable.lean` compiled with
// `--config=faithful`, where `Nat`, `Int`, `USize`, `UInt64`, `Int64` and `ISize` are
// `BigInt`s.
//
// Every export is checked against what Lean answers for it, which
// `scripts/expectations/PrimOpIntBit01Configurable.json` holds and Lean itself wrote
// (`scripts/regen-primop-expectations.sh`).  The last argument is how many of those
// answers this representation cannot hold exactly; see `scripts/primop-check.mjs`.
import { checkModule } from "../scripts/primop-check.mjs";

import * as m from "./PrimOpIntBit01Configurable-bigint.js";

checkModule(m, "PrimOpIntBit01Configurable", "bigint", { inexact: 0 });
