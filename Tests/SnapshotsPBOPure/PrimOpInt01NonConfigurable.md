# `PrimOpInt01NonConfigurable`: ours against the reference

The file defines `add`, `sub`, `eq`, `ne`, `lt`, `gt`, `le`, `ge`, `mul`, `div`, `neg` for
`UInt8`, `UInt16`, `UInt32`, `Int8`, `Int16` and `Int32`: 66 functions.  These types have a
single JavaScript representation (a `number`), so the `pbo` and `faithful` outputs are the same.

Reference: `legacy-backend/PrimOpInt01NonConfigurable.js` (purescript-backend-optimizer).

**Before:** 18 functions were runtime calls: `div` of the three unsigned types and
`add`/`sub`/`mul`/`div`/`neg` of the three signed types (`int8__lean_int8_add(a, b)`, …).
**Now** all 66 functions are inline JavaScript and the module imports nothing from
`runtime.js`.  The reference uses a runtime function in 54 of its 66 functions (all but the unsigned
comparisons).  The node checks
against Lean pass: 1089 at `pbo` and 1089 at `faithful`.

| fn | ours | reference |
|---|---|---|
| `UInt8.add`, `sub`, `mul`, `neg` | `(a + b) & 255`, `(a - b) & 255`, `(a * b) & 255`, `-a & 255` | `$lean_uint8_add(v0, v1)`, … (call) |
| `UInt16.*` | as `UInt8`, with `65535` | calls |
| `UInt32.add`, `sub`, `mul`, `neg` | `(a + b) >>> 0`, `(a - b) >>> 0`, `Math.imul(a, b) >>> 0`, `-a >>> 0` | calls |
| `UInt8.div`, `UInt16.div` | `(a / b) \| 0` (**new**) | `$lean_uint8_div(v0, v1)` |
| `UInt32.div` | `(a / b) >>> 0` (**new**) | `$lean_uint32_div(v0, v1)` |
| `UIntN.eq`, `ne` | `a === b`, `a !== b` | `instDecidableEqUInt8`, an `if` returning `false`/`true` |
| `UIntN.lt`, `gt`, `le`, `ge` | `a < b`, `a > b`, `a <= b`, `a >= b` | `v0 < v1`, `v1 < v0`, … |
| `Int8.add`, `sub`, `mul` | `((a + b) << 24) >> 24`, … (**new**) | `$lean_int8_add(v0, v1)`, … |
| `Int8.neg` | `(-a << 24) >> 24` (**new**) | `$lean_int8_neg(v0)` |
| `Int8.div` | `((a / b) << 24) >> 24` (**new**) | `$lean_int8_div(v0, v1)` |
| `Int16.*` | as `Int8`, with `16` (**new**) | calls |
| `Int32.add`, `sub`, `neg` | `(a + b) \| 0`, `(a - b) \| 0`, `-a \| 0` (**new**) | calls |
| `Int32.mul` | `Math.imul(a, b)` (**new**) | `$lean_int32_mul(v0, v1)` |
| `Int32.div` | `(a / b) \| 0` (**new**) | `$lean_int32_div(v0, v1)` |
| `IntN.lt`, `gt`, `le`, `ge` | `a < b`, … | `$lean_int8_dec_lt(v0, v1)`, `$lean_int8_dec_lt(v1, v0)`, … |
| `IntN.eq`, `ne` | `a === b`, `a !== b` | `instDecidableEqInt8`, an `if` |

The bitwise operations of `Int8`/`Int16`/`Int32` (`~a`, `a & b`, `a | b`, `a ^ b`) are inline
now too.  They are not used in this file.

## Where the change is

The `Term` produced from Lean is already minimal for this file (each function is one extern
call), so there was nothing for the `Term` → `Term` optimiser to do.  The change is in
`Term` → `JsTerm`: new inline forms of the externs in `scripts/js_ops_inline.json`, regenerated
into `JsTerm/Ops/` by `scripts/gen_js_ops.py`.  `JsTerm` → `JsTerm` was not changed.  This file
has no recursion or loops, so labelled blocks and loops do not come up.

## Why the forms are correct

`RuntimeSpec/InlineSInt.lean` proves each form equal to the Lean operation, in the model of
JavaScript's 32-bit operators of `RuntimeSpec/Model.lean`, for all arguments (no `sorry`):
`int8_add_inline`, …, `int32_div_inline`, `uint8_div_inline`, `uint16_div_inline`,
`uint32_div_inline`.

The division forms leave out the runtime's `b === 0 ? 0 : …` test, which reads `b` twice.  That
is correct because JavaScript's `ToInt32`, which `| 0`, `<<` and `>>>` apply, maps `Infinity`,
`-Infinity` and `NaN` to `0`, which is Lean's result for division by zero.  For a nonzero
divisor, `ToInt32(a / b)` is the quotient truncated toward zero: the rounding error of `a / b`
on two safe integers is less than the distance of a non-integral quotient to the nearest
integer.  The model takes this one fact about floating-point division as given (it is stated in
the module doc).  The checks also cover division by zero and `-128 / -1`, `-2^31 / -1`.
