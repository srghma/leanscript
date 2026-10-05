# `PrimOpInt02NonConfigurable`: ours against the reference

The file defines, for each of `UInt8`, `UInt16`, `UInt32`, `Int8`, `Int16` and `Int32`, an
`@[inline] intValues op` (six calls of `op` on fixed arguments, two of them `-1`/`-2`) and
`test1` … `test10`, each `intValues` of one operation (`+`, `-`, `==`, `!=`, `<`, `>`, `<=`,
`>=`, `*`, `/`), plus `test11 = #[-1, -(-1)]`.  72 definitions.  These types fit in a JavaScript
number exactly, so the two presets (`pbo`, `faithful`) differ only in the layout of arrays.

Reference: `legacy-backend/PrimOpInt02NonConfigurable.js` (purescript-backend-optimizer).

## Summary

| | reference | ours, `pbo` | ours, `faithful` |
|---|---|---|---|
| `test1` … `test11` | computed when the module loads: a local closure `v0` per test, 6 calls of it, runtime calls (`$lean_uint8_neg(1)`, `$lean_int8_div(…)`, `$lean_uint8_shift_left(v0, 1)`), nested spreads `[...[...[...[], a], b], c]` | an array literal | an array literal (`Uint8Array.of(…)`, `Int16Array.of(…)` … for the integer arrays) |
| equal results | recomputed | shared: `TestInt16$test1 = TestInt8$test1`, `TestUInt32$test3 = TestUInt8$test3`, … | same |
| `intValues` | `(v0) => { const v1 = $lean_uint8_neg(1); return [...[...[], v0(1, 1)], …]; }` | `(op) => [op(1, 1), op(1, 2), op(2, 1), op(1, 254), op(255, 2), op(255, 255)]`: the literals already negated | same |
| imports | 51 runtime functions | none | none |
| size | 24 049 bytes, 1100 lines | 9 017 bytes (114 lines without the doc comments) | 9 616 bytes (135 lines) |
| checks against Lean | — | 78 passed | 78 passed |

So both presets are better than the reference in every definition: there is no work left at
run time, nothing is imported, and every value is Lean's (checked by
`PrimOpInt02NonConfigurable-pbo.check.mjs` and `-faithful.check.mjs`, which compare every
definition, and each `intValues` on sample operations, with what compiled Lean answers).

## Where the work happens

The elaboration to `Term` already produces the literals for the tests (see
`PrimOpInt02NonConfigurable-Term-unoptimized.txt`): `intValues` is `@[inline]`, so every `op` is
applied to literals, and each operation on literals is computed.  The `Term` optimiser has
nothing left to do on this file; `Term → JsTerm` writes the literals (as typed arrays at
`faithful`) and shares equal top-level arrays.  There are no loops or recursion here, so labelled
blocks and loops do not come into it.  No change to the translation was needed for this file,
and its output did not change.

## Beyond this file: an unknown operand

Because the file folds to constants, `Tests/SnapshotsMy/IntOpsUnknown.lean` applies the same
`intValues` to operations reading an unknown `c` (`fun a b => a + b + c`, `a * c < b`,
`c - (a - b)`, …), so that they cannot be folded.  That showed residues, now removed:

| before | now | where |
|---|---|---|
| `(c - 0) & 255`, `(c / 1) >>> 0`, `-(-c \| 0) \| 0` | `c` | `Term → Term`: `Neu.intUnit` (`LeanScript/Term/Optimize/IntUnit.lean`) |
| `((c * 255) & 255) < 2` (`UInt8`), `((c * -1) << 24) >> 24` (`Int8`), `(0 - c) \| 0` | `-c & 255`, `-c \| 0` (then shared by a `const`) | `Term → Term`: `x * -1` and `0 - x` are `-x` (and `-x` counts as `x * -1` in the sums of `Term.arithWalk`, so the copies of `x` in a sum are still counted together) |
| `(c - 255) & 255` | `(c + 1) & 255` | `Term → Term`: `x - k` is `x + (-k)`, folded with the literals around it |
| `((c + -1) << 24) >> 24`, `(c + 255) & 255`, `(a + 144) & 255` | `((c - 1) << 24) >> 24`, `(c - 1) & 255`, `(a - 112) & 255` | `Term → JsTerm`: an addition of a negative literal is written as a subtraction (`Neu.addLitAsSub`, `LeanScript/Term/Optimize/AddLitAsSub.lean`); not in the optimiser, which would turn it back into an addition |

Each rewrite is proved not to change the value (`Neu.intUnit_eval`, `Neu.addLitAsSub_eval`;
`Neu.normArithPrim_eval` still holds with `Neu.intUnit` in it).  The rules cover `UInt8`–`UInt64`,
`Int8`–`Int64` and `Int` (and `x - 0`, `x / 1` for `Nat`).  Other snapshots improved as a result:
`PrimOpInt03NonConfigurable`/`PrimOpInt03Configurable` (`(a + 144) & 255` is now
`(a - 112) & 255`, `((a + -56) << 24) >> 24` is `((a - 56) << 24) >> 24`, `BigInt.asIntN(64, a +
-8446744073709551616n)` is `BigInt.asIntN(64, a - 8446744073709551616n)`).

Left as they are:

* `c + c * -1` at `Int8` gives `((c * 0) << 24) >> 24`: the product by the literal `0` is not
  replaced by `0` (that would change the level of the expression in the optimiser).
* `(((1 / c) << 24) >> 24) - 1` keeps its inner truncation: `1 / c` is a fractional number in
  JavaScript, so the truncation is needed.
* `Int` subtraction of two unknowns, `(c - 1) - (d - 2)`, is not regrouped (the sums of
  `Term.arithWalk` only regroup additions).
