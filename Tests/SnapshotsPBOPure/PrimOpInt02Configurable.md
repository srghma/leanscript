# `PrimOpInt02Configurable`: ours against the references

The file defines, for each of `UInt64`, `USize`, `Nat`, `Int64`, `ISize` and `Int`, an
`@[inline] intValues op` (six calls of `op` on fixed arguments) and `test1` … `test11`, each
`intValues` of one operation (`+`, `-`, `==`, `!=`, `<`, `>`, `<=`, `>=`, `*`, `/`), plus
`test11 = #[-1, -(-1)]`.  71 definitions (`Nat` has no `test11`).

References: `-num.js` (purescript-backend-optimizer, every type a JavaScript number) for our
`pbo` preset, `-bigint.js` (every type a `BigInt`) for `faithful`; `-num.expected.js` /
`-bigint.expected.js` are hand-written ideal outputs (every test a literal).

## Summary

| | `-num.js` / `-bigint.js` | `-*.expected.js` | ours, `faithful` | ours, `pbo` |
|---|---|---|---|---|
| `test1` … `test11` | runtime calls (`$lean_uint64_add(…)`, `instDecidableEq…`, `$lean_int64_dec_lt`), a local closure `v0` per test, nested spreads `[...[...[], x], y]` | an array literal | an array literal (a typed array for `UInt64`/`Int64`/`USize`/`ISize`), equal arrays shared | an array literal, equal arrays shared, **except 10 `UInt64`/`USize` tests** (below) |
| `intValues` | `(op) => [op(1)(1), …]` (curried) | same | `(op) => [op(1n, 1n), …]` (one call of two arguments) | same, **except `UInt64`/`USize`** |
| imports | 6 runtime modules | none | none | none |
| values | `UInt64`/`USize` values above `2^53` cannot be exact numbers (`-num.test.js` allows 10 inexact answers) | `UInt64`/`USize` `test5`–`test8` of `-num.expected` are the *signed* answers (`1 < -2` is false), not Lean's | all exactly Lean's | all exactly Lean's |

So `faithful` is better than `-bigint.js` in every definition and equal to `-bigint.expected.js`
(plus typed arrays and shared arrays), and `pbo` is better than `-num.js` in every definition it
translates.  `pbo` translates 59 of the 71.

## The `UInt64` / `USize` definitions at `pbo`

`TestUInt64.intValues`, `test1`, `test2`, `test9`, `test10`, `test11`, and the same six of
`TestUSize` are refused at `pbo` ("literal too big …", and `leanscript` exits with a failure).
Each holds a `UInt64` value above `2^53 - 1` that no JavaScript number can hold exactly:

* `test1 = #[2, 3, 3, 18446744073709551615, 1, 18446744073709551614]` (Lean's `1 + (-2)` is
  `2^64 - 1`), and similarly `test2`, `test9`, `test11`;
* `test10 = #[…, 9223372036854775807, …]` (`(-1) / 2`);
* `intValues` passes `op` the literals `-2 = 18446744073709551614` and `-1`.

`-num.js` computes them at run time as numbers (`$lean_uint64_neg(1)`, …), and
`-num.expected.js` lists `-1` and `-2` there: not `UInt64` values, and not what Lean computes.  At `pbo` a 64-bit number must be a safe integer, the runtime throws ("integer
overflow … use the bigint representation") rather than round, and a literal that cannot be one
is refused at compile time rather than emitted as a module-level constant that would throw on
`import`.  The six comparison tests (`test3` … `test8`), whose answers are booleans, are
computed at compile time and translated (with Lean's answers, which `-num.expected.js` gets
wrong for `test5` … `test8`).

## Where the work happens

Everything is folded by the `Term → Term` optimiser: `intValues` is inlined into each test,
`op` is beta-reduced, and the primitive operations on literals are computed
(`Tests/SnapshotsPBOPure/PrimOpInt02Configurable-Term-optimized.txt`).  `Term → JsTerm` writes
the literals at the representation of the preset (typed arrays at `faithful`), and shares equal
top-level arrays (`TestUSize$test1 = TestUInt64$test1`).  There are no loops or recursion in
this file, so labelled blocks and loops do not come into it.  No change to the translation was
needed for this file.

## What changed: the checks

Before, the checks of this file (`*-pbo.check.mjs`, `*-faithful.check.mjs`) covered 49 values
per preset: none of the arrays of `UInt64`/`Int64`/`USize`/`ISize`, and none of the `intValues`
of a fixed-width type, because the check generator (`LeanScriptCli/Check.lean`) had no samples
of those types.  It now also handles:

* an `Array` of fixed-width integers (`UInt8` … `UInt64`, `Int8` … `Int64`, `USize`, `ISize`)
  as a result or a parameter, spelled as the typed array the configuration makes it
  (`BigUint64Array.of(1n, 2n)`, `Uint8Array.of(…)`) or a plain array; at `pbo` an answer with an
  element outside `±(2^53 - 1)` is skipped, as for a single 64-bit answer;
* a function parameter of two fixed-width arguments (`UInt64 → UInt64 → Nat`): the samples read
  the arguments as integers (`x * 10 + y`, `y * 3 - x`).

Now every translated definition is checked (each `intValues` by two calls): 63 checks at
`pbo` (59 definitions) and 77 at `faithful` (71), all passing.  Other
snapshots gained checks too, all passing, with no change to any `.js` file:
`PrimOpInt02NonConfigurable` (+42 per preset), `ArrayGetDefault` (+80), `ArrayStdFunctions` (+8),
`ArrayFSet` (+6), `ShareConstValues` (+1).

`Tests/Main.lean` has a new `primOpInt02Spec`: it checks which definitions are refused at `pbo`,
fragments of both outputs, that neither imports anything nor calls the runtime, and runs the
node checks (63 and 77).
