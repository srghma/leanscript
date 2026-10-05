# `PrimOpInt01Configurable`: ours against the references

The file defines `add`, `sub`, `eq`, `ne`, `lt`, `gt`, `le`, `ge`, `mul`, `div`, `neg` for
`UInt64`, `USize`, `Nat` (no `neg`), `Int64`, `ISize` and `Int`: 65 functions.

References: `-num.js` for our `pbo` preset (every type a JavaScript number) and `-bigint.js`
for `faithful` (every type a `BigInt`); `-num.expected.js` / `-bigint.expected.js` are the
hand-written curried forms (`(a) => (b) => …`).

**Before:** the 22 functions of `USize` and `ISize` were not translated at all ("the width of
`BitVec System.Platform.numBits` is not a numeral").  **Now** all 65 are, at both presets, and
every one is on par with the reference or better (one exception, `div`, discussed below).  The
checks against Lean: 831 (`pbo`) and 940 (`faithful`), all passing (569 and 577 before, the
`USize`/`ISize` functions had none).

## `pbo` (numbers) against `-num.js`

| fn | ours | `-num.js` |
|---|---|---|
| `USize.add`, `sub`, `mul`, `neg` | `uint53__lean_uint64_add(a, b)`, … (call) | `$lean_usize_add(v0, v1)`, … (call) |
| `USize.div` | `uint53__lean_uint64_div(a, b)` | `$lean_usize_div(v0, v1)` |
| `USize.eq`, `ne` | `a === b`, `a !== b` | `instDecidableEqUSize`, an `if` returning `false`/`true` |
| `USize.lt`, `gt`, `le`, `ge` | `a < b`, `a > b`, `a <= b`, `a >= b` | `v0 < v1`, `v1 < v0`, `v0 <= v1`, `v1 <= v0` |
| `ISize.add`, `sub`, `mul`, `div` | `int53__lean_int64_add(a, b)`, … (call) | `$lean_isize_add(v0, v1)`, … (call) |
| `ISize.neg` | `0 - a` | `$lean_isize_neg(v0)` |
| `ISize.lt`, `gt`, `le`, `ge` | `a < b`, `a > b`, `a <= b`, `a >= b` | `$lean_isize_dec_lt(v0, v1)`, `$lean_isize_dec_lt(v1, v0)`, … |
| `ISize.eq`, `ne` | `a === b`, `a !== b` | `instDecidableEqISize`, an `if` |
| `Int64.*` | as `ISize` | as `ISize` (`$lean_int64_…`) |
| `Int64.neg` | `0 - a` (was `int53__lean_int64_neg(a)`) | `$lean_int64_neg(v0)` |
| `Int.neg` | `0 - a` (was `int53__lean_int_neg(a)`) | `$lean_int_neg(v0)` |
| `Nat.sub` | `Math.max(0, a - b)` (was `uint53__lean_nat_sub(a, b)`) | `Math.max(0, v0 - v1)` |
| `Nat.add`, `mul`, `Int.add`, `sub`, `mul` | `uint53__lean_nat_add(a, b)`, … | `v0 + v1`, … |
| `Nat.div` | `uint53__lean_nat_div(a, b)` | `v1 !== 0 ? Math.trunc(v0 / v1) : 0` |
| `Int.div` | `int53__lean_int_ediv(a, b)` | `$lean_int_ediv(v0, v1)` |
| `UInt64.*` | as `USize` | as `USize` (`$lean_uint64_…`) |

* `Nat.add`, `Nat.mul`, `Int.add`/`sub`/`mul` stay calls on purpose: at `pbo` a number must be
  a safe integer, and the runtime throws ("integer overflow … use the bigint representation")
  where `v0 + v1` would silently round above `2^53`.  The reference computes a wrong answer
  there; ours computes Lean's or throws.
* `Nat.div` (and `UInt64.div`) is a call where the reference writes the test inline: the
  divisor is read twice by the test (`b === 0 ? 0 : …`), and an inline operation reads each
  operand once (`JsInline`); see "Not done".

## `faithful` (`BigInt`) against `-bigint.js`

| fn | ours | `-bigint.js` |
|---|---|---|
| `USize.add`, `sub`, `mul`, `neg` | `BigInt.asUintN(64, a + b)`, … (inline) | `$lean_usize_add(v0, v1)`, … (call) |
| `ISize.add`, `sub`, `mul`, `neg` | `BigInt.asIntN(64, a + b)`, … (inline) | `$lean_isize_add(v0, v1)`, … (call) |
| `Int64.add`, `sub`, `mul`, `neg` | `BigInt.asIntN(64, a + b)`, … (inline; was a call) | `$lean_int64_add(v0, v1)`, … (call) |
| comparisons of all six | `a === b`, `a !== b`, `a < b`, `a > b`, … | calls of the runtime for `USize`, `ISize`, `Int64`; `if`s for `ne`; swapped operands for `gt`, `ge` |
| `Nat.sub`, `Nat.div`, `Int.div`, `UInt64.div`, … | calls (`bigint_nat__lean_nat_sub`, …) | calls (`$lean_nat_sub`, …) |
| `Int.neg` | `-a` | `$lean_int_neg(v0)` |

Every function is a function of two parameters (`(a, b) =>`) where the curried references
make two calls (`(a) => (b) =>`).

## How

In the order of preference of the phases:

1. **Lean → `Term`** (the elaborator; nothing could be translated otherwise).  `USize` is a
   structure around a `BitVec System.Platform.numBits`, and `numBits` is `32` or `64` depending
   on the platform: no definition of an operation of `USize` or `ISize` can be unfolded to
   something the language has.  The translation now **assumes a 64-bit platform**, as the
   compiled Lean the checks compare against does, and as both references do:
   * `USize` is the leaf `uint64`, `ISize` the leaf `int64` (`classify`,
     `LeanScript/GenElab/Read.lean`); the conversions `USize.toUInt64`, `UInt64.toUSize`,
     `ISize.toInt64`, `Int64.toISize` are the identity (`platformIntConv`).
   * Every operation is read as the 64-bit one between those conversions
     (`platformIntOpCall?`, `platformIntDecide?`, `LeanScript/TermElab/ToTerm/Expr/Calls.lean`):
     `USize.add a b` is `(a.toUInt64 + b.toUInt64).toUSize`, `USize.decLt a b` is
     `decide (a.toUInt64 < b.toUInt64)`.  Covered: `add`, `sub`, `mul`, `div`, `mod`, `neg`,
     `land`, `lor`, `xor`, `complement`, `=`, `<`, `≤`, `ofNat`, `toNat`, `ISize.ofInt`,
     `ISize.toInt`, `ISize.ofNat`, and the conversions from and to `UInt8`/`UInt16`/`UInt32`.
   * **Each reading is proved equal to the original on every platform**, without the
     assumption, in `LeanScript/TermElab/ToTerm/PlatformIntOps.lean` (`usize_add`, …,
     `isize_div`, `isize_mod`, `usize_complement`, `usize_lt`, `isize_eq`, …).  Only the
     identity of the conversions needs `numBits = 64`.
   * A closed value of `USize`/`ISize` (a literal `3 : USize`) is not computed at compile time
     (`numBits` does not reduce) but translated down to the `UInt64`/`Int64` literal it is
     (`LeanScript/TermElab/ToTerm/Expr.lean`).
2. **`Term` → `Term`**: nothing new was needed: the optimised `Term`s of `USize` are those of
   `UInt64` (`lean_uint64_add(x2, x4)`, `cond(lean_uint64_dec_eq(x2, x4), false, true)`), and
   the existing rules already give `!==` for `ne` and `>` for `gt`.
3. **`Term` → `JsTerm`** (the operations, `scripts/js_ops_inline.json`, regenerated by
   `scripts/gen_js_ops.py`): written inline instead of calls of the runtime, each operand read
   once and in order:
   * `Int64` at `BigInt`: `add`, `sub`, `mul`, `neg`, `complement`, `land`, `lor`, `xor`, the
     bodies of the runtime's functions (`BigInt.asIntN(64, a + b)`);
   * `Int.neg` and `Int64.neg` at `number`: `0 - a` (the runtime's body; `-a` would give `-0`);
   * `Nat.sub` at `number`: `Math.max(0, a - b)` instead of the runtime's `a > b ? a - b : 0`
     (which reads both operands twice).
   Each form is proved to compute the Lean operation in the model of `runtime.js`
   (`RuntimeSpec/InlineInt.lean`: `int64_add_inline`, …, `int64_neg_inline_num`,
   `nat_sub_inline`).
4. **`JsTerm` → `JsTerm`**: nothing was needed.

There are no loops or recursion in this file, so labelled blocks and loops do not come into
it; `Tests/SnapshotsMy/PlatformInts.lean` has two loops over `USize`/`ISize` accumulators, which
are `while (true)` loops with `return`.

## Tests

* `PrimOpInt01Configurable`: 831 (`pbo`) and 940 (`faithful`) checks against Lean, all passing.
  The check generator has samples of `USize` and `ISize` now (`SType.usize`, `SType.isize`,
  `LeanScriptCli/Check.lean`), including `2^64 - 1`, `-2^63` and `2^63 - 1` at `BigInt`
  (`TestUSize$add(18446744073709551615n, 2n)` is `1`, `TestISize$div(-9223372036854775808n, -1n)`
  is `-9223372036854775808`).
* New `Tests/SnapshotsMy/PlatformInts.lean`: literals, `toNat`, `ofNat`, `Nat.toUSize`, bitwise
  operations, `%`, conversions from and to `UInt64`/`Int64`/`UInt32`/`UInt8`/`Int`,
  comparisons in conditions, two loops: 187 and 241 checks, all passing.
* `primOpInt01Spec` in `Tests/Main.lean` checks the lines above and runs the checks.
* Every snapshot was regenerated; the other outputs that changed are `Nat.sub` (now
  `Math.max(0, a - b)`), `Int.neg` (`0 - a`) and `Int64` arithmetic at `BigInt` (inline), and
  `USize`/`ISize` functions of `PrimOpInt02`/`PrimOpInt03`/`PrimOpIntBit01`/`PrimOpIntBit02`/
  `PrimOpIntDiv` that are now translated.  No check fails.

## Not done

* **Division inline** (`b === 0 ? 0 : Math.floor(a / b)`): an inline operation
  (`JsInline`) reads each argument once, in order, which the test of the divisor breaks.  It
  would need a way to inline an operation only when its arguments are variables or literals.
* **Shifts of `USize`/`ISize`**, `USize.size`, `ISize.toInt8`/`16`/`32`: not in the table yet
  (the shift of `USize` takes its count modulo `numBits`, which only the platform assumption
  could turn into `64`).  Listed in `NOT_IMPLEMENTED.md`.
