# Integer → `Float32` conversions: `Number(x)` was a no-op and a bug

## The question

```lean
| .int53__lean_int64_to_float32 => .call "Number" [.arg 0]
```

Why is this not the identity, when an `int53` is already a JavaScript number?

## Answer

`Number(x)` on a number *is* the identity, so this template did nothing. But the identity is
also **wrong** here. A `float32` value (`JsTerminalTy.float32`) is "a `number` rounded by
`Math.fround`". `Int64.toFloat32` rounds to single precision, but a 64-bit (or 32-bit) integer
is usually not a single-precision value:

```lean
#eval (16777217 : Int64).toFloat32 == 16777216   -- true: 2^24 + 1 rounds to 2^24
```

The old JavaScript returned `16777217`, which is not a `float32` at all, so any later
comparison or `toString` disagreed with Lean. The right template is `Math.fround(x)`. An
`int53` is exact in a double, so `Math.fround` rounds it once, just as the C cast
`(float)(int64_t)x` does.

`Number(...)` got there through the generator. `conv_value` in `scripts/gen_js_ops.py` treated
`float` and `float32` targets the same: `Number(x)` for a `BigInt` source and the identity
otherwise. That rule is right for `float` and wrong for `float32`.

## Every inlined conversion, checked

I checked every template in `JsTerm/Ops/Template.lean` that is the identity or a call of
`Number` / `BigInt` / `Math.fround`, against the representations in its signature:

| operation | old | new | why |
| :-- | :-- | :-- | :-- |
| `int53__lean_int64_to_float32` | `Number(x)` (no-op) | `Math.fround(x)` | needs rounding to single |
| `uint53__lean_uint64_to_float32` | `Number(x)` (no-op) | `Math.fround(x)` | needs rounding to single |
| `int32__lean_int32_to_float32` | `x` | `Math.fround(x)` | 32 bits > 24-bit significand |
| `uint32__lean_uint32_to_float32` | `x` | `Math.fround(x)` | 32 bits > 24-bit significand |
| `bigint_int__lean_int64_to_float32` | `Number(x)` | runtime `$bigToF32` | `Number` gives a double, not a float; `Math.fround(Number(x))` would round twice |
| `bigint_nat__lean_uint64_to_float32` | `Number(x)` | runtime `$bigToF32` | the same |

The rest are correct, and none of them is a no-op:
* `{u,}int{8,16}_to_float32` stay the identity, because every such integer is a `float32`.
* `*_to_float` (double) from an integer `number` is the identity. From a `BigInt`, `Number(x)`
  is needed: by the ECMAScript spec it rounds once to nearest, ties to even.
* Every remaining `Number(...)` / `BigInt(...)` converts between the two JavaScript types
  (`number` ↔ `BigInt`), so none is redundant.
* `Math.fround` is left off `ceilf` / `floorf` / `fabsf` / negation on purpose: those results
  are already `float32`s.

### Why a `BigInt` cannot just use `Math.fround(Number(x))`

Take `x = 2^63 + 2^39 + 1`. The two nearest floats are `2^63` and `2^63 + 2^40`, and `x` is
just above their midpoint, so the correctly rounded result is `2^63 + 2^40`. The double
nearest `x`, however, is the midpoint itself, and `Math.fround` then rounds that tie to even:
down to `2^63`. So `$bigToF32` (in `runtime.js`) first cuts `|x|` to its 30 leading bits and
sets the lowest kept bit when any dropped bit is set (a "sticky" bit). The result is exact in
a double and lies on the same side of every float midpoint as `x`, so one `Math.fround` gives
the correctly rounded result.

## Checks

* **Ad-hoc comparison with Lean.** I compared about 19,800 values (random values, powers of
  two ± 3, and values at and next to float midpoints at every magnitude) against Lean's
  `UInt64.toFloat32` / `Int64.toFloat32`. This was a one-off script run during this change; it
  is not part of the test suite.
  - New code: 0 mismatches, for both the `BigInt` function and `Math.fround` on the
    safe-integer ones.
  - Old `Number(x)`: 18,670 mismatches.
  - `Math.fround(Number(x))` (double rounding): 1,201 mismatches.
* **Runtime test.** `Tests/Main.lean`, "runtime.js computes what Lean computes", now has seven
  cases for the two `BigInt` functions, including the double-rounding example.
* **Snapshot test.** `Tests/SnapshotsMy/IntToFloat32.lean` has 20 checks per preset. With the
  old templates, 8 of the 20 `pbo` checks fail.

## `runtime.js`

I scanned every exported function for a conversion to the type its argument already has
(`Number(x)` of a `number`, `BigInt(x)` of a `BigInt`). There are none. The `float32` results
of `runtime.js` (`add` / `sub` / `mul` / `div`, `Float.toFloat32`, `scaleb`, `ofBits`) are all
rounded, and `roundf` of a `float32` is already a `float32`.

Some `uint53` / `int53` functions go through `BigInt` (`mul`, `shift_left`, `land` / `lor` /
`xor`, `mix_hash`). That detour is needed: 64-bit wrap-around and bit operations above 32 bits
cannot be done on doubles. A fast path for small operands would only be an optimisation. Two
functions are worth noting, though; I did not change them, since `RuntimeSpec` models and
proves them as written:
* `uint53__lean_uint64_neg(a)`, for `a ≠ 0`, is `2^64 - a > 2^53`, which always overflows. It
  is therefore `a === 0 ? 0 : $overflow()`, and the `BigInt` arithmetic is never needed.
* `uint53__lean_uint64_complement(a)` is `2^64 - 1 - a ≥ 2^64 - 2^53`, so it always throws.
