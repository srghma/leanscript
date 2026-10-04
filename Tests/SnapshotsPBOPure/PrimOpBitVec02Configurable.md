# `PrimOpBitVec02Configurable`: ours against purescript-backend-optimizer

Before this change the four shifts (`shiftLeft`, `shiftRight` at `BitVec 32` and `BitVec 64`)
were not translated ("`BitVec 32` is a leaf of the language").  Now all 12 functions are, and
every one is on par with the reference (`-num.js` for our `pbo` preset, `-bigint.js` for
`faithful`) or better.

## `BitVec 32` (a JavaScript number at both presets)

| fn | ours (`pbo` = `faithful`) | reference |
|---|---|---|
| `land` | `(a, b) => (a & b) >>> 0` | `(v0, v1) => BitVec_and(32, v0, v1)` |
| `lor` | `(a, b) => (a \| b) >>> 0` | `BitVec_or(32, v0, v1)` |
| `xor` | `(a, b) => (a ^ b) >>> 0` | `BitVec_xor(32, v0, v1)` |
| `complement` | `(a) => ~a >>> 0` | `BitVec_not(32, v0)` |
| `shiftLeft` | `(a, b) => (b < 32 ? (a << b) >>> 0 : 0)` | `BitVec_shiftLeft(32, v0, BitVec_toNat(32, v1))` |
| `shiftRight` | `(a, b) => (b < 32 ? a >>> b : 0)` | `BitVec_ushiftRight(32, v0, BitVec_toNat(32, v1))` |

## `BitVec 64`

| fn | ours, `pbo` (number) | ours, `faithful` (`BigInt`) | reference |
|---|---|---|---|
| `land` | `uint53__lean_uint64_land(a, b)` | `a & b` | `BitVec_and(64n, v0, v1)` |
| `lor` | `uint53__lean_uint64_lor(a, b)` | `a \| b` | `BitVec_or(64n, v0, v1)` |
| `xor` | `uint53__lean_uint64_xor(a, b)` | `a ^ b` | `BitVec_xor(64n, v0, v1)` |
| `complement` | `uint53__lean_uint64_complement(a)` | `BigInt.asUintN(64, ~a)` | `BitVec_not(64n, v0)` |
| `shiftLeft` | `b < 64 ? uint53__lean_uint64_shift_left(a, b) : 0` | `b < 64n ? BigInt.asUintN(64, a << b) : 0n` | `BitVec_shiftLeft(64n, v0, BitVec_toNat(64n, v1))` |
| `shiftRight` | `Math.floor(a / 2 ** b)` | `a >> b` | `BitVec_ushiftRight(64n, v0, BitVec_toNat(64n, v1))` |

* **No width argument and no `toNat` call**: the reference makes two runtime calls per shift.
  Ours makes none, except the `number` representation of `BitVec 64`, which must throw when a
  result is not a safe integer.
* **`shiftRight` at `BitVec 64` needs no test.** A right shift of a value below `2 ^ 64` by 64
  or more is already `0` in JavaScript: `a >> b` on a `BigInt`, and `Math.floor(a / 2 ** b)` on
  a number (`2 ** b` is `Infinity` from `b = 1024` on, and `a / Infinity` is `0`).
* **`BitVec 32` shifts have no mask.** JavaScript's `<<` and `>>>` take the count modulo 32,
  which is Lean's `UInt32` count, so the test `b < 32` is all that's left of `BitVec`'s "0 from
  the width on".
* **What remains a runtime call at `pbo`:** the 64-bit bitwise operations on numbers. The
  reference calls its runtime too. `$land53` and the others split the number into two 32-bit
  halves, so they are not a single operator.

## How

1. **Lean → Term (elaborator, `bitvecShiftCall?` in
   `LeanScript/TermElab/ToTerm/Expr/Calls.lean`).** `x <<< y` on `BitVec w` (the count
   `y.toNat`), at the widths 8/16/32/64, is read as
   `if UIntW.ofBitVec y < w then (UIntW.ofBitVec x <<< UIntW.ofBitVec y).toBitVec else 0`.
   A literal count `k` gives the shift alone when `k < w`, and `0` otherwise. Any other
   natural count `n` gives `if n < w then … UIntW.ofNat n … else 0`. A computed count is bound
   once (`const x$1 = (32 - k) >>> 0;`). `x.toNat` is read as `(UIntW.ofBitVec x).toNat`. Every
   reading is proved equal to Lean's definition in
   `LeanScript/TermElab/ToTerm/BitVecOps.lean` (`bitvec32_shiftLeft`, `bitvec64_shiftRight_nat`,
   `bitvec32_shiftLeft_lit`, `bitvec32_shiftLeft_big`, `bitvec32_toNat`, …).
2. **Term → JsTerm (conversion).**
   * New inline templates: `UInt32.shiftLeft` is `(a << b) >>> 0`. At `BigInt`, `UInt64.shiftLeft`
     is `BigInt.asUintN(64, a << (b & 63n))`, `UInt64.shiftRight` is `a >> (b & 63n)` and
     `UInt64.ofNat` is `BigInt.asUintN(64, a)`. At `number`, `UInt64.shiftRight` is
     `Math.floor(a / 2 ** (b % 64))` and `Nat.shiftRight` is `Math.floor(a / 2 ** b)`. They are
     proved against the JavaScript model in `RuntimeSpec/InlineShift.lean`.
   * `JsTerm/Lower/Shift.lean`: under the test `b < 64` the mask of the count is dropped, and a
     right shift drops the test too. A literal count below 64 also drops the mask. Both are
     proved in `RuntimeSpec/InlineShift.lean` (`uint64_shift_right_guarded`,
     `uint64_shift_left_guarded`, `uint64_shift_right_lit`, `uint64_shift_left_lit`).

   The mask can't be dropped in `Term`: Lean's shift of `UInt64`, the only shift the language
   has, takes its count modulo 64.

The `JsTerm` optimiser wasn't changed. There are no loops or recursion in this file, so labelled
blocks and loops don't come into it.

## Checks

The check generator now also samples the counts `w - 1`, `w` and `w + 36` for a `BitVec w`, and
tries every pair of bit vectors (up to 96 cases) instead of 24 spread over the space. Before
this, no check shifted by the width or more. When the function shifts, a value of `2 ^ 20` or
more is only passed as the first argument: Lean computes `x <<< y` as
`(x.toNat <<< y.toNat) % 2 ^ w`, and a count of `2 ^ 64 - 1` aborts the generator ("Nat.shiftl
exponent is too big").

| file | `pbo` | `faithful` |
|---|---|---|
| `PrimOpBitVec02Configurable` | 712 passed, 0 failed | 792 passed, 0 failed |
| `Tests/SnapshotsMy/BitVecShift` (shifts at 8/16/32/64, by literals, by `Nat`, by another width, a rotate) | 946 passed, 0 failed | 981 passed, 0 failed |
