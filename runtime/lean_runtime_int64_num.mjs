// The runtime functions that answer with an `Int64`, where an `Int64` is a JavaScript
// number (`int64Repr = num`).
//
// An `Int64` is 64 bits wide and a number holds only 53 of them exactly, so every answer
// here is exact modulo `2^64`, read back as a signed 64-bit value, and then rounded to
// a number.  `lean_runtime_int64_bigint.mjs` is the same catalogue over `BigInt`s, where
// nothing is cut.

/** `x` taken modulo `2^64`, read as a signed 64-bit value, and then back to a number. */
const wrapS64 = (x) => Number(BigInt.asIntN(64, BigInt(x)));

/** The shift distance Lean uses at 64 bits: the argument taken modulo 64. */
const shift64 = (b) => ((BigInt(b) % 64n) + 64n) % 64n;

/** `Int64.ofNat`. */
export const $lean_int64_of_nat = (n) => wrapS64(n);

/** `Int64.div`: truncates towards zero, wraps, and `a / 0` is `0`. */
export const $lean_int64_div = (a, b) =>
  Number(b) === 0 ? 0 : wrapS64(BigInt(a) / BigInt(b));

/** `Int64.neg`. */
export const $lean_int64_neg = (a) => wrapS64(-BigInt(a));

/** `Int64.add`. */
export const $lean_int64_add = (a, b) => wrapS64(BigInt(a) + BigInt(b));
/** `Int64.sub`. */
export const $lean_int64_sub = (a, b) => wrapS64(BigInt(a) - BigInt(b));
/** `Int64.mul`. */
export const $lean_int64_mul = (a, b) => wrapS64(BigInt(a) * BigInt(b));

/** `Int64.land`, on the two's complement. */
export const $lean_int64_land = (a, b) => wrapS64(BigInt(a) & BigInt(b));
/** `Int64.lor`. */
export const $lean_int64_lor = (a, b) => wrapS64(BigInt(a) | BigInt(b));
/** `Int64.xor`. */
export const $lean_int64_xor = (a, b) => wrapS64(BigInt(a) ^ BigInt(b));
/** `Int64.complement`. */
export const $lean_int64_complement = (a) => wrapS64(~BigInt(a));
/** `Int64.shiftLeft`. */
export const $lean_int64_shift_left = (a, b) => wrapS64(BigInt(a) << shift64(b));
/** `Int64.shiftRight`, which is arithmetic: the sign bit is carried in. */
export const $lean_int64_shift_right = (a, b) => wrapS64(BigInt(a) >> shift64(b));
