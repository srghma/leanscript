// The runtime functions that answer with an `ISize`, where an `ISize` is a JavaScript
// number (`isizeRepr = num`).
//
// An `ISize` is 64 bits wide and a number holds only 53 of them exactly, so every answer
// here is exact modulo `2^64`, read back as a signed 64-bit value, and then rounded to
// a number.  `lean_runtime_isize_bigint.mjs` is the same catalogue over `BigInt`s, where
// nothing is cut.

/** `x` taken modulo `2^64`, read as a signed 64-bit value, and then back to a number. */
const wrapS64 = (x) => Number(BigInt.asIntN(64, BigInt(x)));

/** The shift distance Lean uses at 64 bits: the argument taken modulo 64. */
const shift64 = (b) => ((BigInt(b) % 64n) + 64n) % 64n;

/** `ISize.ofNat`. */
export const $lean_isize_of_nat = (n) => wrapS64(n);

/** `ISize.div`: truncates towards zero, wraps, and `a / 0` is `0`. */
export const $lean_isize_div = (a, b) =>
  Number(b) === 0 ? 0 : wrapS64(BigInt(a) / BigInt(b));

/** `ISize.neg`. */
export const $lean_isize_neg = (a) => wrapS64(-BigInt(a));

/** `ISize.add`. */
export const $lean_isize_add = (a, b) => wrapS64(BigInt(a) + BigInt(b));
/** `ISize.sub`. */
export const $lean_isize_sub = (a, b) => wrapS64(BigInt(a) - BigInt(b));
/** `ISize.mul`. */
export const $lean_isize_mul = (a, b) => wrapS64(BigInt(a) * BigInt(b));

/** `ISize.land`, on the two's complement. */
export const $lean_isize_land = (a, b) => wrapS64(BigInt(a) & BigInt(b));
/** `ISize.lor`. */
export const $lean_isize_lor = (a, b) => wrapS64(BigInt(a) | BigInt(b));
/** `ISize.xor`. */
export const $lean_isize_xor = (a, b) => wrapS64(BigInt(a) ^ BigInt(b));
/** `ISize.complement`. */
export const $lean_isize_complement = (a) => wrapS64(~BigInt(a));
/** `ISize.shiftLeft`. */
export const $lean_isize_shift_left = (a, b) => wrapS64(BigInt(a) << shift64(b));
/** `ISize.shiftRight`, which is arithmetic: the sign bit is carried in. */
export const $lean_isize_shift_right = (a, b) => wrapS64(BigInt(a) >> shift64(b));
