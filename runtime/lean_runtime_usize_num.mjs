// The runtime functions that answer with a `USize`, where a `USize` is a JavaScript
// number (`usizeRepr = num`).
//
// A `USize` is 64 bits wide and a number holds only 53 of them exactly, so the wrap is
// computed over `BigInt` and the answer is read back as a number: the arithmetic is
// exact modulo `2^64` and then rounded, which is the trade-off this representation
// makes.  `lean_runtime_usize_bigint.mjs` makes the other one.

/** `x` taken modulo `2^64`, exactly, and then back to a number. */
const wrapU64 = (x) => Number(BigInt.asUintN(64, BigInt(x)));

/** The shift distance Lean uses at 64 bits: the argument taken modulo 64. */
const shift64 = (b) => ((BigInt(b) % 64n) + 64n) % 64n;

/** `USize.ofNat`. */
export const $lean_usize_of_nat = (n) => wrapU64(n);

/**
 * `UInt64.toUSize`.  A `USize` is a number here, so the value is cut to the 53 bits a
 * number holds exactly — the *low* bits, which are the ones a hash bucket is masked
 * out of.
 */
export const $lean_uint64_to_usize = (a) =>
  Number(BigInt.asUintN(64, BigInt(a)) & 0x1fffffffffffffn);

/** `USize.div`: rounds down, and `a / 0` is `0`. */
export const $lean_usize_div = (a, b) =>
  Number(b) === 0 ? 0 : wrapU64(BigInt(a) / BigInt(b));

/** `USize.neg`. */
export const $lean_usize_neg = (a) => wrapU64(-BigInt(a));

/** `USize.add`. */
export const $lean_usize_add = (a, b) => wrapU64(BigInt(a) + BigInt(b));
/** `USize.sub`. */
export const $lean_usize_sub = (a, b) => wrapU64(BigInt(a) - BigInt(b));
/** `USize.mul`. */
export const $lean_usize_mul = (a, b) => wrapU64(BigInt(a) * BigInt(b));

/** `USize.land`. */
export const $lean_usize_land = (a, b) => wrapU64(BigInt(a) & BigInt(b));
/** `USize.lor`. */
export const $lean_usize_lor = (a, b) => wrapU64(BigInt(a) | BigInt(b));
/** `USize.xor`. */
export const $lean_usize_xor = (a, b) => wrapU64(BigInt(a) ^ BigInt(b));
/** `USize.complement`. */
export const $lean_usize_complement = (a) => wrapU64(~BigInt(a));
/** `USize.shiftLeft`. */
export const $lean_usize_shift_left = (a, b) => wrapU64(BigInt(a) << shift64(b));
/** `USize.shiftRight`; the value is unsigned, so the shift brings in zeros. */
export const $lean_usize_shift_right = (a, b) => wrapU64(BigInt(a) >> shift64(b));
