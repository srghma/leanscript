// The runtime functions that answer with a `USize`, where a `USize` is a `BigInt`
// (`usizeRepr = bigint`): exact at all 64 bits.  `lean_runtime_usize_num.mjs` is the
// same catalogue over JavaScript numbers.

/** `x` taken modulo `2^64`. */
const U64 = (x) => BigInt.asUintN(64, BigInt(x));

/** The shift distance Lean uses at 64 bits: the argument taken modulo 64. */
const shift64 = (b) => ((BigInt(b) % 64n) + 64n) % 64n;

/** `USize.ofNat`. */
export const $lean_usize_of_nat = (n) => U64(n);

/** `UInt64.toUSize`: both are 64 bits wide here, so nothing is cut. */
export const $lean_uint64_to_usize = (a) => U64(a);

/** `USize.div`: rounds down, and `a / 0` is `0`. */
export const $lean_usize_div = (a, b) => (U64(b) === 0n ? 0n : U64(a) / U64(b));

/** `USize.neg`. */
export const $lean_usize_neg = (a) => U64(-U64(a));

/** `USize.add`. */
export const $lean_usize_add = (a, b) => U64(U64(a) + U64(b));
/** `USize.sub`. */
export const $lean_usize_sub = (a, b) => U64(U64(a) - U64(b));
/** `USize.mul`. */
export const $lean_usize_mul = (a, b) => U64(U64(a) * U64(b));

/** `USize.land`. */
export const $lean_usize_land = (a, b) => U64(a) & U64(b);
/** `USize.lor`. */
export const $lean_usize_lor = (a, b) => U64(U64(a) | U64(b));
/** `USize.xor`. */
export const $lean_usize_xor = (a, b) => U64(U64(a) ^ U64(b));
/** `USize.complement`. */
export const $lean_usize_complement = (a) => U64(~U64(a));
/** `USize.shiftLeft`. */
export const $lean_usize_shift_left = (a, b) => U64(U64(a) << shift64(b));
/** `USize.shiftRight`; the value is unsigned, so the shift brings in zeros. */
export const $lean_usize_shift_right = (a, b) => U64(U64(a) >> shift64(b));
