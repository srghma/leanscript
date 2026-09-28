// The runtime functions that answer with an `ISize`, where an `ISize` is a `BigInt`
// (`isizeRepr = bigint`): exact at all 64 bits.  `lean_runtime_isize_num.mjs` is the
// same catalogue over JavaScript numbers, which hold only 53 bits exactly.

/** `x` taken modulo `2^64` and read as a signed 64-bit value. */
const S64 = (x) => BigInt.asIntN(64, BigInt(x));

/** The shift distance Lean uses at 64 bits: the argument taken modulo 64. */
const shift64 = (b) => ((BigInt(b) % 64n) + 64n) % 64n;

/** `ISize.ofNat`. */
export const $lean_isize_of_nat = (n) => S64(n);

/** `ISize.div`: truncates towards zero, wraps, and `a / 0` is `0`. */
export const $lean_isize_div = (a, b) => (S64(b) === 0n ? 0n : S64(S64(a) / S64(b)));

/** `ISize.neg`. */
export const $lean_isize_neg = (a) => S64(-S64(a));

/** `ISize.add`. */
export const $lean_isize_add = (a, b) => S64(S64(a) + S64(b));
/** `ISize.sub`. */
export const $lean_isize_sub = (a, b) => S64(S64(a) - S64(b));
/** `ISize.mul`. */
export const $lean_isize_mul = (a, b) => S64(S64(a) * S64(b));

/** `ISize.land`, on the two's complement. */
export const $lean_isize_land = (a, b) => S64(S64(a) & S64(b));
/** `ISize.lor`. */
export const $lean_isize_lor = (a, b) => S64(S64(a) | S64(b));
/** `ISize.xor`. */
export const $lean_isize_xor = (a, b) => S64(S64(a) ^ S64(b));
/** `ISize.complement`. */
export const $lean_isize_complement = (a) => S64(~S64(a));
/** `ISize.shiftLeft`. */
export const $lean_isize_shift_left = (a, b) => S64(S64(a) << shift64(b));
/** `ISize.shiftRight`, which is arithmetic: the sign bit is carried in. */
export const $lean_isize_shift_right = (a, b) => S64(S64(a) >> shift64(b));
