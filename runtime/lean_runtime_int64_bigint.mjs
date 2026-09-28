// The runtime functions that answer with an `Int64`, where an `Int64` is a `BigInt`
// (`int64Repr = bigint`): exact at all 64 bits.  `lean_runtime_int64_num.mjs` is the
// same catalogue over JavaScript numbers, which hold only 53 bits exactly.

/** `x` taken modulo `2^64` and read as a signed 64-bit value. */
const S64 = (x) => BigInt.asIntN(64, BigInt(x));

/** The shift distance Lean uses at 64 bits: the argument taken modulo 64. */
const shift64 = (b) => ((BigInt(b) % 64n) + 64n) % 64n;

/** `Int64.ofNat`. */
export const $lean_int64_of_nat = (n) => S64(n);

/** `Int64.div`: truncates towards zero, wraps, and `a / 0` is `0`. */
export const $lean_int64_div = (a, b) => (S64(b) === 0n ? 0n : S64(S64(a) / S64(b)));

/** `Int64.neg`. */
export const $lean_int64_neg = (a) => S64(-S64(a));

/** `Int64.add`. */
export const $lean_int64_add = (a, b) => S64(S64(a) + S64(b));
/** `Int64.sub`. */
export const $lean_int64_sub = (a, b) => S64(S64(a) - S64(b));
/** `Int64.mul`. */
export const $lean_int64_mul = (a, b) => S64(S64(a) * S64(b));

/** `Int64.land`, on the two's complement. */
export const $lean_int64_land = (a, b) => S64(S64(a) & S64(b));
/** `Int64.lor`. */
export const $lean_int64_lor = (a, b) => S64(S64(a) | S64(b));
/** `Int64.xor`. */
export const $lean_int64_xor = (a, b) => S64(S64(a) ^ S64(b));
/** `Int64.complement`. */
export const $lean_int64_complement = (a) => S64(~S64(a));
/** `Int64.shiftLeft`. */
export const $lean_int64_shift_left = (a, b) => S64(S64(a) << shift64(b));
/** `Int64.shiftRight`, which is arithmetic: the sign bit is carried in. */
export const $lean_int64_shift_right = (a, b) => S64(S64(a) >> shift64(b));
