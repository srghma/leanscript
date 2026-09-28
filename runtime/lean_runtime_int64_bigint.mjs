// The runtime functions that answer with an `Int64`, where an `Int64` is a `BigInt`
// (`int64Repr = bigint`): exact at all 64 bits.  `lean_runtime_int64_num.mjs` is the
// same catalogue over JavaScript numbers, which hold only 53 bits exactly.

/* ----------------------------------------------------- imported by the backend */

/** `Bool.toInt64`. */
export const $lean_bool_to_int64 = (a) => a ? 1n : 0n;

/** `Int16.toInt64`. */
export const $lean_int16_to_int64 = (a) => BigInt(a);

/** `Int32.toInt64`. */
export const $lean_int32_to_int64 = (a) => BigInt(a);

/** `Int64.abs`. */
export const $lean_int64_abs = (a) => BigInt.asIntN(64, a < 0n ? -a : a);

/** `Int64.add`. */
export const $lean_int64_add = (a, b) => BigInt.asIntN(64, a + b);

/** `Int64.complement`. */
export const $lean_int64_complement = (a) => BigInt.asIntN(64, ~a);

/** `Int64.div`. */
export const $lean_int64_div = (a, b) => b === 0n ? 0n : BigInt.asIntN(64, a / b);

/** `Int64.land`. */
export const $lean_int64_land = (a, b) => BigInt.asIntN(64, a & b);

/** `Int64.lor`. */
export const $lean_int64_lor = (a, b) => BigInt.asIntN(64, a | b);

/** `Int64.mod`. */
export const $lean_int64_mod = (a, b) => b === 0n ? a : a % b;

/** `Int64.mul`. */
export const $lean_int64_mul = (a, b) => BigInt.asIntN(64, a * b);

/** `Int64.neg`. */
export const $lean_int64_neg = (a) => BigInt.asIntN(64, -a);

/** `Int64.ofInt`. */
export const $lean_int64_of_int = (a) => BigInt.asIntN(64, BigInt(a));

/** `Int64.ofNat`. */
export const $lean_int64_of_nat = (a) => BigInt.asIntN(64, BigInt(a));

/** `Int64.shiftLeft`. */
export const $lean_int64_shift_left = (a, b) => BigInt.asIntN(64, a << (((b % 64n) + 64n) % 64n));

/** `Int64.shiftRight`. */
export const $lean_int64_shift_right = (a, b) => a >> (((b % 64n) + 64n) % 64n);

/** `Int64.sub`. */
export const $lean_int64_sub = (a, b) => BigInt.asIntN(64, a - b);

/** `Int64.xor`. */
export const $lean_int64_xor = (a, b) => BigInt.asIntN(64, a ^ b);

/** `Int8.toInt64`. */
export const $lean_int8_to_int64 = (a) => BigInt(a);

/* -------------------------------------- not imported by the current backend */

/** `x` taken modulo `2^64` and read as a signed 64-bit value. */

/** The shift distance Lean uses at 64 bits: the argument taken modulo 64. */

