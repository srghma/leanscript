// The runtime functions that answer with an `Int64`, where an `Int64` is a JavaScript
// number (`int64Repr = num`).
//
// The functions the backend imports (section "imported by the backend") compute exactly
// (over `BigInt` where needed) and answer with a number only when the answer is a safe
// integer (below `2^53` in magnitude); otherwise they throw a `RangeError` (`$toNum53`),
// as the checked `uint53` arithmetic of the backend does, instead of rounding silently.
// `lean_runtime_int64_bigint.mjs` is the same catalogue over `BigInt`s, exact at every size.

const $toNum53 = (x) => {
  if (x > 9007199254740991n || x < -9007199254740991n) {
    throw new RangeError(
      "LeanScript: integer overflow: the result does not fit in a number (use the bigint representation)",
    );
  }
  return Number(x);
};

/* ----------------------------------------------------- imported by the backend */

/** `Bool.toInt64`. */
export const $lean_bool_to_int64 = (a) => a ? 1 : 0;

/** `Int16.toInt64`. */
export const $lean_int16_to_int64 = (a) => a;

/** `Int32.toInt64`. */
export const $lean_int32_to_int64 = (a) => a;

/** `Int64.abs`. */
export const $lean_int64_abs = (a) => {
  a = BigInt(a);
  return $toNum53(BigInt.asIntN(64, a < 0n ? -a : a));
};

/** `Int64.add`. */
export const $lean_int64_add = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(BigInt.asIntN(64, a + b));
};

/** `Int64.complement`. */
export const $lean_int64_complement = (a) => {
  a = BigInt(a);
  return $toNum53(BigInt.asIntN(64, ~a));
};

/** `Int64.div`. */
export const $lean_int64_div = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(b === 0n ? 0n : BigInt.asIntN(64, a / b));
};

/** `Int64.land`. */
export const $lean_int64_land = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(BigInt.asIntN(64, a & b));
};

/** `Int64.lor`. */
export const $lean_int64_lor = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(BigInt.asIntN(64, a | b));
};

/** `Int64.mod`. */
export const $lean_int64_mod = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(b === 0n ? a : a % b);
};

/** `Int64.mul`. */
export const $lean_int64_mul = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(BigInt.asIntN(64, a * b));
};

/** `Int64.neg`. */
export const $lean_int64_neg = (a) => {
  a = BigInt(a);
  return $toNum53(BigInt.asIntN(64, -a));
};

/** `Int64.ofInt`. */
export const $lean_int64_of_int = (a) => {
  a = BigInt(a);
  return $toNum53(BigInt.asIntN(64, a));
};

/** `Int64.ofNat`. */
export const $lean_int64_of_nat = (a) => {
  a = BigInt(a);
  return $toNum53(BigInt.asIntN(64, a));
};

/** `Int64.shiftLeft`. */
export const $lean_int64_shift_left = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(BigInt.asIntN(64, a << (((b % 64n) + 64n) % 64n)));
};

/** `Int64.shiftRight`. */
export const $lean_int64_shift_right = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(a >> (((b % 64n) + 64n) % 64n));
};

/** `Int64.sub`. */
export const $lean_int64_sub = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(BigInt.asIntN(64, a - b));
};

/** `Int64.xor`. */
export const $lean_int64_xor = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(BigInt.asIntN(64, a ^ b));
};

/** `Int8.toInt64`. */
export const $lean_int8_to_int64 = (a) => a;

/* -------------------------------------- not imported by the current backend */

/** `x` taken modulo `2^64`, read as a signed 64-bit value, and then back to a number. */

/** The shift distance Lean uses at 64 bits: the argument taken modulo 64. */

