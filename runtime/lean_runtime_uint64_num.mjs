// The runtime functions that answer with a `UInt64`, where a `UInt64` is a JavaScript
// number (`uint64Repr = num`).
//
// The functions the backend imports (section "imported by the backend") compute exactly
// (over `BigInt` where needed) and answer with a number only when the answer is a safe
// integer (below `2^53` in magnitude); otherwise they throw a `RangeError` (`$toNum53`),
// as the checked `uint53` arithmetic of the backend does, instead of rounding silently.
// The two hashes are the exception: they are cut to the low 53 bits (a hash is only a
// function of its argument, and losing its low bits would put every key in one bucket).
// `lean_runtime_uint64_bigint.mjs` is the same catalogue over `BigInt`s, exact at every size.

const $toNum53 = (x) => {
  if (x > 9007199254740991n || x < -9007199254740991n) {
    throw new RangeError(
      "LeanScript: integer overflow: the result does not fit in a number (use the bigint representation)",
    );
  }
  return Number(x);
};

/* ----------------------------------------------------- imported by the backend */

/** `Bool.toUInt64`. */
export const $lean_bool_to_uint64 = (a) => a ? 1 : 0;

/** `UInt16.toUInt64`. */
export const $lean_uint16_to_uint64 = (a) => a;

/** `UInt32.toUInt64`. */
export const $lean_uint32_to_uint64 = (a) => a;

/** `UInt64.add`. */
export const $lean_uint64_add = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(BigInt.asUintN(64, a + b));
};

/** `UInt64.complement`. */
export const $lean_uint64_complement = (a) => {
  a = BigInt(a);
  return $toNum53(BigInt.asUintN(64, ~a));
};

/** `UInt64.div`. */
export const $lean_uint64_div = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(b === 0n ? 0n : BigInt.asUintN(64, a / b));
};

/** `UInt64.land`. */
export const $lean_uint64_land = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(BigInt.asUintN(64, a & b));
};

/** `UInt64.log2`. */
export const $lean_uint64_log2 = (a) => {
  a = BigInt(a);
  return $toNum53(a === 0n ? 0n : BigInt(a.toString(2).length - 1));
};

/** `UInt64.lor`. */
export const $lean_uint64_lor = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(BigInt.asUintN(64, a | b));
};

/** `UInt64.mod`. */
export const $lean_uint64_mod = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(b === 0n ? a : a % b);
};

/** `UInt64.mul`. */
export const $lean_uint64_mul = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(BigInt.asUintN(64, a * b));
};

/** `UInt64.neg`. */
export const $lean_uint64_neg = (a) => {
  a = BigInt(a);
  return $toNum53(BigInt.asUintN(64, -a));
};

/** `UInt64.ofNatLT`, `UInt64.ofNat`. */
export const $lean_uint64_of_nat = (a) => {
  a = BigInt(a);
  return $toNum53(BigInt.asUintN(64, a));
};

/** `UInt64.ofBitVec`: the argument may be a `BigInt` or a number. */
export const $lean_uint64_of_nat_mk = (a) => (typeof a === "bigint" ? $toNum53(a) : a);

/** `UInt64.shiftLeft`. */
export const $lean_uint64_shift_left = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(BigInt.asUintN(64, a << (((b % 64n) + 64n) % 64n)));
};

/** `UInt64.shiftRight`. */
export const $lean_uint64_shift_right = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(a >> (((b % 64n) + 64n) % 64n));
};

/** `UInt64.sub`. */
export const $lean_uint64_sub = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(BigInt.asUintN(64, a - b));
};

/** `UInt64.xor`. */
export const $lean_uint64_xor = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(BigInt.asUintN(64, a ^ b));
};

/** `UInt8.toUInt64`. */
export const $lean_uint8_to_uint64 = (a) => a;

/* -------------------------------------- not imported by the current backend */

/** `x` taken modulo `2^64`, exactly, and then back to a number. */

/** `x` cut to the 53 bits a JavaScript number holds exactly, keeping the low ones. */
const low53 = (x) => Number(BigInt.asUintN(64, BigInt(x)) & 0x1fffffffffffffn);

const encoder = new TextEncoder();

/**
 * `String.hash`.  Lean's own hash is not specified by the language, and nothing in a
 * compiled program may depend on its value — only on its being a function of the
 * string.  This is FNV-1a over the UTF-8 bytes, taken to 64 bits and then cut to the
 * 53 a number holds.
 */
export const $lean_string_hash = (s) => {
  let h = 0xcbf29ce484222325n;
  for (const b of encoder.encode(s)) {
    h = BigInt.asUintN(64, (h ^ BigInt(b)) * 0x100000001b3n);
  }
  return low53(h);
};

/** `instHashableString`: a `Hashable` is its one method. */
export const instHashableString = (s) => $lean_string_hash(s);

/** `instHashableNat`. */
export const instHashableNat = (n) => low53(n);
