// The runtime functions that answer with a `UInt64`, where a `UInt64` is a `BigInt`
// (`uint64Repr = bigint`): exact at all 64 bits.  `lean_runtime_uint64_num.mjs` is the
// same catalogue over JavaScript numbers, which hold only 53 bits exactly.

/* ----------------------------------------------------- imported by the backend */

/** `Bool.toUInt64`. */
export const $lean_bool_to_uint64 = (a) => a ? 1n : 0n;

/** `UInt16.toUInt64`. */
export const $lean_uint16_to_uint64 = (a) => BigInt(a);

/** `UInt32.toUInt64`. */
export const $lean_uint32_to_uint64 = (a) => BigInt(a);

/** `UInt64.add`. */
export const $lean_uint64_add = (a, b) => BigInt.asUintN(64, a + b);

/** `UInt64.complement`. */
export const $lean_uint64_complement = (a) => BigInt.asUintN(64, ~a);

/** `UInt64.div`. */
export const $lean_uint64_div = (a, b) => b === 0n ? 0n : BigInt.asUintN(64, a / b);

/** `UInt64.land`. */
export const $lean_uint64_land = (a, b) => BigInt.asUintN(64, a & b);

/** `UInt64.log2`. */
export const $lean_uint64_log2 = (a) => a === 0n ? 0n : BigInt(a.toString(2).length - 1);

/** `UInt64.lor`. */
export const $lean_uint64_lor = (a, b) => BigInt.asUintN(64, a | b);

/** `UInt64.mod`. */
export const $lean_uint64_mod = (a, b) => b === 0n ? a : a % b;

/** `UInt64.mul`. */
export const $lean_uint64_mul = (a, b) => BigInt.asUintN(64, a * b);

/** `UInt64.neg`. */
export const $lean_uint64_neg = (a) => BigInt.asUintN(64, -a);

/** `UInt64.ofNat`, `UInt64.ofNatLT`. */
export const $lean_uint64_of_nat = (a) => BigInt.asUintN(64, BigInt(a));

/** `UInt64.ofBitVec`. */
export const $lean_uint64_of_nat_mk = (a) => BigInt(a);

/** `UInt64.shiftLeft`. */
export const $lean_uint64_shift_left = (a, b) => BigInt.asUintN(64, a << (((b % 64n) + 64n) % 64n));

/** `UInt64.shiftRight`. */
export const $lean_uint64_shift_right = (a, b) => a >> (((b % 64n) + 64n) % 64n);

/** `UInt64.sub`. */
export const $lean_uint64_sub = (a, b) => BigInt.asUintN(64, a - b);

/** `UInt64.xor`. */
export const $lean_uint64_xor = (a, b) => BigInt.asUintN(64, a ^ b);

/** `UInt8.toUInt64`. */
export const $lean_uint8_to_uint64 = (a) => BigInt(a);

/* -------------------------------------- not imported by the current backend */

/** `x` taken modulo `2^64`. */
const U64 = (x) => BigInt.asUintN(64, BigInt(x));

const encoder = new TextEncoder();

/**
 * `String.hash`: FNV-1a over the UTF-8 bytes, taken to 64 bits.  Lean's own hash is
 * not specified by the language, and nothing in a compiled program may depend on its
 * value — only on its being a function of the string.
 */
export const $lean_string_hash = (s) => {
  let h = 0xcbf29ce484222325n;
  for (const b of encoder.encode(s)) {
    h = U64((h ^ BigInt(b)) * 0x100000001b3n);
  }
  return h;
};

/** `instHashableString`: a `Hashable` is its one method. */
export const instHashableString = (s) => $lean_string_hash(s);

/** `instHashableNat`. */
export const instHashableNat = (n) => U64(n);
