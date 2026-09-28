// The runtime functions that answer with a `UInt64`, where a `UInt64` is a `BigInt`
// (`uint64Repr = bigint`): exact at all 64 bits.  `lean_runtime_uint64_num.mjs` is the
// same catalogue over JavaScript numbers, which hold only 53 bits exactly.

/** `x` taken modulo `2^64`. */
const U64 = (x) => BigInt.asUintN(64, BigInt(x));

/** The shift distance Lean uses at 64 bits: the argument taken modulo 64. */
const shift64 = (b) => ((BigInt(b) % 64n) + 64n) % 64n;

const encoder = new TextEncoder();

/** `UInt64.ofNat`. */
export const $lean_uint64_of_nat = (n) => U64(n);

/** `UInt64.div`: rounds down, and `a / 0` is `0`. */
export const $lean_uint64_div = (a, b) => (U64(b) === 0n ? 0n : U64(a) / U64(b));

/** `UInt64.neg`. */
export const $lean_uint64_neg = (a) => U64(-U64(a));

/** `UInt64.add`. */
export const $lean_uint64_add = (a, b) => U64(U64(a) + U64(b));
/** `UInt64.sub`. */
export const $lean_uint64_sub = (a, b) => U64(U64(a) - U64(b));
/** `UInt64.mul`. */
export const $lean_uint64_mul = (a, b) => U64(U64(a) * U64(b));

/** `UInt64.land`. */
export const $lean_uint64_land = (a, b) => U64(a) & U64(b);
/** `UInt64.lor`. */
export const $lean_uint64_lor = (a, b) => U64(U64(a) | U64(b));
/** `UInt64.xor`. */
export const $lean_uint64_xor = (a, b) => U64(U64(a) ^ U64(b));
/** `UInt64.complement`. */
export const $lean_uint64_complement = (a) => U64(~U64(a));
/** `UInt64.shiftLeft`. */
export const $lean_uint64_shift_left = (a, b) => U64(U64(a) << shift64(b));
/** `UInt64.shiftRight`; the shift is taken modulo 64, as Lean's is. */
export const $lean_uint64_shift_right = (a, b) => U64(U64(a) >> shift64(b));

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
