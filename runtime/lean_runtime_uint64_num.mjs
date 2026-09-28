// The runtime functions that answer with a `UInt64`, where a `UInt64` is a JavaScript
// number (`uint64Repr = num`).
//
// A `UInt64` is 64 bits wide and a number holds only 53 of them exactly, so every
// answer here is exact modulo `2^64` and then rounded to a number — the trade-off this
// representation makes.  The two hashes are the exception: a hash is only ever a
// function of its argument, and losing its *low* bits would put every key in one
// bucket, so they are cut to the 53 bits a number holds rather than rounded.
// `lean_runtime_uint64_bigint.mjs` makes the other trade-off: nothing is cut at all.

/** `x` taken modulo `2^64`, exactly, and then back to a number. */
const wrapU64 = (x) => Number(BigInt.asUintN(64, BigInt(x)));

/** `x` cut to the 53 bits a JavaScript number holds exactly, keeping the low ones. */
const low53 = (x) => Number(BigInt.asUintN(64, BigInt(x)) & 0x1fffffffffffffn);

/** The shift distance Lean uses at 64 bits: the argument taken modulo 64. */
const shift64 = (b) => ((BigInt(b) % 64n) + 64n) % 64n;

const encoder = new TextEncoder();

/** `UInt64.ofNat`. */
export const $lean_uint64_of_nat = (n) => wrapU64(n);

/** `UInt64.div`: rounds down, and `a / 0` is `0`. */
export const $lean_uint64_div = (a, b) =>
  Number(b) === 0 ? 0 : wrapU64(BigInt(a) / BigInt(b));

/** `UInt64.neg`. */
export const $lean_uint64_neg = (a) => wrapU64(-BigInt(a));

/** `UInt64.add`. */
export const $lean_uint64_add = (a, b) => wrapU64(BigInt(a) + BigInt(b));
/** `UInt64.sub`. */
export const $lean_uint64_sub = (a, b) => wrapU64(BigInt(a) - BigInt(b));
/** `UInt64.mul`. */
export const $lean_uint64_mul = (a, b) => wrapU64(BigInt(a) * BigInt(b));

/** `UInt64.land`. */
export const $lean_uint64_land = (a, b) => wrapU64(BigInt(a) & BigInt(b));
/** `UInt64.lor`. */
export const $lean_uint64_lor = (a, b) => wrapU64(BigInt(a) | BigInt(b));
/** `UInt64.xor`. */
export const $lean_uint64_xor = (a, b) => wrapU64(BigInt(a) ^ BigInt(b));
/** `UInt64.complement`. */
export const $lean_uint64_complement = (a) => wrapU64(~BigInt(a));
/** `UInt64.shiftLeft`. */
export const $lean_uint64_shift_left = (a, b) => wrapU64(BigInt(a) << shift64(b));
/** `UInt64.shiftRight`; the shift is taken modulo 64, as Lean's is. */
export const $lean_uint64_shift_right = (a, b) => wrapU64(BigInt(a) >> shift64(b));

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
