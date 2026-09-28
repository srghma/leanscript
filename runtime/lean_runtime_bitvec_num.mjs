// The runtime functions that answer with a `BitVec w`, where a bit vector is a
// JavaScript number (`bitvecRepr = num`).
//
// A number holds an integer exactly only below `2^53`, so the wrap is computed over
// `BigInt` and the answer is read back as a number: the arithmetic is exact modulo
// `2^w` and then rounded, which is the trade-off this representation makes.  The width
// itself is a `Nat`, so it arrives as a number or as a `BigInt` depending on `natRepr`;
// every function reads it through `W` and so accepts both.
// `lean_runtime_bitvec_bigint.mjs` makes the other trade-off.

/** The width, as a JavaScript number, whichever representation a `Nat` has. */
const W = (w) => Number(w);

/** Either representation of a bit vector, lifted to a `BigInt`. */
const bi = (x) => BigInt(x);

/** `x` cut to `w` bits, and back to a number. */
const val = (w, x) => Number(BigInt.asUintN(W(w), bi(x)));

/** `BitVec.ofNat`: the natural number cut to `w` bits. */
export const BitVec_ofNat = (w, n) => val(w, n);

/** `BitVec.add`. */
export const BitVec_add = (w, a, b) => val(w, bi(a) + bi(b));
/** `BitVec.sub`. */
export const BitVec_sub = (w, a, b) => val(w, bi(a) - bi(b));
/** `BitVec.mul`. */
export const BitVec_mul = (w, a, b) => val(w, bi(a) * bi(b));
/** `BitVec.neg`. */
export const BitVec_neg = (w, a) => val(w, -bi(a));

/** `BitVec.udiv`: unsigned division, and `a / 0` is `0` as `Nat.div` is. */
export const BitVec_udiv = (w, a, b) =>
  bi(b) === 0n ? val(w, 0n) : val(w, bi(a) / bi(b));
/** `BitVec.umod`: unsigned remainder, and `a % 0` is `a` as `Nat.mod` is. */
export const BitVec_umod = (w, a, b) =>
  bi(b) === 0n ? val(w, a) : val(w, bi(a) % bi(b));

/** `BitVec.and`. */
export const BitVec_and = (w, a, b) => val(w, bi(a) & bi(b));
/** `BitVec.or`. */
export const BitVec_or = (w, a, b) => val(w, bi(a) | bi(b));
/** `BitVec.xor`. */
export const BitVec_xor = (w, a, b) => val(w, bi(a) ^ bi(b));
/** `BitVec.not`: the complement inside `w` bits. */
export const BitVec_not = (w, a) => val(w, ~bi(a));

/**
 * `BitVec.shiftLeft`.  The distance is a `Nat` and is *not* taken modulo the width:
 * shifting by the width or more answers zero, which is also what keeps the `BigInt`
 * the wrap is computed over from being built at an absurd size.
 */
export const BitVec_shiftLeft = (w, a, n) =>
  bi(n) >= bi(W(w)) ? val(w, 0n) : val(w, bi(a) << bi(n));
/** `BitVec.ushiftRight`: the value is unsigned, so the shift brings in zeros. */
export const BitVec_ushiftRight = (w, a, n) =>
  bi(n) >= bi(W(w)) ? val(w, 0n) : val(w, bi(a) >> bi(n));
/** `BitVec.sshiftRight`: the shift of the *signed* reading, so it brings in the sign. */
export const BitVec_sshiftRight = (w, a, n) => {
  const signed = BigInt.asIntN(W(w), bi(a));
  const d = bi(n) >= bi(W(w)) ? bi(W(w)) : bi(n);
  return val(w, signed >> d);
};

/** `UInt64.toBitVec`: a `UInt64` and a `BitVec 64` are held the same way. */
export const $lean_uint64_to_bitvec = (a) => val(64, a);
/** `USize.toBitVec`: a `USize` is 64 bits wide, and is held the same way. */
export const $lean_usize_to_bitvec = (a) => val(64, a);
