// Nat, Int, USize, UInt64, Int64 (and ISize — see note at bottom) can exceed
// Number.MAX_SAFE_INTEGER (2^53 - 1), so representing them as a plain Number is a
// choice with a real correctness boundary, not a free simplification. This file is
// the "num" output for natRepr/intRepr/usizeRepr/uint64Repr/int64Repr = .num.
// It is EXACT for values whose magnitude stays under 2^53 (~9.007e15), and loses
// precision beyond that — same as any other double-based arithmetic in JS. If you
// need correctness across the full 64-bit range, use the matching -bigint.js file
// for that type instead.
//
// Technique: split each Number into a low 32-bit word and a high word via floor
// division by 2^32 (works for negative values too, since Math.floor rounds toward
// -Infinity, giving the correct two's-complement low word). AND/OR/XOR/complement
// are then done natively per-word (each word safely fits int32) and recombined —
// this is exact as long as the original Number was itself exact (< 2^53).
// shiftLeft/shiftRight are done via multiply/divide by a power of two, matching
// plain floating-point scaling — exact only while the result stays under 2^53.

const TWO32 = 4294967296; // 2**32, exactly representable
const TWO64 = TWO32 * TWO32; // 2**64, exactly representable (power of two)

// hi is chosen so that hi*2^32 + lo === a exactly, with lo in [0, 2^32).
// Works for negative a too: e.g. a=-5 -> hi=-1, lo=4294967291 (0xFFFFFFFB).
function hi(a) {
  return Math.floor(a / TWO32);
}

function lo(a) {
  return a - hi(a) * TWO32;
}

function fromHiLo(hi, lo) {
  return hi * TWO32 + lo;
}

// ---------------- TestUSize (assumes 64-bit platform) ----------------

export const TestUSize$land = (a) => (b) => {
  const ah = hi(a), al = lo(a), bh = hi(b), bl = lo(b);
  return fromHiLo((ah & bh) >>> 0, (al & bl) >>> 0);
};
export const TestUSize$lor = (a) => (b) => {
  const ah = hi(a), al = lo(a), bh = hi(b), bl = lo(b);
  return fromHiLo((ah | bh) >>> 0, (al | bl) >>> 0);
};
export const TestUSize$xor = (a) => (b) => {
  const ah = hi(a), al = lo(a), bh = hi(b), bl = lo(b);
  return fromHiLo((ah ^ bh) >>> 0, (al ^ bl) >>> 0);
};
export const TestUSize$complement = (a) => {
  const ah = hi(a), al = lo(a);
  return fromHiLo((~ah) >>> 0, (~al) >>> 0);
};
export const TestUSize$shiftLeft = (a) => (b) => {
  const amt = ((b % 64) + 64) % 64;
  return (a * 2 ** amt) % TWO64;
};
export const TestUSize$shiftRight = (a) => (b) => {
  const amt = ((b % 64) + 64) % 64;
  return Math.floor(a / 2 ** amt);
};

// ---------------- TestUInt64 ----------------

export const TestUInt64$land = TestUSize$land;
export const TestUInt64$lor = TestUSize$lor;
export const TestUInt64$xor = TestUSize$xor;
export const TestUInt64$complement = TestUSize$complement;
export const TestUInt64$shiftLeft = TestUSize$shiftLeft;
export const TestUInt64$shiftRight = TestUSize$shiftRight;

// ---------------- TestInt64 / TestISize (signed 64-bit) ----------------
// land/lor/xor need no re-sign-extension (same argument as the 32-bit signed
// types): the hi word already carries the correct sign bit pattern, so the
// per-word op produces a correctly sign-extended result directly.

export const TestInt64$land = (a) => (b) => {
  const ah = hi(a), al = lo(a), bh = hi(b), bl = lo(b);
  return fromHiLo(ah & bh, (al & bl) >>> 0);
};
export const TestInt64$lor = (a) => (b) => {
  const ah = hi(a), al = lo(a), bh = hi(b), bl = lo(b);
  return fromHiLo(ah | bh, (al | bl) >>> 0);
};
export const TestInt64$xor = (a) => (b) => {
  const ah = hi(a), al = lo(a), bh = hi(b), bl = lo(b);
  return fromHiLo(ah ^ bh, (al ^ bl) >>> 0);
};
export const TestInt64$complement = (a) => -a - 1;
export const TestInt64$shiftLeft = (a) => (b) => {
  const amt = ((b % 64) + 64) % 64;
  return a * 2 ** amt; // caller's responsibility to stay within safe/expected range
};
export const TestInt64$shiftRight = (a) => (b) => {
  const amt = ((b % 64) + 64) % 64;
  return Math.floor(a / 2 ** amt); // floor division = arithmetic (sign-extending) shift
};

export const TestISize$land = TestInt64$land;
export const TestISize$lor = TestInt64$lor;
export const TestISize$xor = TestInt64$xor;
export const TestISize$complement = TestInt64$complement;
export const TestISize$shiftLeft = TestInt64$shiftLeft;
export const TestISize$shiftRight = TestInt64$shiftRight;

// ---------------- TestNat (arbitrary precision, unsigned, no complement) ----------------
// Same hi/lo technique, but with no fixed width to wrap shifts into — a shift by a
// very large amount will just grow (or eventually overflow to Infinity), same
// caveat as everything else in this file.

export const TestNat$land = (a) => (b) => {
  const ah = hi(a), al = lo(a), bh = hi(b), bl = lo(b);
  return fromHiLo((ah & bh) >>> 0, (al & bl) >>> 0);
};
export const TestNat$lor = (a) => (b) => {
  const ah = hi(a), al = lo(a), bh = hi(b), bl = lo(b);
  return fromHiLo((ah | bh) >>> 0, (al | bl) >>> 0);
};
export const TestNat$xor = (a) => (b) => {
  const ah = hi(a), al = lo(a), bh = hi(b), bl = lo(b);
  return fromHiLo((ah ^ bh) >>> 0, (al ^ bl) >>> 0);
};
export const TestNat$shiftLeft = (a) => (b) => a * 2 ** b;
export const TestNat$shiftRight = (a) => (b) => Math.floor(a / 2 ** b);
// TestNat$complement intentionally omitted — Nat has no fixed bit width.

// ---------------- TestInt (arbitrary precision signed, only complement defined) ----------------

export const TestInt$complement = (a) => -a - 1;

// NOTE on ISize: your JsNumRepr enum lists natRepr/intRepr/usizeRepr/uint64Repr/
// int64Repr but no isizeRepr. This file assumes ISize follows the same mode as
// Int64 (equivalently USize's unsigned counterpart) — flag if it should be its
// own independently configurable switch instead.
