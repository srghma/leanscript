// This is the "bigint" output for natRepr/intRepr/usizeRepr/uint64Repr/int64Repr
// = .bigint. Every value here is a native JS `BigInt`, so — unlike the -num.js
// sibling file — there is NO precision boundary at all: this file is exact for
// every value these types can hold, full stop.
//
// Verified against Lean core's actual semantics (Init/Data/UInt/Bitwise.lean):
// UInt8/16/32/64/USize's `<<<`/`>>>` reduce the shift amount mod the type's bit
// width *before* shifting (e.g. `UInt64.toNat_shiftLeft : (a <<< b).toNat =
// a.toNat <<< (b.toNat % 64) % 2^64`), and `shiftLeft`'s result is truncated mod
// 2^width. So normalizing the shift amount mod width below is correct — Lean
// does NOT zero out shifts that are `>= width` the way a naive BitVec-width
// truncation might suggest.
//
// Nat/Int need no width-specific handling at all in this file: JS BigInt is
// itself arbitrary-precision, so it's already an exact model of Lean's Nat/Int —
// no hi/lo splitting, no masking, just the native operators.

const MASK64 = (1n << 64n) - 1n;
const SIGN64 = 1n << 63n;
const TWO64 = 1n << 64n;

function mod64(n) {
  return ((n % 64n) + 64n) % 64n;
}

// ---------------- TestUSize / TestUInt64 (unsigned 64-bit) ----------------

export const TestUSize$land = (a) => (b) => (a & b) & MASK64;
export const TestUSize$lor = (a) => (b) => (a | b) & MASK64;
export const TestUSize$xor = (a) => (b) => (a ^ b) & MASK64;
export const TestUSize$complement = (a) => (~a) & MASK64;
export const TestUSize$shiftLeft = (a) => (b) => (a << mod64(b)) & MASK64;
export const TestUSize$shiftRight = (a) => (b) => a >> mod64(b);

export const TestUInt64$land = TestUSize$land;
export const TestUInt64$lor = TestUSize$lor;
export const TestUInt64$xor = TestUSize$xor;
export const TestUInt64$complement = TestUSize$complement;
export const TestUInt64$shiftLeft = TestUSize$shiftLeft;
export const TestUInt64$shiftRight = TestUSize$shiftRight;

// ---------------- TestInt64 / TestISize (signed 64-bit) ----------------

export const TestInt64$land = (a) => (b) => a & b;
export const TestInt64$lor = (a) => (b) => a | b;
export const TestInt64$xor = (a) => (b) => a ^ b;
export const TestInt64$complement = (a) => ~a;
export const TestInt64$shiftRight = (a) => (b) => a >> mod64(b);
export const TestInt64$shiftLeft = (a) => (b) => {
  const amt = mod64(b);
  const au = a < 0n ? a + TWO64 : a;
  const r = (au << amt) & MASK64;
  return r >= SIGN64 ? r - TWO64 : r;
};

export const TestISize$land = TestInt64$land;
export const TestISize$lor = TestInt64$lor;
export const TestISize$xor = TestInt64$xor;
export const TestISize$complement = TestInt64$complement;
export const TestISize$shiftLeft = TestInt64$shiftLeft;
export const TestISize$shiftRight = TestInt64$shiftRight;

// ---------------- TestNat (arbitrary precision, unsigned, no complement) ----------------

export const TestNat$land = (a) => (b) => a & b;
export const TestNat$lor = (a) => (b) => a | b;
export const TestNat$xor = (a) => (b) => a ^ b;
export const TestNat$shiftLeft = (a) => (b) => a << b;
export const TestNat$shiftRight = (a) => (b) => a >> b;

// ---------------- TestInt (arbitrary precision signed, only complement defined) ----------------

export const TestInt$complement = (a) => ~a;
