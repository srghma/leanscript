// UInt64, USize, Nat, Int64, ISize, Int in this file are configured with
// `*Repr = "bignum"` (natRepr/intRepr/usizeRepr/uint64Repr/int64Repr = "bignum").
// All values are represented as native JavaScript BigInts (arbitrary precision).
//
// Rules under `bignum` mode:
// - Comparisons (==, !=, <, >, <=, >=) operate directly on JS BigInts.
// - Fixed-width 64-bit unsigned types (UInt64, USize) wrap arithmetic via `BigInt.asUintN(64, ...)`.
// - Fixed-width 64-bit signed types (Int64, ISize) wrap arithmetic via `BigInt.asIntN(64, ...)`.
// - Unbounded types (Nat, Int) use native BigInt arithmetic without bit-width wrapping.
// - For unsigned types (UInt64, USize, Nat), division uses native truncated integer division:
//   `b !== 0n ? a / b : 0n`.
// - For signed types (Int64, ISize, Int), division follows Euclidean division:
//   `b !== 0n ? (a < 0n && a % b !== 0n ? (b > 0n ? a / b - 1n : a / b + 1n) : a / b) : 0n`.
// - Nat subtraction is saturating: `a >= b ? a - b : 0n`.
// - Nat does not support negation.

// ---------------- TestUInt64 ----------------

export const TestUInt64$add = (a) => (b) => BigInt.asUintN(64, a + b);
export const TestUInt64$sub = (a) => (b) => BigInt.asUintN(64, a - b);
export const TestUInt64$eq = (a) => (b) => a === b;
export const TestUInt64$ne = (a) => (b) => a !== b;
export const TestUInt64$lt = (a) => (b) => a < b;
export const TestUInt64$gt = (a) => (b) => a > b;
export const TestUInt64$le = (a) => (b) => a <= b;
export const TestUInt64$ge = (a) => (b) => a >= b;
export const TestUInt64$mul = (a) => (b) => BigInt.asUintN(64, a * b);
export const TestUInt64$div = (a) => (b) => (b !== 0n ? a / b : 0n);
export const TestUInt64$neg = (a) => BigInt.asUintN(64, -a);

// ---------------- TestUSize ----------------

export const TestUSize$add = (a) => (b) => BigInt.asUintN(64, a + b);
export const TestUSize$sub = (a) => (b) => BigInt.asUintN(64, a - b);
export const TestUSize$eq = (a) => (b) => a === b;
export const TestUSize$ne = (a) => (b) => a !== b;
export const TestUSize$lt = (a) => (b) => a < b;
export const TestUSize$gt = (a) => (b) => a > b;
export const TestUSize$le = (a) => (b) => a <= b;
export const TestUSize$ge = (a) => (b) => a >= b;
export const TestUSize$mul = (a) => (b) => BigInt.asUintN(64, a * b);
export const TestUSize$div = (a) => (b) => (b !== 0n ? a / b : 0n);
export const TestUSize$neg = (a) => BigInt.asUintN(64, -a);

// ---------------- TestNat ----------------

export const TestNat$add = (a) => (b) => a + b;
export const TestNat$sub = (a) => (b) => (a >= b ? a - b : 0n);
export const TestNat$eq = (a) => (b) => a === b;
export const TestNat$ne = (a) => (b) => a !== b;
export const TestNat$lt = (a) => (b) => a < b;
export const TestNat$gt = (a) => (b) => a > b;
export const TestNat$le = (a) => (b) => a <= b;
export const TestNat$ge = (a) => (b) => a >= b;
export const TestNat$mul = (a) => (b) => a * b;
export const TestNat$div = (a) => (b) => (b !== 0n ? a / b : 0n);
// Nat does not support negation

// ---------------- TestInt64 ----------------

export const TestInt64$add = (a) => (b) => BigInt.asIntN(64, a + b);
export const TestInt64$sub = (a) => (b) => BigInt.asIntN(64, a - b);
export const TestInt64$eq = (a) => (b) => a === b;
export const TestInt64$ne = (a) => (b) => a !== b;
export const TestInt64$lt = (a) => (b) => a < b;
export const TestInt64$gt = (a) => (b) => a > b;
export const TestInt64$le = (a) => (b) => a <= b;
export const TestInt64$ge = (a) => (b) => a >= b;
export const TestInt64$mul = (a) => (b) => BigInt.asIntN(64, a * b);
export const TestInt64$div = (a) => (b) =>
(b !== 0n
  ? BigInt.asIntN(64, a < 0n && a % b !== 0n ? (b > 0n ? a / b - 1n : a / b + 1n) : a / b)
  : 0n);
export const TestInt64$neg = (a) => BigInt.asIntN(64, -a);

// ---------------- TestISize ----------------

export const TestISize$add = (a) => (b) => BigInt.asIntN(64, a + b);
export const TestISize$sub = (a) => (b) => BigInt.asIntN(64, a - b);
export const TestISize$eq = (a) => (b) => a === b;
export const TestISize$ne = (a) => (b) => a !== b;
export const TestISize$lt = (a) => (b) => a < b;
export const TestISize$gt = (a) => (b) => a > b;
export const TestISize$le = (a) => (b) => a <= b;
export const TestISize$ge = (a) => (b) => a >= b;
export const TestISize$mul = (a) => (b) => BigInt.asIntN(64, a * b);
export const TestISize$div = (a) => (b) =>
(b !== 0n
  ? BigInt.asIntN(64, a < 0n && a % b !== 0n ? (b > 0n ? a / b - 1n : a / b + 1n) : a / b)
  : 0n);
export const TestISize$neg = (a) => BigInt.asIntN(64, -a);

// ---------------- TestInt ----------------

export const TestInt$add = (a) => (b) => a + b;
export const TestInt$sub = (a) => (b) => a - b;
export const TestInt$eq = (a) => (b) => a === b;
export const TestInt$ne = (a) => (b) => a !== b;
export const TestInt$lt = (a) => (b) => a < b;
export const TestInt$gt = (a) => (b) => a > b;
export const TestInt$le = (a) => (b) => a <= b;
export const TestInt$ge = (a) => (b) => a >= b;
export const TestInt$mul = (a) => (b) => a * b;
export const TestInt$div = (a) => (b) =>
  (b !== 0n ? (a < 0n && a % b !== 0n ? (b > 0n ? a / b - 1n : a / b + 1n) : a / b) : 0n);
export const TestInt$neg = (a) => -a;
