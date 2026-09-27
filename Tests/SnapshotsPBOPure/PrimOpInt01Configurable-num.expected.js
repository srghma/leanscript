// UInt64, USize, Nat, Int64, ISize, Int in this file are configured with
// `*Repr = "num"` (natRepr/intRepr/usizeRepr/uint64Repr/int64Repr = "num").
// All values are represented as plain JS Numbers (IEEE-754 double-precision floats,
// safe up to Number.MAX_SAFE_INTEGER = 2^53 - 1).
//
// Rules under `num` mode:
// - Comparisons (==, !=, <, >, <=, >=) operate directly on JS Numbers.
// - Basic arithmetic (+, -, *) operates natively via `+`, `-`, `*`.
// - For unsigned types (UInt64, USize, Nat), division truncates toward zero / floor:
//   `b !== 0 ? Math.floor(a / b) : 0`.
// - For signed types (Int64, ISize, Int), division follows Euclidean division:
//   `b > 0 ? Math.floor(a / b) : b < 0 ? -Math.floor(a / -b) : 0`.
// - Nat subtraction is saturating: `Math.max(0, a - b)`.
// - Nat does not support negation.

// ---------------- TestUInt64 ----------------

export const TestUInt64$add = (a) => (b) => a + b;
export const TestUInt64$sub = (a) => (b) => a - b;
export const TestUInt64$eq = (a) => (b) => a === b;
export const TestUInt64$ne = (a) => (b) => a !== b;
export const TestUInt64$lt = (a) => (b) => a < b;
export const TestUInt64$gt = (a) => (b) => a > b;
export const TestUInt64$le = (a) => (b) => a <= b;
export const TestUInt64$ge = (a) => (b) => a >= b;
export const TestUInt64$mul = (a) => (b) => a * b;
export const TestUInt64$div = (a) => (b) => (b !== 0 ? Math.floor(a / b) : 0);
export const TestUInt64$neg = (a) => -a;

// ---------------- TestUSize ----------------

export const TestUSize$add = (a) => (b) => a + b;
export const TestUSize$sub = (a) => (b) => a - b;
export const TestUSize$eq = (a) => (b) => a === b;
export const TestUSize$ne = (a) => (b) => a !== b;
export const TestUSize$lt = (a) => (b) => a < b;
export const TestUSize$gt = (a) => (b) => a > b;
export const TestUSize$le = (a) => (b) => a <= b;
export const TestUSize$ge = (a) => (b) => a >= b;
export const TestUSize$mul = (a) => (b) => a * b;
export const TestUSize$div = (a) => (b) => (b !== 0 ? Math.floor(a / b) : 0);
export const TestUSize$neg = (a) => -a;

// ---------------- TestNat ----------------

export const TestNat$add = (a) => (b) => a + b;
export const TestNat$sub = (a) => (b) => Math.max(0, a - b);
export const TestNat$eq = (a) => (b) => a === b;
export const TestNat$ne = (a) => (b) => a !== b;
export const TestNat$lt = (a) => (b) => a < b;
export const TestNat$gt = (a) => (b) => a > b;
export const TestNat$le = (a) => (b) => a <= b;
export const TestNat$ge = (a) => (b) => a >= b;
export const TestNat$mul = (a) => (b) => a * b;
export const TestNat$div = (a) => (b) => (b !== 0 ? Math.floor(a / b) : 0);
// Nat does not support negation

// ---------------- TestInt64 ----------------

export const TestInt64$add = (a) => (b) => a + b;
export const TestInt64$sub = (a) => (b) => a - b;
export const TestInt64$eq = (a) => (b) => a === b;
export const TestInt64$ne = (a) => (b) => a !== b;
export const TestInt64$lt = (a) => (b) => a < b;
export const TestInt64$gt = (a) => (b) => a > b;
export const TestInt64$le = (a) => (b) => a <= b;
export const TestInt64$ge = (a) => (b) => a >= b;
export const TestInt64$mul = (a) => (b) => a * b;
export const TestInt64$div = (a) => (b) =>
  b > 0 ? Math.floor(a / b) : b < 0 ? -Math.floor(a / -b) : 0;
export const TestInt64$neg = (a) => -a;

// ---------------- TestISize ----------------

export const TestISize$add = (a) => (b) => a + b;
export const TestISize$sub = (a) => (b) => a - b;
export const TestISize$eq = (a) => (b) => a === b;
export const TestISize$ne = (a) => (b) => a !== b;
export const TestISize$lt = (a) => (b) => a < b;
export const TestISize$gt = (a) => (b) => a > b;
export const TestISize$le = (a) => (b) => a <= b;
export const TestISize$ge = (a) => (b) => a >= b;
export const TestISize$mul = (a) => (b) => a * b;
export const TestISize$div = (a) => (b) =>
  b > 0 ? Math.floor(a / b) : b < 0 ? -Math.floor(a / -b) : 0;
export const TestISize$neg = (a) => -a;

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
  b > 0 ? Math.floor(a / b) : b < 0 ? -Math.floor(a / -b) : 0;
export const TestInt$neg = (a) => -a;
