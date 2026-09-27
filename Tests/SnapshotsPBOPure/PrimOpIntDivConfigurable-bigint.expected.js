// UInt64, USize, Nat, Int64, ISize, Int in this file are configured with
// `*Repr = "bignum"` (natRepr/intRepr/usizeRepr/uint64Repr/int64Repr = "bignum").
// All values are represented as native JavaScript BigInts (arbitrary precision).

export const test = (divNoInline) => (a) => (b) => (expectedResult) =>
  (b !== 0n ? a / b : 0n) === divNoInline(a)(b) &&
  (b !== 0n ? a / b : 0n) === expectedResult;

// ---------------- TestUInt64 ----------------

export const TestUInt64$divNoInline = (a) => (b) => (b !== 0n ? a / b : 0n);
export const TestUInt64$test1_0 = TestUInt64$divNoInline(1n)(0n) === 0n;
export const TestUInt64$test3_2 = TestUInt64$divNoInline(3n)(2n) === 1n;
export const TestUInt64$test3m2 = TestUInt64$divNoInline(3n)(18446744073709551614n) === 0n;

// ---------------- TestUSize ----------------

export const TestUSize$divNoInline = (a) => (b) => (b !== 0n ? a / b : 0n);
export const TestUSize$test1_0 = TestUSize$divNoInline(1n)(0n) === 0n;
export const TestUSize$test3_2 = TestUSize$divNoInline(3n)(2n) === 1n;
export const TestUSize$test3m2 = TestUSize$divNoInline(3n)(18446744073709551614n) === 0n;

// ---------------- TestNat ----------------

export const TestNat$divNoInline = (a) => (b) => (b !== 0n ? a / b : 0n);
export const TestNat$test1_0 = TestNat$divNoInline(1n)(0n) === 0n;
export const TestNat$test3_2 = TestNat$divNoInline(3n)(2n) === 1n;
// Nat does not support negation

// ---------------- TestInt64 ----------------

export const TestInt64$divNoInline = (a) => (b) =>
  b !== 0n
    ? BigInt.asIntN(64, a < 0n && a % b !== 0n ? (b > 0n ? a / b - 1n : a / b + 1n) : a / b)
    : 0n;
export const TestInt64$test1_0 = TestInt64$divNoInline(1n)(0n) === 0n;
export const TestInt64$test3_2 = TestInt64$divNoInline(3n)(2n) === 1n;
export const TestInt64$test3m2 = TestInt64$divNoInline(3n)(-2n) === -1n;

// ---------------- TestISize ----------------

export const TestISize$divNoInline = (a) => (b) =>
  b !== 0n
    ? BigInt.asIntN(64, a < 0n && a % b !== 0n ? (b > 0n ? a / b - 1n : a / b + 1n) : a / b)
    : 0n;
export const TestISize$test1_0 = TestISize$divNoInline(1n)(0n) === 0n;
export const TestISize$test3_2 = TestISize$divNoInline(3n)(2n) === 1n;
export const TestISize$test3m2 = TestISize$divNoInline(3n)(-2n) === -1n;

// ---------------- TestInt ----------------

export const TestInt$divNoInline = (a) => (b) =>
  b !== 0n ? (a < 0n && a % b !== 0n ? (b > 0n ? a / b - 1n : a / b + 1n) : a / b) : 0n;
export const TestInt$test1_0 = TestInt$divNoInline(1n)(0n) === 0n;
export const TestInt$test3_2 = TestInt$divNoInline(3n)(2n) === 1n;
export const TestInt$test3m2 = TestInt$divNoInline(3n)(-2n) === -1n;
