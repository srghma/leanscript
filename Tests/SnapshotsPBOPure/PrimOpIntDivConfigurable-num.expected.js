// UInt64, USize, Nat, Int64, ISize, Int in this file are configured with
// `*Repr = "num"` (natRepr/intRepr/usizeRepr/uint64Repr/int64Repr = "num").
// All values are represented as plain JS Numbers.

export const test = (divNoInline) => (a) => (b) => (expectedResult) =>
  (b !== 0 ? Math.floor(a / b) : 0) === divNoInline(a)(b) &&
  (b !== 0 ? Math.floor(a / b) : 0) === expectedResult;

// ---------------- TestUInt64 ----------------

export const TestUInt64$divNoInline = (a) => (b) => (b !== 0 ? Math.floor(a / b) : 0);
export const TestUInt64$test1_0 = TestUInt64$divNoInline(1)(0) === 0;
export const TestUInt64$test3_2 = TestUInt64$divNoInline(3)(2) === 1;
export const TestUInt64$test3m2 = TestUInt64$divNoInline(3)(-2) === -2;

// ---------------- TestUSize ----------------

export const TestUSize$divNoInline = (a) => (b) => (b !== 0 ? Math.floor(a / b) : 0);
export const TestUSize$test1_0 = TestUSize$divNoInline(1)(0) === 0;
export const TestUSize$test3_2 = TestUSize$divNoInline(3)(2) === 1;
export const TestUSize$test3m2 = TestUSize$divNoInline(3)(-2) === -2;

// ---------------- TestNat ----------------

export const TestNat$divNoInline = (a) => (b) => (b !== 0 ? Math.floor(a / b) : 0);
export const TestNat$test1_0 = TestNat$divNoInline(1)(0) === 0;
export const TestNat$test3_2 = TestNat$divNoInline(3)(2) === 1;
// Nat does not support negation

// ---------------- TestInt64 ----------------

export const TestInt64$divNoInline = (a) => (b) =>
  b > 0 ? Math.floor(a / b) : b < 0 ? -Math.floor(a / -b) : 0;
export const TestInt64$test1_0 = TestInt64$divNoInline(1)(0) === 0;
export const TestInt64$test3_2 = TestInt64$divNoInline(3)(2) === 1;
export const TestInt64$test3m2 = TestInt64$divNoInline(3)(-2) === -1;

// ---------------- TestISize ----------------

export const TestISize$divNoInline = (a) => (b) =>
  b > 0 ? Math.floor(a / b) : b < 0 ? -Math.floor(a / -b) : 0;
export const TestISize$test1_0 = TestISize$divNoInline(1)(0) === 0;
export const TestISize$test3_2 = TestISize$divNoInline(3)(2) === 1;
export const TestISize$test3m2 = TestISize$divNoInline(3)(-2) === -1;

// ---------------- TestInt ----------------

export const TestInt$divNoInline = (a) => (b) =>
  b > 0 ? Math.floor(a / b) : b < 0 ? -Math.floor(a / -b) : 0;
export const TestInt$test1_0 = TestInt$divNoInline(1)(0) === 0;
export const TestInt$test3_2 = TestInt$divNoInline(3)(2) === 1;
export const TestInt$test3m2 = TestInt$divNoInline(3)(-2) === -1;
