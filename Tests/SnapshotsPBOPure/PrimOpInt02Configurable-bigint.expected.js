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
//
// In `PrimOpInt02`, `intValues` is marked `@[inline]` and evaluated at compile time,
// so all static applications of primitive operations in `test1`–`test11` are fully
// inlined and computed.

// ---------------- TestUInt64 ----------------

export const TestUInt64$intValues = (op) => [
  op(1n)(1n),
  op(1n)(2n),
  op(2n)(1n),
  op(1n)(18446744073709551614n),
  op(18446744073709551615n)(2n),
  op(18446744073709551615n)(18446744073709551615n),
];

export const TestUInt64$test1 = [2n, 3n, 3n, 18446744073709551615n, 1n, 18446744073709551614n];
export const TestUInt64$test2 = [0n, 18446744073709551615n, 1n, 3n, 18446744073709551613n, 0n];
export const TestUInt64$test3 = [true, false, false, false, false, true];
export const TestUInt64$test4 = [false, true, true, true, true, false];
export const TestUInt64$test5 = [false, true, false, true, false, false];
export const TestUInt64$test6 = [false, false, true, false, true, false];
export const TestUInt64$test7 = [true, true, false, true, false, true];
export const TestUInt64$test8 = [true, false, true, false, true, true];
export const TestUInt64$test9 = [1n, 2n, 2n, 18446744073709551614n, 18446744073709551614n, 1n];
export const TestUInt64$test10 = [1n, 0n, 2n, 0n, 9223372036854775807n, 1n];
export const TestUInt64$test11 = [18446744073709551615n, 1n];

// ---------------- TestUSize ----------------

export const TestUSize$intValues = (op) => [
  op(1n)(1n),
  op(1n)(2n),
  op(2n)(1n),
  op(1n)(18446744073709551614n),
  op(18446744073709551615n)(2n),
  op(18446744073709551615n)(18446744073709551615n),
];

export const TestUSize$test1 = [2n, 3n, 3n, 18446744073709551615n, 1n, 18446744073709551614n];
export const TestUSize$test2 = [0n, 18446744073709551615n, 1n, 3n, 18446744073709551613n, 0n];
export const TestUSize$test3 = [true, false, false, false, false, true];
export const TestUSize$test4 = [false, true, true, true, true, false];
export const TestUSize$test5 = [false, true, false, true, false, false];
export const TestUSize$test6 = [false, false, true, false, true, false];
export const TestUSize$test7 = [true, true, false, true, false, true];
export const TestUSize$test8 = [true, false, true, false, true, true];
export const TestUSize$test9 = [1n, 2n, 2n, 18446744073709551614n, 18446744073709551614n, 1n];
export const TestUSize$test10 = [1n, 0n, 2n, 0n, 9223372036854775807n, 1n];
export const TestUSize$test11 = [18446744073709551615n, 1n];

// ---------------- TestNat ----------------

export const TestNat$intValues = (op) => [
  op(1n)(1n),
  op(1n)(2n),
  op(2n)(1n),
  op(1n)(0n),
  op(0n)(2n),
  op(0n)(0n),
];

export const TestNat$test1 = [2n, 3n, 3n, 1n, 2n, 0n];
export const TestNat$test2 = [0n, 0n, 1n, 1n, 0n, 0n];
export const TestNat$test3 = [true, false, false, false, false, true];
export const TestNat$test4 = [false, true, true, true, true, false];
export const TestNat$test5 = [false, true, false, false, true, false];
export const TestNat$test6 = [false, false, true, true, false, false];
export const TestNat$test7 = [true, true, false, false, true, true];
export const TestNat$test8 = [true, false, true, true, false, true];
export const TestNat$test9 = [1n, 2n, 2n, 0n, 0n, 0n];
export const TestNat$test10 = [1n, 0n, 2n, 0n, 0n, 0n];
// Nat does not support negation

// ---------------- TestInt64 ----------------

export const TestInt64$intValues = (op) => [
  op(1n)(1n),
  op(1n)(2n),
  op(2n)(1n),
  op(1n)(-2n),
  op(-1n)(2n),
  op(-1n)(-1n),
];

export const TestInt64$test1 = [2n, 3n, 3n, -1n, 1n, -2n];
export const TestInt64$test2 = [0n, -1n, 1n, 3n, -3n, 0n];
export const TestInt64$test3 = [true, false, false, false, false, true];
export const TestInt64$test4 = [false, true, true, true, true, false];
export const TestInt64$test5 = [false, true, false, false, true, false];
export const TestInt64$test6 = [false, false, true, true, false, false];
export const TestInt64$test7 = [true, true, false, false, true, true];
export const TestInt64$test8 = [true, false, true, true, false, true];
export const TestInt64$test9 = [1n, 2n, 2n, -2n, -2n, 1n];
export const TestInt64$test10 = [1n, 0n, 2n, 0n, -1n, 1n];
export const TestInt64$test11 = [-1n, 1n];

// ---------------- TestISize ----------------

export const TestISize$intValues = (op) => [
  op(1n)(1n),
  op(1n)(2n),
  op(2n)(1n),
  op(1n)(-2n),
  op(-1n)(2n),
  op(-1n)(-1n),
];

export const TestISize$test1 = [2n, 3n, 3n, -1n, 1n, -2n];
export const TestISize$test2 = [0n, -1n, 1n, 3n, -3n, 0n];
export const TestISize$test3 = [true, false, false, false, false, true];
export const TestISize$test4 = [false, true, true, true, true, false];
export const TestISize$test5 = [false, true, false, false, true, false];
export const TestISize$test6 = [false, false, true, true, false, false];
export const TestISize$test7 = [true, true, false, false, true, true];
export const TestISize$test8 = [true, false, true, true, false, true];
export const TestISize$test9 = [1n, 2n, 2n, -2n, -2n, 1n];
export const TestISize$test10 = [1n, 0n, 2n, 0n, -1n, 1n];
export const TestISize$test11 = [-1n, 1n];

// ---------------- TestInt ----------------

export const TestInt$intValues = (op) => [
  op(1n)(1n),
  op(1n)(2n),
  op(2n)(1n),
  op(1n)(-2n),
  op(-1n)(2n),
  op(-1n)(-1n),
];

export const TestInt$test1 = [2n, 3n, 3n, -1n, 1n, -2n];
export const TestInt$test2 = [0n, -1n, 1n, 3n, -3n, 0n];
export const TestInt$test3 = [true, false, false, false, false, true];
export const TestInt$test4 = [false, true, true, true, true, false];
export const TestInt$test5 = [false, true, false, false, true, false];
export const TestInt$test6 = [false, false, true, true, false, false];
export const TestInt$test7 = [true, true, false, false, true, true];
export const TestInt$test8 = [true, false, true, true, false, true];
export const TestInt$test9 = [1n, 2n, 2n, -2n, -2n, 1n];
export const TestInt$test10 = [1n, 0n, 2n, 0n, -1n, 1n];
export const TestInt$test11 = [-1n, 1n];
