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
//
// In `PrimOpInt02`, `intValues` is marked `@[inline]` and evaluated at compile time,
// so all static applications of primitive operations in `test1`–`test11` are fully
// inlined and computed.

// ---------------- TestUInt64 ----------------

export const TestUInt64$intValues = (op) => [
  op(1)(1),
  op(1)(2),
  op(2)(1),
  op(1)(-2),
  op(-1)(2),
  op(-1)(-1),
];

export const TestUInt64$test1 = [2, 3, 3, -1, 1, -2];
export const TestUInt64$test2 = [0, -1, 1, 3, -3, 0];
export const TestUInt64$test3 = [true, false, false, false, false, true];
export const TestUInt64$test4 = [false, true, true, true, true, false];
export const TestUInt64$test5 = [false, true, false, false, true, false];
export const TestUInt64$test6 = [false, false, true, true, false, false];
export const TestUInt64$test7 = [true, true, false, false, true, true];
export const TestUInt64$test8 = [true, false, true, true, false, true];
export const TestUInt64$test9 = [1, 2, 2, -2, -2, 1];
export const TestUInt64$test10 = [1, 0, 2, -1, -1, 1];
export const TestUInt64$test11 = [-1, 1];

// ---------------- TestUSize ----------------

export const TestUSize$intValues = (op) => [
  op(1)(1),
  op(1)(2),
  op(2)(1),
  op(1)(-2),
  op(-1)(2),
  op(-1)(-1),
];

export const TestUSize$test1 = [2, 3, 3, -1, 1, -2];
export const TestUSize$test2 = [0, -1, 1, 3, -3, 0];
export const TestUSize$test3 = [true, false, false, false, false, true];
export const TestUSize$test4 = [false, true, true, true, true, false];
export const TestUSize$test5 = [false, true, false, false, true, false];
export const TestUSize$test6 = [false, false, true, true, false, false];
export const TestUSize$test7 = [true, true, false, false, true, true];
export const TestUSize$test8 = [true, false, true, true, false, true];
export const TestUSize$test9 = [1, 2, 2, -2, -2, 1];
export const TestUSize$test10 = [1, 0, 2, -1, -1, 1];
export const TestUSize$test11 = [-1, 1];

// ---------------- TestNat ----------------

export const TestNat$intValues = (op) => [
  op(1)(1),
  op(1)(2),
  op(2)(1),
  op(1)(0),
  op(0)(2),
  op(0)(0),
];

export const TestNat$test1 = [2, 3, 3, 1, 2, 0];
export const TestNat$test2 = [0, 0, 1, 1, 0, 0];
export const TestNat$test3 = [true, false, false, false, false, true];
export const TestNat$test4 = [false, true, true, true, true, false];
export const TestNat$test5 = [false, true, false, false, true, false];
export const TestNat$test6 = [false, false, true, true, false, false];
export const TestNat$test7 = [true, true, false, false, true, true];
export const TestNat$test8 = [true, false, true, true, false, true];
export const TestNat$test9 = [1, 2, 2, 0, 0, 0];
export const TestNat$test10 = [1, 0, 2, 0, 0, 0];
// Nat does not support negation

// ---------------- TestInt64 ----------------

export const TestInt64$intValues = (op) => [
  op(1)(1),
  op(1)(2),
  op(2)(1),
  op(1)(-2),
  op(-1)(2),
  op(-1)(-1),
];

export const TestInt64$test1 = [2, 3, 3, -1, 1, -2];
export const TestInt64$test2 = [0, -1, 1, 3, -3, 0];
export const TestInt64$test3 = [true, false, false, false, false, true];
export const TestInt64$test4 = [false, true, true, true, true, false];
export const TestInt64$test5 = [false, true, false, false, true, false];
export const TestInt64$test6 = [false, false, true, true, false, false];
export const TestInt64$test7 = [true, true, false, false, true, true];
export const TestInt64$test8 = [true, false, true, true, false, true];
export const TestInt64$test9 = [1, 2, 2, -2, -2, 1];
export const TestInt64$test10 = [1, 0, 2, 0, -1, 1];
export const TestInt64$test11 = [-1, 1];

// ---------------- TestISize ----------------

export const TestISize$intValues = (op) => [
  op(1)(1),
  op(1)(2),
  op(2)(1),
  op(1)(-2),
  op(-1)(2),
  op(-1)(-1),
];

export const TestISize$test1 = [2, 3, 3, -1, 1, -2];
export const TestISize$test2 = [0, -1, 1, 3, -3, 0];
export const TestISize$test3 = [true, false, false, false, false, true];
export const TestISize$test4 = [false, true, true, true, true, false];
export const TestISize$test5 = [false, true, false, false, true, false];
export const TestISize$test6 = [false, false, true, true, false, false];
export const TestISize$test7 = [true, true, false, false, true, true];
export const TestISize$test8 = [true, false, true, true, false, true];
export const TestISize$test9 = [1, 2, 2, -2, -2, 1];
export const TestISize$test10 = [1, 0, 2, 0, -1, 1];
export const TestISize$test11 = [-1, 1];

// ---------------- TestInt ----------------

export const TestInt$intValues = (op) => [
  op(1)(1),
  op(1)(2),
  op(2)(1),
  op(1)(-2),
  op(-1)(2),
  op(-1)(-1),
];

export const TestInt$test1 = [2, 3, 3, -1, 1, -2];
export const TestInt$test2 = [0, -1, 1, 3, -3, 0];
export const TestInt$test3 = [true, false, false, false, false, true];
export const TestInt$test4 = [false, true, true, true, true, false];
export const TestInt$test5 = [false, true, false, false, true, false];
export const TestInt$test6 = [false, false, true, true, false, false];
export const TestInt$test7 = [true, true, false, false, true, true];
export const TestInt$test8 = [true, false, true, true, false, true];
export const TestInt$test9 = [1, 2, 2, -2, -2, 1];
export const TestInt$test10 = [1, 0, 2, 0, -1, 1];
export const TestInt$test11 = [-1, 1];
