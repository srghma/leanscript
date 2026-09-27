// UInt64, USize, Nat, Int64, ISize, Int in this file are configured with
// `*Repr = "num"` (natRepr/intRepr/usizeRepr/uint64Repr/int64Repr = "num").
// All values are represented as plain JS Numbers (IEEE-754 double-precision floats,
// safe up to Number.MAX_SAFE_INTEGER = 2^53 - 1).

// ---------------- TestUInt64 ----------------

export const TestUInt64$test1 = 20000000000000000000;
export const TestUInt64$test2 = -9000000000000000000;
export const TestUInt64$test3 = 25000000000000000000;
export const TestUInt64$test4 = (a) => a + 20000000000000000000;

// ---------------- TestUSize ----------------

export const TestUSize$test1 = 20000000000000000000;
export const TestUSize$test2 = -9000000000000000000;
export const TestUSize$test3 = 25000000000000000000;
export const TestUSize$test4 = (a) => a + 20000000000000000000;

// ---------------- TestNat ----------------

export const TestNat$test1 = 4000000000;
export const TestNat$test2 = 0; // Math.max(0, 1000000000 - 2000000000)
export const TestNat$test3 = 4000000000000000000;
export const TestNat$test4 = (a) => a + 4000000000;

// ---------------- TestInt64 ----------------

export const TestInt64$test1 = 10000000000000000000;
export const TestInt64$test2 = -10000000000000000000;
export const TestInt64$test3 = 25000000000000000000;
export const TestInt64$test4 = (a) => a + 10000000000000000000;

// ---------------- TestISize ----------------

export const TestISize$test1 = 10000000000000000000;
export const TestISize$test2 = -10000000000000000000;
export const TestISize$test3 = 25000000000000000000;
export const TestISize$test4 = (a) => a + 10000000000000000000;

// ---------------- TestInt ----------------

export const TestInt$test1 = 4000000000;
export const TestInt$test2 = -4000000000;
export const TestInt$test3 = 4000000000000000000;
export const TestInt$test4 = (a) => a + 4000000000;
