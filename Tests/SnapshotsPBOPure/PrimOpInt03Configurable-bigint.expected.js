// UInt64, USize, Nat, Int64, ISize, Int in this file are configured with
// `*Repr = "bignum"` (natRepr/intRepr/usizeRepr/uint64Repr/int64Repr = "bignum").
// All values are represented as native JavaScript BigInts (arbitrary precision).

// ---------------- TestUInt64 ----------------

export const TestUInt64$test1 = 1553255926290448384n;  // BigInt.asUintN(64, 2 * 10^19)
export const TestUInt64$test2 = 9446744073709551616n;  // BigInt.asUintN(64, -9 * 10^18)
export const TestUInt64$test3 = 6553255926290448384n;  // BigInt.asUintN(64, 2.5 * 10^19)
export const TestUInt64$test4 = (a) => BigInt.asUintN(64, a + 1553255926290448384n);

// ---------------- TestUSize ----------------

export const TestUSize$test1 = 1553255926290448384n;
export const TestUSize$test2 = 9446744073709551616n;
export const TestUSize$test3 = 6553255926290448384n;
export const TestUSize$test4 = (a) => BigInt.asUintN(64, a + 1553255926290448384n);

// ---------------- TestNat ----------------

export const TestNat$test1 = 4000000000n;
export const TestNat$test2 = 0n; // Saturating subtraction
export const TestNat$test3 = 4000000000000000000n;
export const TestNat$test4 = (a) => a + 4000000000n;

// ---------------- TestInt64 ----------------

export const TestInt64$test1 = -8446744073709551616n; // BigInt.asIntN(64, 10^19)
export const TestInt64$test2 = 8446744073709551616n;  // BigInt.asIntN(64, -10^19)
export const TestInt64$test3 = 6553255926290448384n;  // BigInt.asIntN(64, 2.5 * 10^19)
export const TestInt64$test4 = (a) => BigInt.asIntN(64, a - 8446744073709551616n);

// ---------------- TestISize ----------------

export const TestISize$test1 = -8446744073709551616n;
export const TestISize$test2 = 8446744073709551616n;
export const TestISize$test3 = 6553255926290448384n;
export const TestISize$test4 = (a) => BigInt.asIntN(64, a - 8446744073709551616n);

// ---------------- TestInt ----------------

export const TestInt$test1 = 4000000000n;
export const TestInt$test2 = -4000000000n;
export const TestInt$test3 = 4000000000000000000n;
export const TestInt$test4 = (a) => a + 4000000000n;
