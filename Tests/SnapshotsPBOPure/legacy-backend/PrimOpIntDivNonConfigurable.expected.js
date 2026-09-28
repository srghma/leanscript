// UInt8, UInt16, UInt32, Int8, Int16, Int32 are always representable exactly as a
// JS Number (max magnitude 2^32 < Number.MAX_SAFE_INTEGER = 2^53 - 1), so there is
// only one output mode for these — no BigInt needed, ever.
//
// In `PrimOpIntDiv`, `test` is `@[inline]` and folds the static division `a / b`
// and comparison with `expectedResult`, while `divNoInline` is `@[noinline]`.

export const test = (divNoInline) => (a) => (b) => (expectedResult) =>
  (b !== 0 ? Math.floor(a / b) : 0) === divNoInline(a)(b) &&
  (b !== 0 ? Math.floor(a / b) : 0) === expectedResult;

// ---------------- TestUInt8 ----------------

export const TestUInt8$divNoInline = (a) => (b) => (b !== 0 ? Math.floor(a / b) : 0);
export const TestUInt8$test1_0 = TestUInt8$divNoInline(1)(0) === 0;
export const TestUInt8$test3_2 = TestUInt8$divNoInline(3)(2) === 1;
export const TestUInt8$test3m2 = TestUInt8$divNoInline(3)(254) === 0;

// ---------------- TestUInt16 ----------------

export const TestUInt16$divNoInline = (a) => (b) => (b !== 0 ? Math.floor(a / b) : 0);
export const TestUInt16$test1_0 = TestUInt16$divNoInline(1)(0) === 0;
export const TestUInt16$test3_2 = TestUInt16$divNoInline(3)(2) === 1;
export const TestUInt16$test3m2 = TestUInt16$divNoInline(3)(65534) === 0;

// ---------------- TestUInt32 ----------------

export const TestUInt32$divNoInline = (a) => (b) => (b !== 0 ? Math.floor(a / b) : 0);
export const TestUInt32$test1_0 = TestUInt32$divNoInline(1)(0) === 0;
export const TestUInt32$test3_2 = TestUInt32$divNoInline(3)(2) === 1;
export const TestUInt32$test3m2 = TestUInt32$divNoInline(3)(4294967294) === 0;

// ---------------- TestInt8 ----------------

export const TestInt8$divNoInline = (a) => (b) =>
  (((b > 0 ? Math.floor(a / b) : b < 0 ? -Math.floor(a / -b) : 0) << 24) >> 24);
export const TestInt8$test1_0 = TestInt8$divNoInline(1)(0) === 0;
export const TestInt8$test3_2 = TestInt8$divNoInline(3)(2) === 1;
export const TestInt8$test3m2 = TestInt8$divNoInline(3)(-2) === -1;

// ---------------- TestInt16 ----------------

export const TestInt16$divNoInline = (a) => (b) =>
  (((b > 0 ? Math.floor(a / b) : b < 0 ? -Math.floor(a / -b) : 0) << 16) >> 16);
export const TestInt16$test1_0 = TestInt16$divNoInline(1)(0) === 0;
export const TestInt16$test3_2 = TestInt16$divNoInline(3)(2) === 1;
export const TestInt16$test3m2 = TestInt16$divNoInline(3)(-2) === -1;

// ---------------- TestInt32 ----------------

export const TestInt32$divNoInline = (a) => (b) =>
  b > 0 ? Math.floor(a / b) : b < 0 ? -Math.floor(a / -b) : 0;
export const TestInt32$test1_0 = TestInt32$divNoInline(1)(0) === 0;
export const TestInt32$test3_2 = TestInt32$divNoInline(3)(2) === 1;
export const TestInt32$test3m2 = TestInt32$divNoInline(3)(-2) === -1;
