// ---------------- TestFloat ----------------

export const TestFloat$test1 = (a) => (b) => a + b;
export const TestFloat$test2 = (a) => (b) => a - b;
export const TestFloat$test3 = (a) => (b) => a === b;
export const TestFloat$test4 = (a) => (b) => a !== b;
export const TestFloat$test5 = (a) => (b) => a < b;
export const TestFloat$test6 = (a) => (b) => a > b;
export const TestFloat$test7 = (a) => (b) => a <= b;
export const TestFloat$test8 = (a) => (b) => a >= b;
export const TestFloat$test9 = (a) => (b) => a * b;
export const TestFloat$test10 = (a) => (b) => a / b;
export const TestFloat$test11 = (a) => -a;
export const TestFloat$test12 = (a) => (b) => (c) => a - (b - c);
export const TestFloat$test13 = (a) => (b) => (c) => a / (b / c);

// ---------------- TestFloat32 ----------------

export const TestFloat32$test1 = (a) => (b) => Math.fround(a + b);
export const TestFloat32$test2 = (a) => (b) => Math.fround(a - b);
export const TestFloat32$test3 = (a) => (b) => a === b;
export const TestFloat32$test4 = (a) => (b) => a !== b;
export const TestFloat32$test5 = (a) => (b) => a < b;
export const TestFloat32$test6 = (a) => (b) => a > b;
export const TestFloat32$test7 = (a) => (b) => a <= b;
export const TestFloat32$test8 = (a) => (b) => a >= b;
export const TestFloat32$test9 = (a) => (b) => Math.fround(a * b);
export const TestFloat32$test10 = (a) => (b) => Math.fround(a / b);
export const TestFloat32$test11 = (a) => Math.fround(-a);
export const TestFloat32$test12 = (a) => (b) => (c) => Math.fround(a - Math.fround(b - c));
export const TestFloat32$test13 = (a) => (b) => (c) => Math.fround(a / Math.fround(b / c));
