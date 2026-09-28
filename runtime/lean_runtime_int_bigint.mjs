// The runtime functions that answer with an `Int`, where an `Int` is a `BigInt`
// (`intRepr = bigint`).  `lean_runtime_int_num.mjs` is the same catalogue over
// JavaScript numbers.

/* ----------------------------------------------------- imported by the backend */

/** `Int16.toInt`. */
export const $lean_int16_to_int = (a) => BigInt(a);

/** `Int32.toInt`. */
export const $lean_int32_to_int = (a) => BigInt(a);

/** `Int64.toInt`. */
export const $lean_int64_to_int_sint = (a) => BigInt(a);

/** `Int8.toInt`. */
export const $lean_int8_to_int = (a) => BigInt(a);

/** `Int.add`. */
export const $lean_int_add = (a, b) => a + b;

/** `Int.tdiv`. */
export const $lean_int_div = (a, b) => b === 0n ? 0n : a / b;

/** `Int.divExact`. */
export const $lean_int_div_exact = (a, b) =>
  b === 0n
  ? 0n
  : a % b < 0n
    ? b > 0n
      ? a / b - 1n
      : a / b + 1n
    : a / b;

/** `Int.ediv`. */
export const $lean_int_ediv = (a, b) =>
  b === 0n
  ? 0n
  : a % b < 0n
    ? b > 0n
      ? a / b - 1n
      : a / b + 1n
    : a / b;

/** `Int.emod`. */
export const $lean_int_emod = (a, b) => b === 0n ? a : ((a % b) + (b < 0n ? -b : b)) % (b < 0n ? -b : b);

/** `Int.tmod`. */
export const $lean_int_mod = (a, b) => b === 0n ? a : a % b;

/** `Int.mul`. */
export const $lean_int_mul = (a, b) => a * b;

/** `Int.neg`. */
export const $lean_int_neg = (a) => -a;

/** `Int.negSucc`. */
export const $lean_int_neg_succ_of_nat = (a) => -BigInt(a) - 1n;

/** `Int.sub`. */
export const $lean_int_sub = (a, b) => a - b;

/** `Int.ofNat`. */
export const $lean_nat_to_int = (a) => BigInt(a);

/* -------------------------------------- not imported by the current backend */

/** `Int.not`, the complement of an unbounded integer: `~~~a` is `-a - 1`. */
export const Int_not = (a) => -a - 1n;
