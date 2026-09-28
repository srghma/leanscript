// The runtime functions that answer with an `Int`, where an `Int` is a JavaScript
// number (`intRepr = num`).  `lean_runtime_int_bigint.mjs` is the same catalogue over
// `BigInt`s.

const $chk53 = (x) => {
  if (!Number.isSafeInteger(x)) {
    throw new RangeError(
      "LeanScript: integer overflow: the result does not fit in a number (use the bigint representation)",
    );
  }
  return x;
};

const $toNum53 = (x) => {
  if (x > 9007199254740991n || x < -9007199254740991n) {
    throw new RangeError(
      "LeanScript: integer overflow: the result does not fit in a number (use the bigint representation)",
    );
  }
  return Number(x);
};

/* ----------------------------------------------------- imported by the backend */

/** `Int16.toInt`. */
export const $lean_int16_to_int = (a) => a;

/** `Int32.toInt`. */
export const $lean_int32_to_int = (a) => a;

/** `Int64.toInt`: the argument may be a `BigInt` or a number. */
export const $lean_int64_to_int_sint = (a) => (typeof a === "bigint" ? $toNum53(a) : a);

/** `Int8.toInt`. */
export const $lean_int8_to_int = (a) => a;

/** `Int.add`. */
export const $lean_int_add = (a, b) => $chk53(a + b);

/** `Int.tdiv`. */
export const $lean_int_div = (a, b) => b === 0 ? 0 : Math.trunc(a / b);

/** `Int.divExact`. */
export const $lean_int_div_exact = (a, b) =>
  b === 0
  ? 0
  : a % b < 0
    ? b > 0
      ? Math.trunc(a / b) - 1
      : Math.trunc(a / b) + 1
    : Math.trunc(a / b);

/** `Int.ediv`. */
export const $lean_int_ediv = (a, b) =>
  b === 0
  ? 0
  : a % b < 0
    ? b > 0
      ? Math.trunc(a / b) - 1
      : Math.trunc(a / b) + 1
    : Math.trunc(a / b);

/** `Int.emod`. */
export const $lean_int_emod = (a, b) => b === 0 ? a : ((a % b) + Math.abs(b)) % Math.abs(b);

/** `Int.tmod`. */
export const $lean_int_mod = (a, b) => b === 0 ? a : a % b;

/** `Int.mul`. */
export const $lean_int_mul = (a, b) => $chk53(a * b);

/** `Int.neg`. */
export const $lean_int_neg = (a) => 0 - a;

/** `Int.negSucc`. */
export const $lean_int_neg_succ_of_nat = (a) =>
  typeof a === "bigint" ? $toNum53(-a - 1n) : -a - 1;

/** `Int.sub`. */
export const $lean_int_sub = (a, b) => $chk53(a - b);

/** `Int.ofNat`: the argument may be a `BigInt` or a number. */
export const $lean_nat_to_int = (a) => (typeof a === "bigint" ? $toNum53(a) : a);

/* -------------------------------------- not imported by the current backend */

/** `Int.not`, the complement of an unbounded integer: `~~~a` is `-a - 1`. */
export const Int_not = (a) => -a - 1;
