// The runtime functions that answer with a `Nat`, where a `Nat` is a JavaScript
// number (`natRepr = num`).
//
// A number holds an integer exactly up to `2^53`, so this is the fast representation
// and the inexact one; `lean_runtime_nat_bigint.mjs` beside this file is the same
// catalogue over `BigInt`s, which is exact at every size.  A compiled module imports
// one of the two, never both: the two are different JavaScript types, and mixing them
// in an arithmetic operator throws.

const $chk53 = (x) => {
  if (!Number.isSafeInteger(x)) {
    throw new RangeError(
      "LeanScript: integer overflow: the result does not fit in a number (use the bigint representation)",
    );
  }
  return x;
};

const $utf8 = (s) => {
  return new TextEncoder().encode(s);
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

/** `Array.size`. */
export const $lean_array_get_size = (a) => a.length;

/** `Int.natAbs`. */
export const $lean_nat_abs = (a) =>
  typeof a === "bigint" ? $toNum53(a < 0n ? -a : a) : a < 0 ? -a : a;

/** `Nat.add`. */
export const $lean_nat_add = (a, b) => $chk53(a + b);

/** `Nat.div`. */
export const $lean_nat_div = (a, b) => b === 0 ? 0 : Math.floor(a / b);

/** `Nat.divExact`. */
export const $lean_nat_div_exact = (a, b) => b === 0 ? 0 : Math.floor(a / b);

/** `Nat.land`. */
export const $lean_nat_land = (a, b) => Number(BigInt(a) & BigInt(b));

/** `Nat.log2`. */
export const $lean_nat_log2 = (a) => a === 0 ? 0 : a.toString(2).length - 1;

/** `Nat.lor`. */
export const $lean_nat_lor = (a, b) => Number(BigInt(a) | BigInt(b));

/** `Nat.xor`. */
export const $lean_nat_lxor = (a, b) => Number(BigInt(a) ^ BigInt(b));

/** `Nat.modCore`, `Nat.mod`. */
export const $lean_nat_mod = (a, b) => b === 0 ? a : a % b;

/** `Nat.mul`. */
export const $lean_nat_mul = (a, b) => $chk53(a * b);

/** `Nat.pow`. */
export const $lean_nat_pow = (a, b) => $chk53(Math.pow(a, b));

/** `Nat.pred`. */
export const $lean_nat_pred = (a) => a > 0 ? a - 1 : 0;

/** `Nat.shiftLeft`. */
export const $lean_nat_shiftl = (a, b) => $chk53(a * Math.pow(2, b));

/** `Nat.shiftRight`. */
export const $lean_nat_shiftr = (a, b) => Math.floor(a / Math.pow(2, b));

/** `Nat.sub`. */
export const $lean_nat_sub = (a, b) => a > b ? a - b : 0;

/** `String.Internal.length`, `String.length`. */
export const $lean_string_length = (a) => [...a].length;

/** `String.utf8ByteSize`. */
export const $lean_string_utf8_byte_size = (a) => $utf8(a).length;

/** `UInt16.toNat`. */
export const $lean_uint16_to_nat = (a) => a;

/** `UInt32.toNat`. */
export const $lean_uint32_to_nat = (a) => a;

/** `UInt64.toNat`: the argument may be a `BigInt` or a number. */
export const $lean_uint64_to_nat = (a) => (typeof a === "bigint" ? $toNum53(a) : a);

/** `UInt8.toNat`. */
export const $lean_uint8_to_nat = (a) => a;

/* -------------------------------------- not imported by the current backend */

/** `Nat.gcd`. */
export const $lean_nat_gcd = (a, b) => {
  let x = a < 0 ? -a : a;
  let y = b < 0 ? -b : b;
  while (y !== 0) {
    const t = x % y;
    x = y;
    y = t;
  }
  return x;
};

/** `Nat.modCore`. */
export const $lean_nat_mod_core = (a, b) => (b === 0 ? a : a % b);

/** `BitVec.toNat`: the value of a bit vector, read as a `Nat`. */
export const BitVec_toNat = (_w, a) => Number(a);
