// The runtime functions that answer with a `Nat`, where a `Nat` is a JavaScript
// number (`natRepr = num`).
//
// A number holds an integer exactly up to `2^53`, so this is the fast representation
// and the inexact one; `lean_runtime_nat_bigint.mjs` beside this file is the same
// catalogue over `BigInt`s, which is exact at every size.  A compiled module imports
// one of the two, never both: the two are different JavaScript types, and mixing them
// in an arithmetic operator throws.

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

/** `Nat.div`: rounds down, and `n / 0` is `0`. */
export const $lean_nat_div = (a, b) => (b === 0 ? 0 : Math.floor(a / b));

/** `Nat.mod`; `n % 0` is `n`. */
export const $lean_nat_mod = (a, b) => (b === 0 ? a : a % b);

/** `Nat.modCore`. */
export const $lean_nat_mod_core = (a, b) => (b === 0 ? a : a % b);

/** `Nat.sub`, which truncates at zero. */
export const $lean_nat_sub = (a, b) => (a >= b ? a - b : 0);

/** `Nat.land`, over the full width, via `BigInt`. */
export const $lean_nat_land = (a, b) => Number(BigInt(a) & BigInt(b));

/** `Nat.lor`. */
export const $lean_nat_lor = (a, b) => Number(BigInt(a) | BigInt(b));

/** `Nat.xor`. */
export const $lean_nat_lxor = (a, b) => Number(BigInt(a) ^ BigInt(b));

/** `Nat.shiftLeft`, which does not wrap: a `Nat` has no width. */
export const $lean_nat_shiftl = (a, b) => Number(BigInt(a) << BigInt(b));

/** `Nat.shiftRight`. */
export const $lean_nat_shiftr = (a, b) => Number(BigInt(a) >> BigInt(b));

/** `String.utf8ByteSize`, which answers with a `Nat`. */
export const $lean_string_utf8_byte_size = (s) => {
  let n = 0;
  for (const ch of s) {
    const cp = ch.codePointAt(0);
    n += cp < 0x80 ? 1 : cp < 0x800 ? 2 : cp < 0x10000 ? 3 : 4;
  }
  return n;
};

/** `BitVec.toNat`: the value of a bit vector, read as a `Nat`. */
export const BitVec_toNat = (_w, a) => Number(a);
