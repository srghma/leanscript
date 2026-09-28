// The runtime functions that answer with a `Nat`, where a `Nat` is a `BigInt`
// (`natRepr = bigint`).
//
// A `BigInt` is exact at every size, which is Lean's own semantics for `Nat`;
// `lean_runtime_nat_num.mjs` beside this file is the same catalogue over JavaScript
// numbers.  A compiled module imports one of the two, never both.

/** `Nat.gcd`. */
export const $lean_nat_gcd = (a, b) => {
  let x = a < 0n ? -a : a;
  let y = b < 0n ? -b : b;
  while (y !== 0n) {
    const t = x % y;
    x = y;
    y = t;
  }
  return x;
};

/** `Nat.div`: rounds down, and `n / 0` is `0`. */
export const $lean_nat_div = (a, b) => (b === 0n ? 0n : a / b);

/** `Nat.mod`; `n % 0` is `n`. */
export const $lean_nat_mod = (a, b) => (b === 0n ? a : a % b);

/** `Nat.modCore`. */
export const $lean_nat_mod_core = (a, b) => (b === 0n ? a : a % b);

/** `Nat.sub`, which truncates at zero. */
export const $lean_nat_sub = (a, b) => (a >= b ? a - b : 0n);

/** `Nat.land`. */
export const $lean_nat_land = (a, b) => a & b;

/** `Nat.lor`. */
export const $lean_nat_lor = (a, b) => a | b;

/** `Nat.xor`. */
export const $lean_nat_lxor = (a, b) => a ^ b;

/** `Nat.shiftLeft`, which does not wrap: a `Nat` has no width. */
export const $lean_nat_shiftl = (a, b) => a << b;

/** `Nat.shiftRight`. */
export const $lean_nat_shiftr = (a, b) => a >> b;

/** `String.utf8ByteSize`, which answers with a `Nat`. */
export const $lean_string_utf8_byte_size = (s) => {
  let n = 0n;
  for (const ch of s) {
    const cp = ch.codePointAt(0);
    n += cp < 0x80 ? 1n : cp < 0x800 ? 2n : cp < 0x10000 ? 3n : 4n;
  }
  return n;
};

/** `BitVec.toNat`: the value of a bit vector, read as a `Nat`. */
export const BitVec_toNat = (_w, a) => BigInt(a);
