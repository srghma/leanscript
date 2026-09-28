// The runtime functions that answer with a `Nat`, where a `Nat` is a `BigInt`
// (`natRepr = bigint`).
//
// A `BigInt` is exact at every size, which is Lean's own semantics for `Nat`;
// `lean_runtime_nat_num.mjs` beside this file is the same catalogue over JavaScript
// numbers.  A compiled module imports one of the two, never both.

const $bigPow = (a, b) => {
  let r = 1n;
  let x = a;
  let e = b;
  while (e > 0n) {
    if ((e & 1n) === 1n) {
      r = r * x;
    }
    e = e >> 1n;
    if (e > 0n) {
      x = x * x;
    }
  }
  return r;
};

const $utf8 = (s) => {
  return new TextEncoder().encode(s);
};

/* ----------------------------------------------------- imported by the backend */

/** `Array.size`. */
export const $lean_array_get_size = (a) => BigInt(a.length);

/** `Int.natAbs`. */
export const $lean_nat_abs = (a) => {
  a = BigInt(a);
  return a < 0n ? -a : a;
};

/** `Nat.add`. */
export const $lean_nat_add = (a, b) => a + b;

/** `Nat.div`. */
export const $lean_nat_div = (a, b) => b === 0n ? 0n : a / b;

/** `Nat.divExact`. */
export const $lean_nat_div_exact = (a, b) => b === 0n ? 0n : a / b;

/** `Nat.land`. */
export const $lean_nat_land = (a, b) => a & b;

/** `Nat.log2`. */
export const $lean_nat_log2 = (a) => a === 0n ? 0n : BigInt(a.toString(2).length - 1);

/** `Nat.lor`. */
export const $lean_nat_lor = (a, b) => a | b;

/** `Nat.xor`. */
export const $lean_nat_lxor = (a, b) => a ^ b;

/** `Nat.modCore`, `Nat.mod`. */
export const $lean_nat_mod = (a, b) => b === 0n ? a : a % b;

/** `Nat.mul`. */
export const $lean_nat_mul = (a, b) => a * b;

/** `Nat.pow`. */
export const $lean_nat_pow = (a, b) => $bigPow(a, b);

/** `Nat.pred`. */
export const $lean_nat_pred = (a) => a > 0n ? a - 1n : 0n;

/** `Nat.shiftLeft`. */
export const $lean_nat_shiftl = (a, b) => a << b;

/** `Nat.shiftRight`. */
export const $lean_nat_shiftr = (a, b) => a >> b;

/** `Nat.sub`. */
export const $lean_nat_sub = (a, b) => a > b ? a - b : 0n;

/** `String.Internal.length`, `String.length`. */
export const $lean_string_length = (a) => BigInt([...a].length);

/** `String.utf8ByteSize`. */
export const $lean_string_utf8_byte_size = (a) => BigInt($utf8(a).length);

/** `UInt16.toNat`. */
export const $lean_uint16_to_nat = (a) => BigInt(a);

/** `UInt32.toNat`. */
export const $lean_uint32_to_nat = (a) => BigInt(a);

/** `UInt64.toNat`. */
export const $lean_uint64_to_nat = (a) => BigInt(a);

/** `UInt8.toNat`. */
export const $lean_uint8_to_nat = (a) => BigInt(a);

/* -------------------------------------- not imported by the current backend */

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

/** `Nat.modCore`. */
export const $lean_nat_mod_core = (a, b) => (b === 0n ? a : a % b);

/** `BitVec.toNat`: the value of a bit vector, read as a `Nat`. */
export const BitVec_toNat = (_w, a) => BigInt(a);
