// The runtime functions that answer with an `Int`, where an `Int` is a `BigInt`
// (`intRepr = bigint`).  `lean_runtime_int_num.mjs` is the same catalogue over
// JavaScript numbers.

/** `Int.ediv`, which is what `/` on `Int` is: the remainder is never negative. */
export const $lean_int_ediv = (a, b) => {
  if (b === 0n) return 0n;
  const q = a / b; // BigInt division truncates towards zero
  const r = a - q * b;
  return r < 0n ? (b > 0n ? q - 1n : q + 1n) : q;
};

/** `Int.div`, which truncates towards zero; `a / 0` is `0`. */
export const $lean_int_div = (a, b) => (b === 0n ? 0n : a / b);

/** `Int.neg`. */
export const $lean_int_neg = (a) => -a;

/** `Int.not`, the complement of an unbounded integer: `~~~a` is `-a - 1`. */
export const Int_not = (a) => -a - 1n;
