// The runtime functions that answer with an `Int`, where an `Int` is a JavaScript
// number (`intRepr = num`).  `lean_runtime_int_bigint.mjs` is the same catalogue over
// `BigInt`s.

/** `Int.ediv`, which is what `/` on `Int` is: the remainder is never negative. */
export const $lean_int_ediv = (a, b) => {
  if (b === 0) return 0;
  const q = Math.trunc(a / b);
  const r = a - q * b;
  return r < 0 ? (b > 0 ? q - 1 : q + 1) : q;
};

/** `Int.div`, which truncates towards zero; `a / 0` is `0`. */
export const $lean_int_div = (a, b) => (b === 0 ? 0 : Math.trunc(a / b));

/** `Int.neg`. */
export const $lean_int_neg = (a) => -a;

/** `Int.not`, the complement of an unbounded integer: `~~~a` is `-a - 1`. */
export const Int_not = (a) => -a - 1;
