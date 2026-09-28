==== FILE: runtime/lean_values.mjs ====
// Building and reading the values a compiled module takes and answers with.
//
// The backend represents a value of a Lean inductive type as `{ tag, _1, _2, … }`: the
// number of the constructor, in declaration order, and its fields, numbered from one.
// So `List` is `{ tag: 0 }` / `{ tag: 1, _1: head, _2: tail }` and `Option` is
// `{ tag: 0 }` / `{ tag: 1, _1: value }`.  A `Nat`, an `Int` and a `String.Pos.Raw` are
// JavaScript numbers, a `String` is a JavaScript string and an `Array` is a JavaScript
// array.  These helpers are for the tests only; nothing the backend emits needs them.

/** The Lean `List` of the elements of a JavaScript array. */
export const list = (xs) => {
  let out = { tag: 0 };
  for (let i = xs.length - 1; i >= 0; i--) out = { tag: 1, _1: xs[i], _2: out };
  return out;
};

/** The elements of a Lean `List`, as a JavaScript array. */
export const ofList = (xs) => {
  const out = [];
  let cur = xs;
  while (cur.tag === 1) {
    out.push(cur._1);
    cur = cur._2;
  }
  return out;
};

/** `Option.none`. */
export const none = { tag: 0 };

/** `Option.some x`. */
export const some = (x) => ({ tag: 1, _1: x });

==== FILE: runtime/lean_runtime_int_num.mjs ====
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

==== FILE: runtime/lean_runtime_int_bigint.mjs ====
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

==== FILE: runtime/lean_runtime_non_configurable.mjs ====
// The part of the runtime prelude that no configuration changes.
//
// The prelude is one module per *knob*: `LeanScript/Config.lean` decides, for each of the
// six configurable Lean types, whether it is a JavaScript number or a `BigInt`, and a
// compiled module imports each runtime function from the module of the type that
// function answers with:
//
//     lean_runtime_non_configurable.mjs   what no knob changes — this file
//     lean_runtime_nat_<num|bigint>.mjs   the functions that answer with a `Nat`
//     lean_runtime_int_<num|bigint>.mjs   … with an `Int`
//     lean_runtime_usize_<num|bigint>.mjs
//     lean_runtime_uint64_<num|bigint>.mjs
//     lean_runtime_int64_<num|bigint>.mjs
//     lean_runtime_isize_<num|bigint>.mjs
//
// A function belongs here when its answer is of a type that has no knob — a `Bool`, a
// `String`, a `Char`, an array, a list, one of the fixed-width types below 64 bits, or
// a `String.Pos.Raw`, which is a byte offset and always a number.  Where such a
// function *takes* a value of a configurable type it coerces it (`Number(x)`), so it
// works whichever representation the caller chose.
//
// Every function here is pure: it never mutates an argument, which is what lets the
// compiler treat a `Term` as a value.

/* ------------------------------------------------------------------------ arrays */

/** `Array.replicate`. */
export const $lean_mk_array = (n, v) => new Array(Number(n)).fill(v);

/** `Array.uget`. */
export const $lean_array_uget = (a, i) => a[Number(i)];

/** `Array.uset`: persistent, so it answers with a copy. */
export const $lean_array_uset = (a, i, v) => {
  const out = a.slice();
  out[Number(i)] = v;
  return out;
};

/** `Array.set`: persistent, so it answers with a copy. */
export const $lean_array_fset = (a, i, v) => {
  const out = a.slice();
  out[Number(i)] = v;
  return out;
};

/** `Array.mkEmpty`: the capacity is a hint, and a JS array needs none. */
export const Array_mkEmpty = (_capacity) => [];

/** `Array.append`. */
export const Array_append = (a, b) => a.concat(b);

/** `Array.back?`. */
export const Array_back_ = (a) =>
  a.length === 0 ? { tag: 0 } : { tag: 1, _1: a[a.length - 1] };

/**
 * `Array.mk`: a JavaScript array out of a `List`, which is `{ tag: 0 }` /
 * `{ tag: 1, _1: head, _2: tail }`.
 */
export const $lean_array_mk = (xs) => {
  const out = [];
  let cur = xs;
  while (cur.tag === 1) {
    out.push(cur._1);
    cur = cur._2;
  }
  return out;
};

/** `Array.toList`. */
export const $lean_array_to_list = (a) => {
  let out = { tag: 0 };
  for (let i = a.length - 1; i >= 0; i--) out = { tag: 1, _1: a[i], _2: out };
  return out;
};

/* ----------------------------------------------------------------------- strings */

const encoder = new TextEncoder();

/** How many UTF-8 bytes a code point takes. */
const cpBytes = (cp) => (cp < 0x80 ? 1 : cp < 0x800 ? 2 : cp < 0x10000 ? 3 : 4);

/**
 * The UTF-8 byte size of a string, as a JavaScript number.  This is *not*
 * `String.utf8ByteSize`, which answers with a `Nat` and therefore lives in the `nat`
 * module; it is the byte arithmetic the functions below do on a `String.Pos.Raw`,
 * which is a number whatever the configuration says.
 */
const byteSize = (s) => {
  let n = 0;
  for (const ch of s) n += cpBytes(ch.codePointAt(0));
  return n;
};

/** The character whose UTF-8 encoding begins at byte `pos`, and its byte length. */
const charAtByte = (s, pos) => {
  let at = 0;
  for (const ch of s) {
    const w = cpBytes(ch.codePointAt(0));
    if (at === pos) return [ch, w];
    at += w;
  }
  return [undefined, 1];
};

/** `String.Pos.Raw.get`; past the end, Lean answers `(default : Char)`, i.e. `'A'`. */
export const $lean_string_pos_raw_get = (s, pos) => {
  const [ch] = charAtByte(s, Number(pos));
  return ch === undefined ? "A" : ch;
};

/** `String.Pos.Raw.next`. */
export const $lean_string_pos_raw_next = (s, pos) => {
  const p = Number(pos);
  const [, w] = charAtByte(s, p);
  return p + w;
};

/** `String.Pos.Raw.atEnd`. */
export const $lean_string_pos_raw_at_end = (s, pos) => Number(pos) >= byteSize(s);

/** `String.append`. */
export const $lean_string_append = (a, b) => a + b;

/**
 * `String.Slice.Pattern.Internal.memcmpStr`: are the `len` bytes of `lhs` at `lstart`
 * the same as the `len` bytes of `rhs` at `rstart`?
 */
export const $lean_string_memcmp = (lhs, rhs, lstart, rstart, len) => {
  const l = encoder.encode(lhs);
  const r = encoder.encode(rhs);
  const ls = Number(lstart);
  const rs = Number(rstart);
  const n = Number(len);
  for (let i = 0; i < n; i++) {
    if (l[ls + i] !== r[rs + i]) return false;
  }
  return true;
};

/** `String.mk`: a string out of a `List Char`. */
export const $lean_string_mk = (chars) => $lean_array_mk(chars).join("");

/** `String.push`: a `Char` is a one-character string here. */
export const $lean_string_push = (s, c) => s + c;

/** `String.quote`. */
export const String_quote = (s) => {
  let out = '"';
  for (const ch of s) {
    out +=
      ch === "\\" ? "\\\\"
      : ch === '"' ? '\\"'
      : ch === "\n" ? "\\n"
      : ch === "\t" ? "\\t"
      : ch === "\r" ? "\\r"
      : ch;
  }
  return out + '"';
};

/** `Nat.reprFast`: the decimal of the number, whichever way a `Nat` is held. */
export const Nat_reprFast = (n) => String(n);

/* ------------------------------------------------------- String.Slice
 *
 * A `String.Slice` is `{ tag: 0, _1: string, _2: startByte, _3: endByte }`, and a
 * position in it is a UTF-8 byte offset into `_1`.
 */

/** `String.Slice.Pos.nextn`: advance `n` characters. */
export const String_Slice_Pos_nextn = (slice, pos, n) => {
  let p = Number(pos);
  const steps = Number(n);
  for (let k = 0; k < steps; k++) {
    if (p >= slice._3) return slice._3;
    p = $lean_string_pos_raw_next(slice._1, p);
  }
  return p > slice._3 ? slice._3 : p;
};

/** `String.Slice.toString`: the characters between the two byte offsets. */
export const String_Slice_toString = (slice) => {
  let out = "";
  let at = 0;
  for (const ch of slice._1) {
    const w = cpBytes(ch.codePointAt(0));
    if (at >= slice._2 && at < slice._3) out += ch;
    at += w;
  }
  return out;
};

/* ==================================================================================
 * The fixed-width types below 64 bits
 *
 * `UInt8/16/32` and `Int8/16/32` fit in a JavaScript number exactly, so no
 * configuration can change them.  Lean's semantics, which these follow:
 *
 *   - division by zero answers zero;
 *   - a fixed-width division truncates towards zero and wraps (`Int8.div (-128) (-1)`
 *     is `-128`);
 *   - addition, subtraction, multiplication and negation wrap.
 * ================================================================================== */

/** `x` taken modulo `2^w`, for `w ≤ 32`. */
const wrapU = (w, x) => {
  const m = 2 ** w;
  const r = Number(x) % m;
  return r < 0 ? r + m : r;
};

/** `x` taken modulo `2^w` and read as a signed `w`-bit value, for `w ≤ 32`. */
const wrapS = (w, x) => {
  const m = 2 ** w;
  const r = wrapU(w, x);
  return r >= m / 2 ? r - m : r;
};

/** Unsigned division at `w ≤ 32` bits: rounds down, and `a / 0` is `0`. */
const udiv = (a, b) => (Number(b) === 0 ? 0 : Math.floor(Number(a) / Number(b)));

/** Signed division at `w ≤ 32` bits: truncates towards zero, wraps, `a / 0` is `0`. */
const sdiv = (w, a, b) =>
  Number(b) === 0 ? 0 : wrapS(w, Math.trunc(Number(a) / Number(b)));

/** `UInt8.div`. */
export const $lean_uint8_div = (a, b) => udiv(a, b);
/** `UInt16.div`. */
export const $lean_uint16_div = (a, b) => udiv(a, b);
/** `UInt32.div`. */
export const $lean_uint32_div = (a, b) => udiv(a, b);

/** `Int8.div`. */
export const $lean_int8_div = (a, b) => sdiv(8, a, b);
/** `Int16.div`. */
export const $lean_int16_div = (a, b) => sdiv(16, a, b);
/** `Int32.div`. */
export const $lean_int32_div = (a, b) => sdiv(32, a, b);

/** `UInt8.neg`. */
export const $lean_uint8_neg = (a) => wrapU(8, -Number(a));
/** `UInt16.neg`. */
export const $lean_uint16_neg = (a) => wrapU(16, -Number(a));
/** `UInt32.neg`. */
export const $lean_uint32_neg = (a) => wrapU(32, -Number(a));

/** `Int8.neg`. */
export const $lean_int8_neg = (a) => wrapS(8, -Number(a));
/** `Int16.neg`. */
export const $lean_int16_neg = (a) => wrapS(16, -Number(a));
/** `Int32.neg`. */
export const $lean_int32_neg = (a) => wrapS(32, -Number(a));

/** `Int8.ofNat`: the `Nat` may be a number or a `BigInt`, the answer is a number. */
export const $lean_int8_of_nat = (n) => wrapS(8, n);
/** `Int16.ofNat`. */
export const $lean_int16_of_nat = (n) => wrapS(16, n);
/** `Int32.ofNat`. */
export const $lean_int32_of_nat = (n) => wrapS(32, n);

/** `UInt8.add`. */
export const $lean_uint8_add = (a, b) => wrapU(8, Number(a) + Number(b));
/** `UInt16.add`. */
export const $lean_uint16_add = (a, b) => wrapU(16, Number(a) + Number(b));
/** `UInt32.add`. */
export const $lean_uint32_add = (a, b) => wrapU(32, Number(a) + Number(b));

/** `UInt8.sub`. */
export const $lean_uint8_sub = (a, b) => wrapU(8, Number(a) - Number(b));
/** `UInt16.sub`. */
export const $lean_uint16_sub = (a, b) => wrapU(16, Number(a) - Number(b));
/** `UInt32.sub`. */
export const $lean_uint32_sub = (a, b) => wrapU(32, Number(a) - Number(b));

/** `UInt8.mul`. */
export const $lean_uint8_mul = (a, b) => wrapU(8, Number(a) * Number(b));
/** `UInt16.mul`. */
export const $lean_uint16_mul = (a, b) => wrapU(16, Number(a) * Number(b));
/** `UInt32.mul`: the product of two 32-bit numbers exceeds the exact range of a
 * double, so the 32-bit machine multiplication is used and read back unsigned. */
export const $lean_uint32_mul = (a, b) => Math.imul(Number(a), Number(b)) >>> 0;

/* ----------------------------------------- the narrow signed wrapping arithmetic
 *
 * Addition, subtraction and multiplication of `Int8/16/32` wrap, which the JavaScript
 * operator does not, so the printer never writes these as operators: they are calls of
 * the functions below.  `UInt8/16/32` have theirs above.
 */

/** `Int8.add`. */
export const $lean_int8_add = (a, b) => wrapS(8, Number(a) + Number(b));
/** `Int16.add`. */
export const $lean_int16_add = (a, b) => wrapS(16, Number(a) + Number(b));
/** `Int32.add`. */
export const $lean_int32_add = (a, b) => wrapS(32, Number(a) + Number(b));

/** `Int8.sub`. */
export const $lean_int8_sub = (a, b) => wrapS(8, Number(a) - Number(b));
/** `Int16.sub`. */
export const $lean_int16_sub = (a, b) => wrapS(16, Number(a) - Number(b));
/** `Int32.sub`. */
export const $lean_int32_sub = (a, b) => wrapS(32, Number(a) - Number(b));

/** `Int8.mul`. */
export const $lean_int8_mul = (a, b) => wrapS(8, Number(a) * Number(b));
/** `Int16.mul`. */
export const $lean_int16_mul = (a, b) => wrapS(16, Number(a) * Number(b));
/** `Int32.mul`: as `UInt32.mul`, through the 32-bit machine multiplication, whose
 * answer is already the signed 32-bit pattern. */
export const $lean_int32_mul = (a, b) => Math.imul(Number(a), Number(b));

/* ------------------------------------------ the narrow bitwise operations
 *
 * Lean takes the shift distance of a `w`-bit type modulo `w` (a negative distance
 * counts from the top), and the answer is the `w`-bit pattern.  The work goes through
 * `BigInt`, which is exact at every width, and comes back as the number the type is
 * held as.
 */

/** The shift distance Lean uses at `w` bits: the argument taken modulo `w`. */
const shiftW = (w, b) => {
  const m = BigInt(w);
  return ((BigInt(b) % m) + m) % m;
};

/** An unsigned `w`-bit answer, out of the `BigInt` that computed it. */
const outU = (w, x) => Number(BigInt.asUintN(w, x));

/** A signed `w`-bit answer, out of the `BigInt` that computed it. */
const outS = (w, x) => Number(BigInt.asIntN(w, x));

/** `UInt8.land`. */
export const $lean_uint8_land = (a, b) => outU(8, BigInt(a) & BigInt(b));
/** `UInt16.land`. */
export const $lean_uint16_land = (a, b) => outU(16, BigInt(a) & BigInt(b));
/** `UInt32.land`. */
export const $lean_uint32_land = (a, b) => outU(32, BigInt(a) & BigInt(b));

/** `UInt8.lor`. */
export const $lean_uint8_lor = (a, b) => outU(8, BigInt(a) | BigInt(b));
/** `UInt16.lor`. */
export const $lean_uint16_lor = (a, b) => outU(16, BigInt(a) | BigInt(b));
/** `UInt32.lor`. */
export const $lean_uint32_lor = (a, b) => outU(32, BigInt(a) | BigInt(b));

/** `UInt8.xor`. */
export const $lean_uint8_xor = (a, b) => outU(8, BigInt(a) ^ BigInt(b));
/** `UInt16.xor`. */
export const $lean_uint16_xor = (a, b) => outU(16, BigInt(a) ^ BigInt(b));
/** `UInt32.xor`. */
export const $lean_uint32_xor = (a, b) => outU(32, BigInt(a) ^ BigInt(b));

/** `UInt8.complement`. */
export const $lean_uint8_complement = (a) => outU(8, ~BigInt(a));
/** `UInt16.complement`. */
export const $lean_uint16_complement = (a) => outU(16, ~BigInt(a));
/** `UInt32.complement`. */
export const $lean_uint32_complement = (a) => outU(32, ~BigInt(a));

/** `UInt8.shiftLeft`. */
export const $lean_uint8_shift_left = (a, b) => outU(8, BigInt(a) << shiftW(8, b));
/** `UInt16.shiftLeft`. */
export const $lean_uint16_shift_left = (a, b) => outU(16, BigInt(a) << shiftW(16, b));
/** `UInt32.shiftLeft`. */
export const $lean_uint32_shift_left = (a, b) => outU(32, BigInt(a) << shiftW(32, b));

/** `UInt8.shiftRight`; the value is unsigned, so the shift brings in zeros. */
export const $lean_uint8_shift_right = (a, b) =>
  outU(8, BigInt.asUintN(8, BigInt(a)) >> shiftW(8, b));
/** `UInt16.shiftRight`. */
export const $lean_uint16_shift_right = (a, b) =>
  outU(16, BigInt.asUintN(16, BigInt(a)) >> shiftW(16, b));
/** `UInt32.shiftRight`. */
export const $lean_uint32_shift_right = (a, b) =>
  outU(32, BigInt.asUintN(32, BigInt(a)) >> shiftW(32, b));

/** `Int8.land`, on the two's complement. */
export const $lean_int8_land = (a, b) => outS(8, BigInt(a) & BigInt(b));
/** `Int16.land`. */
export const $lean_int16_land = (a, b) => outS(16, BigInt(a) & BigInt(b));
/** `Int32.land`. */
export const $lean_int32_land = (a, b) => outS(32, BigInt(a) & BigInt(b));

/** `Int8.lor`. */
export const $lean_int8_lor = (a, b) => outS(8, BigInt(a) | BigInt(b));
/** `Int16.lor`. */
export const $lean_int16_lor = (a, b) => outS(16, BigInt(a) | BigInt(b));
/** `Int32.lor`. */
export const $lean_int32_lor = (a, b) => outS(32, BigInt(a) | BigInt(b));

/** `Int8.xor`. */
export const $lean_int8_xor = (a, b) => outS(8, BigInt(a) ^ BigInt(b));
/** `Int16.xor`. */
export const $lean_int16_xor = (a, b) => outS(16, BigInt(a) ^ BigInt(b));
/** `Int32.xor`. */
export const $lean_int32_xor = (a, b) => outS(32, BigInt(a) ^ BigInt(b));

/** `Int8.complement`. */
export const $lean_int8_complement = (a) => outS(8, ~BigInt(a));
/** `Int16.complement`. */
export const $lean_int16_complement = (a) => outS(16, ~BigInt(a));
/** `Int32.complement`. */
export const $lean_int32_complement = (a) => outS(32, ~BigInt(a));

/** `Int8.shiftLeft`. */
export const $lean_int8_shift_left = (a, b) => outS(8, BigInt(a) << shiftW(8, b));
/** `Int16.shiftLeft`. */
export const $lean_int16_shift_left = (a, b) => outS(16, BigInt(a) << shiftW(16, b));
/** `Int32.shiftLeft`. */
export const $lean_int32_shift_left = (a, b) => outS(32, BigInt(a) << shiftW(32, b));

/** `Int8.shiftRight`, which is arithmetic: the sign bit is carried in. */
export const $lean_int8_shift_right = (a, b) =>
  outS(8, BigInt.asIntN(8, BigInt(a)) >> shiftW(8, b));
/** `Int16.shiftRight`, arithmetic. */
export const $lean_int16_shift_right = (a, b) =>
  outS(16, BigInt.asIntN(16, BigInt(a)) >> shiftW(16, b));
/** `Int32.shiftRight`, arithmetic. */
export const $lean_int32_shift_right = (a, b) =>
  outS(32, BigInt.asIntN(32, BigInt(a)) >> shiftW(32, b));

/* ------------------------------------------------------------------- equalities
 *
 * A decision is a `Bool`, so these have no representation of their own: `===` is the
 * equality of two numbers and the equality of two `BigInt`s alike, and `<` and `<=`
 * order both.
 */

/** `Int.instDecidableEq`. */
export const Int_instDecidableEq = (a, b) => a === b;
/** `instDecidableEqUSize`. */
export const instDecidableEqUSize = (a, b) => a === b;
/** `instDecidableEqUInt8`. */
export const instDecidableEqUInt8 = (a, b) => a === b;
/** `instDecidableEqUInt16`. */
export const instDecidableEqUInt16 = (a, b) => a === b;
/** `instDecidableEqUInt32`. */
export const instDecidableEqUInt32 = (a, b) => a === b;
/** `instDecidableEqUInt64`. */
export const instDecidableEqUInt64 = (a, b) => a === b;
/** `instDecidableEqInt8`. */
export const instDecidableEqInt8 = (a, b) => a === b;
/** `instDecidableEqInt16`. */
export const instDecidableEqInt16 = (a, b) => a === b;
/** `instDecidableEqInt32`. */
export const instDecidableEqInt32 = (a, b) => a === b;
/** `instDecidableEqInt64`. */
export const instDecidableEqInt64 = (a, b) => a === b;
/** `instDecidableEqISize`. */
export const instDecidableEqISize = (a, b) => a === b;

/** `Int8.decLt`. */
export const $lean_int8_dec_lt = (a, b) => a < b;
/** `Int8.decLe`. */
export const $lean_int8_dec_le = (a, b) => a <= b;
/** `Int16.decLt`. */
export const $lean_int16_dec_lt = (a, b) => a < b;
/** `Int16.decLe`. */
export const $lean_int16_dec_le = (a, b) => a <= b;
/** `Int32.decLt`. */
export const $lean_int32_dec_lt = (a, b) => a < b;
/** `Int32.decLe`. */
export const $lean_int32_dec_le = (a, b) => a <= b;
/** `Int64.decLt`. */
export const $lean_int64_dec_lt = (a, b) => a < b;
/** `Int64.decLe`. */
export const $lean_int64_dec_le = (a, b) => a <= b;
/** `ISize.decLt`. */
export const $lean_isize_dec_lt = (a, b) => a < b;
/** `ISize.decLe`. */
export const $lean_isize_dec_le = (a, b) => a <= b;

/* ==================================================================================
 * Lean library declarations
 *
 * A compiled module only contains the declarations of the Lean module it was compiled
 * from; a declaration of the standard library that survives the optimiser is left as a
 * free name, and imported from here in exactly the same way an extern is.  The
 * definitions below follow the calling convention the backend uses for a Lean
 * declaration: type arguments and proofs are erased, a class with a single method is
 * unboxed into that method, a constructor is `{ tag, _1, _2, … }`, and an `Option` is
 * `{ tag: 0 }` for `none` and `{ tag: 1, _1: x }` for `some x`.
 * ================================================================================== */

/** `Function.const`, with its type arguments erased: `const a` ignores its argument. */
export const Function_const = (a, _b) => a;

/** `instBEqOfDecidableEq`: a `BEq` is its one method, and so is a `DecidableEq`. */
export const instBEqOfDecidableEq = (decEq) => decEq;

/** `Repr.addAppParen`: parenthesise a `Std.Format` when the context binds tighter. */
export const Repr_addAppParen = (f, prec) =>
  prec >= 1024
    ? { tag: 5, _1: { tag: 5, _1: { tag: 3, _1: "(" }, _2: f }, _2: { tag: 3, _1: ")" } }
    : f;

/** `List.reverse`; a `List` is `{ tag: 0 }` / `{ tag: 1, _1: head, _2: tail }`. */
export const List_reverse = (xs) => {
  let out = { tag: 0 };
  let cur = xs;
  while (cur.tag === 1) {
    out = { tag: 1, _1: cur._1, _2: out };
    cur = cur._2;
  }
  return out;
};

/**
 * `Id.instMonad`.  The only monadic function of the corpus that takes a `Monad` and is
 * not compiled into the module is `Array.foldrMUnsafe.fold` below, which is only ever
 * handed this instance; the marker is what it checks for.
 */
export const Id_instMonad = { id: true };

/**
 * `Array.foldrMUnsafe.fold`: fold `f` over `as[stop … i)` from the right.  Only the
 * identity monad is supported — in it a monadic value *is* the value, so there is
 * nothing to bind.
 */
export const _private_Init_Data_Array_Basic_0_Array_foldrMUnsafe_fold = (
  monad,
  f,
  as,
  i,
  stop,
  b,
) => {
  if (monad !== Id_instMonad) {
    throw new Error("lean_runtime: Array.foldrMUnsafe.fold only supports Id");
  }
  let acc = b;
  let k = Number(i);
  const end = Number(stop);
  while (k > end) {
    k -= 1;
    acc = f(as[k], acc);
  }
  return acc;
};

/**
 * `instDecidableEqBitVec`.  Both bit vectors are of the same width, so they are held
 * the same way whatever the configuration says, and comparing them does not depend on
 * which way that is.
 */
export const instDecidableEqBitVec = (_w, a, b) => a === b;

/** `instDecidableLtBitVec`: the *unsigned* order, which is the one `BitVec` has. */
export const instDecidableLtBitVec = (_w, a, b) => a < b;

/** `instDecidableLeBitVec`: the *unsigned* order, which is the one `BitVec` has. */
export const instDecidableLeBitVec = (_w, a, b) => a <= b;

==== FILE: runtime/lean_runtime_isize_num.mjs ====
// The runtime functions that answer with an `ISize`, where an `ISize` is a JavaScript
// number (`isizeRepr = num`).
//
// An `ISize` is 64 bits wide and a number holds only 53 of them exactly, so every answer
// here is exact modulo `2^64`, read back as a signed 64-bit value, and then rounded to
// a number.  `lean_runtime_isize_bigint.mjs` is the same catalogue over `BigInt`s, where
// nothing is cut.

/** `x` taken modulo `2^64`, read as a signed 64-bit value, and then back to a number. */
const wrapS64 = (x) => Number(BigInt.asIntN(64, BigInt(x)));

/** The shift distance Lean uses at 64 bits: the argument taken modulo 64. */
const shift64 = (b) => ((BigInt(b) % 64n) + 64n) % 64n;

/** `ISize.ofNat`. */
export const $lean_isize_of_nat = (n) => wrapS64(n);

/** `ISize.div`: truncates towards zero, wraps, and `a / 0` is `0`. */
export const $lean_isize_div = (a, b) =>
  Number(b) === 0 ? 0 : wrapS64(BigInt(a) / BigInt(b));

/** `ISize.neg`. */
export const $lean_isize_neg = (a) => wrapS64(-BigInt(a));

/** `ISize.add`. */
export const $lean_isize_add = (a, b) => wrapS64(BigInt(a) + BigInt(b));
/** `ISize.sub`. */
export const $lean_isize_sub = (a, b) => wrapS64(BigInt(a) - BigInt(b));
/** `ISize.mul`. */
export const $lean_isize_mul = (a, b) => wrapS64(BigInt(a) * BigInt(b));

/** `ISize.land`, on the two's complement. */
export const $lean_isize_land = (a, b) => wrapS64(BigInt(a) & BigInt(b));
/** `ISize.lor`. */
export const $lean_isize_lor = (a, b) => wrapS64(BigInt(a) | BigInt(b));
/** `ISize.xor`. */
export const $lean_isize_xor = (a, b) => wrapS64(BigInt(a) ^ BigInt(b));
/** `ISize.complement`. */
export const $lean_isize_complement = (a) => wrapS64(~BigInt(a));
/** `ISize.shiftLeft`. */
export const $lean_isize_shift_left = (a, b) => wrapS64(BigInt(a) << shift64(b));
/** `ISize.shiftRight`, which is arithmetic: the sign bit is carried in. */
export const $lean_isize_shift_right = (a, b) => wrapS64(BigInt(a) >> shift64(b));

==== FILE: runtime/lean_runtime_bitvec_num.mjs ====
// The runtime functions that answer with a `BitVec w`, where a bit vector is a
// JavaScript number (`bitvecRepr = num`).
//
// A number holds an integer exactly only below `2^53`, so the wrap is computed over
// `BigInt` and the answer is read back as a number: the arithmetic is exact modulo
// `2^w` and then rounded, which is the trade-off this representation makes.  The width
// itself is a `Nat`, so it arrives as a number or as a `BigInt` depending on `natRepr`;
// every function reads it through `W` and so accepts both.
// `lean_runtime_bitvec_bigint.mjs` makes the other trade-off.

/** The width, as a JavaScript number, whichever representation a `Nat` has. */
const W = (w) => Number(w);

/** Either representation of a bit vector, lifted to a `BigInt`. */
const bi = (x) => BigInt(x);

/** `x` cut to `w` bits, and back to a number. */
const val = (w, x) => Number(BigInt.asUintN(W(w), bi(x)));

/** `BitVec.ofNat`: the natural number cut to `w` bits. */
export const BitVec_ofNat = (w, n) => val(w, n);

/** `BitVec.add`. */
export const BitVec_add = (w, a, b) => val(w, bi(a) + bi(b));
/** `BitVec.sub`. */
export const BitVec_sub = (w, a, b) => val(w, bi(a) - bi(b));
/** `BitVec.mul`. */
export const BitVec_mul = (w, a, b) => val(w, bi(a) * bi(b));
/** `BitVec.neg`. */
export const BitVec_neg = (w, a) => val(w, -bi(a));

/** `BitVec.udiv`: unsigned division, and `a / 0` is `0` as `Nat.div` is. */
export const BitVec_udiv = (w, a, b) =>
  bi(b) === 0n ? val(w, 0n) : val(w, bi(a) / bi(b));
/** `BitVec.umod`: unsigned remainder, and `a % 0` is `a` as `Nat.mod` is. */
export const BitVec_umod = (w, a, b) =>
  bi(b) === 0n ? val(w, a) : val(w, bi(a) % bi(b));

/** `BitVec.and`. */
export const BitVec_and = (w, a, b) => val(w, bi(a) & bi(b));
/** `BitVec.or`. */
export const BitVec_or = (w, a, b) => val(w, bi(a) | bi(b));
/** `BitVec.xor`. */
export const BitVec_xor = (w, a, b) => val(w, bi(a) ^ bi(b));
/** `BitVec.not`: the complement inside `w` bits. */
export const BitVec_not = (w, a) => val(w, ~bi(a));

/**
 * `BitVec.shiftLeft`.  The distance is a `Nat` and is *not* taken modulo the width:
 * shifting by the width or more answers zero, which is also what keeps the `BigInt`
 * the wrap is computed over from being built at an absurd size.
 */
export const BitVec_shiftLeft = (w, a, n) =>
  bi(n) >= bi(W(w)) ? val(w, 0n) : val(w, bi(a) << bi(n));
/** `BitVec.ushiftRight`: the value is unsigned, so the shift brings in zeros. */
export const BitVec_ushiftRight = (w, a, n) =>
  bi(n) >= bi(W(w)) ? val(w, 0n) : val(w, bi(a) >> bi(n));
/** `BitVec.sshiftRight`: the shift of the *signed* reading, so it brings in the sign. */
export const BitVec_sshiftRight = (w, a, n) => {
  const signed = BigInt.asIntN(W(w), bi(a));
  const d = bi(n) >= bi(W(w)) ? bi(W(w)) : bi(n);
  return val(w, signed >> d);
};

/** `UInt64.toBitVec`: a `UInt64` and a `BitVec 64` are held the same way. */
export const $lean_uint64_to_bitvec = (a) => val(64, a);
/** `USize.toBitVec`: a `USize` is 64 bits wide, and is held the same way. */
export const $lean_usize_to_bitvec = (a) => val(64, a);

==== FILE: runtime/lean_runtime_nat_bigint.mjs ====
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

==== FILE: runtime/lean_runtime_isize_bigint.mjs ====
// The runtime functions that answer with an `ISize`, where an `ISize` is a `BigInt`
// (`isizeRepr = bigint`): exact at all 64 bits.  `lean_runtime_isize_num.mjs` is the
// same catalogue over JavaScript numbers, which hold only 53 bits exactly.

/** `x` taken modulo `2^64` and read as a signed 64-bit value. */
const S64 = (x) => BigInt.asIntN(64, BigInt(x));

/** The shift distance Lean uses at 64 bits: the argument taken modulo 64. */
const shift64 = (b) => ((BigInt(b) % 64n) + 64n) % 64n;

/** `ISize.ofNat`. */
export const $lean_isize_of_nat = (n) => S64(n);

/** `ISize.div`: truncates towards zero, wraps, and `a / 0` is `0`. */
export const $lean_isize_div = (a, b) => (S64(b) === 0n ? 0n : S64(S64(a) / S64(b)));

/** `ISize.neg`. */
export const $lean_isize_neg = (a) => S64(-S64(a));

/** `ISize.add`. */
export const $lean_isize_add = (a, b) => S64(S64(a) + S64(b));
/** `ISize.sub`. */
export const $lean_isize_sub = (a, b) => S64(S64(a) - S64(b));
/** `ISize.mul`. */
export const $lean_isize_mul = (a, b) => S64(S64(a) * S64(b));

/** `ISize.land`, on the two's complement. */
export const $lean_isize_land = (a, b) => S64(S64(a) & S64(b));
/** `ISize.lor`. */
export const $lean_isize_lor = (a, b) => S64(S64(a) | S64(b));
/** `ISize.xor`. */
export const $lean_isize_xor = (a, b) => S64(S64(a) ^ S64(b));
/** `ISize.complement`. */
export const $lean_isize_complement = (a) => S64(~S64(a));
/** `ISize.shiftLeft`. */
export const $lean_isize_shift_left = (a, b) => S64(S64(a) << shift64(b));
/** `ISize.shiftRight`, which is arithmetic: the sign bit is carried in. */
export const $lean_isize_shift_right = (a, b) => S64(S64(a) >> shift64(b));

==== FILE: runtime/lean_runtime_usize_bigint.mjs ====
// The runtime functions that answer with a `USize`, where a `USize` is a `BigInt`
// (`usizeRepr = bigint`): exact at all 64 bits.  `lean_runtime_usize_num.mjs` is the
// same catalogue over JavaScript numbers.

/** `x` taken modulo `2^64`. */
const U64 = (x) => BigInt.asUintN(64, BigInt(x));

/** The shift distance Lean uses at 64 bits: the argument taken modulo 64. */
const shift64 = (b) => ((BigInt(b) % 64n) + 64n) % 64n;

/** `USize.ofNat`. */
export const $lean_usize_of_nat = (n) => U64(n);

/** `UInt64.toUSize`: both are 64 bits wide here, so nothing is cut. */
export const $lean_uint64_to_usize = (a) => U64(a);

/** `USize.div`: rounds down, and `a / 0` is `0`. */
export const $lean_usize_div = (a, b) => (U64(b) === 0n ? 0n : U64(a) / U64(b));

/** `USize.neg`. */
export const $lean_usize_neg = (a) => U64(-U64(a));

/** `USize.add`. */
export const $lean_usize_add = (a, b) => U64(U64(a) + U64(b));
/** `USize.sub`. */
export const $lean_usize_sub = (a, b) => U64(U64(a) - U64(b));
/** `USize.mul`. */
export const $lean_usize_mul = (a, b) => U64(U64(a) * U64(b));

/** `USize.land`. */
export const $lean_usize_land = (a, b) => U64(a) & U64(b);
/** `USize.lor`. */
export const $lean_usize_lor = (a, b) => U64(U64(a) | U64(b));
/** `USize.xor`. */
export const $lean_usize_xor = (a, b) => U64(U64(a) ^ U64(b));
/** `USize.complement`. */
export const $lean_usize_complement = (a) => U64(~U64(a));
/** `USize.shiftLeft`. */
export const $lean_usize_shift_left = (a, b) => U64(U64(a) << shift64(b));
/** `USize.shiftRight`; the value is unsigned, so the shift brings in zeros. */
export const $lean_usize_shift_right = (a, b) => U64(U64(a) >> shift64(b));

==== FILE: runtime/lean_runtime_bitvec_bigint.mjs ====
// The runtime functions that answer with a `BitVec w`, where a bit vector of at least
// 32 bits is a `BigInt` (`bitvecRepr = bigint`).
//
// A bit vector narrower than 32 bits fits in a JavaScript number exactly and is one
// whatever the configuration says (`LeanScript.Config.JsConfig.reprOfPrim`), so these
// functions answer with a number at those widths and with a `BigInt` at 32 bits and
// above.  The width itself is a `Nat`, so it arrives as a number or as a `BigInt`
// depending on `natRepr`; every function reads it through `W` and so accepts both.
// `lean_runtime_bitvec_num.mjs` is the same catalogue where every width is a number.

/** The width, as a JavaScript number, whichever representation a `Nat` has. */
const W = (w) => Number(w);

/** Either representation of a bit vector, lifted to a `BigInt`. */
const bi = (x) => BigInt(x);

/** `x` cut to `w` bits, in the representation a bit vector of that width has. */
const val = (w, x) => {
  const n = W(w);
  const v = BigInt.asUintN(n, bi(x));
  return n >= 32 ? v : Number(v);
};

/** `BitVec.ofNat`: the natural number cut to `w` bits. */
export const BitVec_ofNat = (w, n) => val(w, n);

/** `BitVec.add`. */
export const BitVec_add = (w, a, b) => val(w, bi(a) + bi(b));
/** `BitVec.sub`. */
export const BitVec_sub = (w, a, b) => val(w, bi(a) - bi(b));
/** `BitVec.mul`. */
export const BitVec_mul = (w, a, b) => val(w, bi(a) * bi(b));
/** `BitVec.neg`. */
export const BitVec_neg = (w, a) => val(w, -bi(a));

/** `BitVec.udiv`: unsigned division, and `a / 0` is `0` as `Nat.div` is. */
export const BitVec_udiv = (w, a, b) =>
  bi(b) === 0n ? val(w, 0n) : val(w, bi(a) / bi(b));
/** `BitVec.umod`: unsigned remainder, and `a % 0` is `a` as `Nat.mod` is. */
export const BitVec_umod = (w, a, b) =>
  bi(b) === 0n ? val(w, a) : val(w, bi(a) % bi(b));

/** `BitVec.and`. */
export const BitVec_and = (w, a, b) => val(w, bi(a) & bi(b));
/** `BitVec.or`. */
export const BitVec_or = (w, a, b) => val(w, bi(a) | bi(b));
/** `BitVec.xor`. */
export const BitVec_xor = (w, a, b) => val(w, bi(a) ^ bi(b));
/** `BitVec.not`: the complement inside `w` bits. */
export const BitVec_not = (w, a) => val(w, ~bi(a));

/**
 * `BitVec.shiftLeft`.  The distance is a `Nat` and is *not* taken modulo the width:
 * shifting by the width or more answers zero, which is also what keeps the `BigInt`
 * from being built at an absurd size.
 */
export const BitVec_shiftLeft = (w, a, n) =>
  bi(n) >= bi(W(w)) ? val(w, 0n) : val(w, bi(a) << bi(n));
/** `BitVec.ushiftRight`: the value is unsigned, so the shift brings in zeros. */
export const BitVec_ushiftRight = (w, a, n) =>
  bi(n) >= bi(W(w)) ? val(w, 0n) : val(w, bi(a) >> bi(n));
/** `BitVec.sshiftRight`: the shift of the *signed* reading, so it brings in the sign. */
export const BitVec_sshiftRight = (w, a, n) => {
  const signed = BigInt.asIntN(W(w), bi(a));
  const d = bi(n) >= bi(W(w)) ? bi(W(w)) : bi(n);
  return val(w, signed >> d);
};

/** `UInt64.toBitVec`: a `UInt64` and a `BitVec 64` are held the same way. */
export const $lean_uint64_to_bitvec = (a) => val(64, a);
/** `USize.toBitVec`: a `USize` is 64 bits wide, and is held the same way. */
export const $lean_usize_to_bitvec = (a) => val(64, a);

==== FILE: runtime/lean_runtime_int64_bigint.mjs ====
// The runtime functions that answer with an `Int64`, where an `Int64` is a `BigInt`
// (`int64Repr = bigint`): exact at all 64 bits.  `lean_runtime_int64_num.mjs` is the
// same catalogue over JavaScript numbers, which hold only 53 bits exactly.

/** `x` taken modulo `2^64` and read as a signed 64-bit value. */
const S64 = (x) => BigInt.asIntN(64, BigInt(x));

/** The shift distance Lean uses at 64 bits: the argument taken modulo 64. */
const shift64 = (b) => ((BigInt(b) % 64n) + 64n) % 64n;

/** `Int64.ofNat`. */
export const $lean_int64_of_nat = (n) => S64(n);

/** `Int64.div`: truncates towards zero, wraps, and `a / 0` is `0`. */
export const $lean_int64_div = (a, b) => (S64(b) === 0n ? 0n : S64(S64(a) / S64(b)));

/** `Int64.neg`. */
export const $lean_int64_neg = (a) => S64(-S64(a));

/** `Int64.add`. */
export const $lean_int64_add = (a, b) => S64(S64(a) + S64(b));
/** `Int64.sub`. */
export const $lean_int64_sub = (a, b) => S64(S64(a) - S64(b));
/** `Int64.mul`. */
export const $lean_int64_mul = (a, b) => S64(S64(a) * S64(b));

/** `Int64.land`, on the two's complement. */
export const $lean_int64_land = (a, b) => S64(S64(a) & S64(b));
/** `Int64.lor`. */
export const $lean_int64_lor = (a, b) => S64(S64(a) | S64(b));
/** `Int64.xor`. */
export const $lean_int64_xor = (a, b) => S64(S64(a) ^ S64(b));
/** `Int64.complement`. */
export const $lean_int64_complement = (a) => S64(~S64(a));
/** `Int64.shiftLeft`. */
export const $lean_int64_shift_left = (a, b) => S64(S64(a) << shift64(b));
/** `Int64.shiftRight`, which is arithmetic: the sign bit is carried in. */
export const $lean_int64_shift_right = (a, b) => S64(S64(a) >> shift64(b));

==== FILE: runtime/lean_runtime_uint64_bigint.mjs ====
// The runtime functions that answer with a `UInt64`, where a `UInt64` is a `BigInt`
// (`uint64Repr = bigint`): exact at all 64 bits.  `lean_runtime_uint64_num.mjs` is the
// same catalogue over JavaScript numbers, which hold only 53 bits exactly.

/** `x` taken modulo `2^64`. */
const U64 = (x) => BigInt.asUintN(64, BigInt(x));

/** The shift distance Lean uses at 64 bits: the argument taken modulo 64. */
const shift64 = (b) => ((BigInt(b) % 64n) + 64n) % 64n;

const encoder = new TextEncoder();

/** `UInt64.ofNat`. */
export const $lean_uint64_of_nat = (n) => U64(n);

/** `UInt64.div`: rounds down, and `a / 0` is `0`. */
export const $lean_uint64_div = (a, b) => (U64(b) === 0n ? 0n : U64(a) / U64(b));

/** `UInt64.neg`. */
export const $lean_uint64_neg = (a) => U64(-U64(a));

/** `UInt64.add`. */
export const $lean_uint64_add = (a, b) => U64(U64(a) + U64(b));
/** `UInt64.sub`. */
export const $lean_uint64_sub = (a, b) => U64(U64(a) - U64(b));
/** `UInt64.mul`. */
export const $lean_uint64_mul = (a, b) => U64(U64(a) * U64(b));

/** `UInt64.land`. */
export const $lean_uint64_land = (a, b) => U64(a) & U64(b);
/** `UInt64.lor`. */
export const $lean_uint64_lor = (a, b) => U64(U64(a) | U64(b));
/** `UInt64.xor`. */
export const $lean_uint64_xor = (a, b) => U64(U64(a) ^ U64(b));
/** `UInt64.complement`. */
export const $lean_uint64_complement = (a) => U64(~U64(a));
/** `UInt64.shiftLeft`. */
export const $lean_uint64_shift_left = (a, b) => U64(U64(a) << shift64(b));
/** `UInt64.shiftRight`; the shift is taken modulo 64, as Lean's is. */
export const $lean_uint64_shift_right = (a, b) => U64(U64(a) >> shift64(b));

/**
 * `String.hash`: FNV-1a over the UTF-8 bytes, taken to 64 bits.  Lean's own hash is
 * not specified by the language, and nothing in a compiled program may depend on its
 * value — only on its being a function of the string.
 */
export const $lean_string_hash = (s) => {
  let h = 0xcbf29ce484222325n;
  for (const b of encoder.encode(s)) {
    h = U64((h ^ BigInt(b)) * 0x100000001b3n);
  }
  return h;
};

/** `instHashableString`: a `Hashable` is its one method. */
export const instHashableString = (s) => $lean_string_hash(s);

/** `instHashableNat`. */
export const instHashableNat = (n) => U64(n);

==== FILE: runtime/lean_runtime_int64_num.mjs ====
// The runtime functions that answer with an `Int64`, where an `Int64` is a JavaScript
// number (`int64Repr = num`).
//
// An `Int64` is 64 bits wide and a number holds only 53 of them exactly, so every answer
// here is exact modulo `2^64`, read back as a signed 64-bit value, and then rounded to
// a number.  `lean_runtime_int64_bigint.mjs` is the same catalogue over `BigInt`s, where
// nothing is cut.

/** `x` taken modulo `2^64`, read as a signed 64-bit value, and then back to a number. */
const wrapS64 = (x) => Number(BigInt.asIntN(64, BigInt(x)));

/** The shift distance Lean uses at 64 bits: the argument taken modulo 64. */
const shift64 = (b) => ((BigInt(b) % 64n) + 64n) % 64n;

/** `Int64.ofNat`. */
export const $lean_int64_of_nat = (n) => wrapS64(n);

/** `Int64.div`: truncates towards zero, wraps, and `a / 0` is `0`. */
export const $lean_int64_div = (a, b) =>
  Number(b) === 0 ? 0 : wrapS64(BigInt(a) / BigInt(b));

/** `Int64.neg`. */
export const $lean_int64_neg = (a) => wrapS64(-BigInt(a));

/** `Int64.add`. */
export const $lean_int64_add = (a, b) => wrapS64(BigInt(a) + BigInt(b));
/** `Int64.sub`. */
export const $lean_int64_sub = (a, b) => wrapS64(BigInt(a) - BigInt(b));
/** `Int64.mul`. */
export const $lean_int64_mul = (a, b) => wrapS64(BigInt(a) * BigInt(b));

/** `Int64.land`, on the two's complement. */
export const $lean_int64_land = (a, b) => wrapS64(BigInt(a) & BigInt(b));
/** `Int64.lor`. */
export const $lean_int64_lor = (a, b) => wrapS64(BigInt(a) | BigInt(b));
/** `Int64.xor`. */
export const $lean_int64_xor = (a, b) => wrapS64(BigInt(a) ^ BigInt(b));
/** `Int64.complement`. */
export const $lean_int64_complement = (a) => wrapS64(~BigInt(a));
/** `Int64.shiftLeft`. */
export const $lean_int64_shift_left = (a, b) => wrapS64(BigInt(a) << shift64(b));
/** `Int64.shiftRight`, which is arithmetic: the sign bit is carried in. */
export const $lean_int64_shift_right = (a, b) => wrapS64(BigInt(a) >> shift64(b));

==== FILE: runtime/lean_runtime_uint64_num.mjs ====
// The runtime functions that answer with a `UInt64`, where a `UInt64` is a JavaScript
// number (`uint64Repr = num`).
//
// A `UInt64` is 64 bits wide and a number holds only 53 of them exactly, so every
// answer here is exact modulo `2^64` and then rounded to a number — the trade-off this
// representation makes.  The two hashes are the exception: a hash is only ever a
// function of its argument, and losing its *low* bits would put every key in one
// bucket, so they are cut to the 53 bits a number holds rather than rounded.
// `lean_runtime_uint64_bigint.mjs` makes the other trade-off: nothing is cut at all.

/** `x` taken modulo `2^64`, exactly, and then back to a number. */
const wrapU64 = (x) => Number(BigInt.asUintN(64, BigInt(x)));

/** `x` cut to the 53 bits a JavaScript number holds exactly, keeping the low ones. */
const low53 = (x) => Number(BigInt.asUintN(64, BigInt(x)) & 0x1fffffffffffffn);

/** The shift distance Lean uses at 64 bits: the argument taken modulo 64. */
const shift64 = (b) => ((BigInt(b) % 64n) + 64n) % 64n;

const encoder = new TextEncoder();

/** `UInt64.ofNat`. */
export const $lean_uint64_of_nat = (n) => wrapU64(n);

/** `UInt64.div`: rounds down, and `a / 0` is `0`. */
export const $lean_uint64_div = (a, b) =>
  Number(b) === 0 ? 0 : wrapU64(BigInt(a) / BigInt(b));

/** `UInt64.neg`. */
export const $lean_uint64_neg = (a) => wrapU64(-BigInt(a));

/** `UInt64.add`. */
export const $lean_uint64_add = (a, b) => wrapU64(BigInt(a) + BigInt(b));
/** `UInt64.sub`. */
export const $lean_uint64_sub = (a, b) => wrapU64(BigInt(a) - BigInt(b));
/** `UInt64.mul`. */
export const $lean_uint64_mul = (a, b) => wrapU64(BigInt(a) * BigInt(b));

/** `UInt64.land`. */
export const $lean_uint64_land = (a, b) => wrapU64(BigInt(a) & BigInt(b));
/** `UInt64.lor`. */
export const $lean_uint64_lor = (a, b) => wrapU64(BigInt(a) | BigInt(b));
/** `UInt64.xor`. */
export const $lean_uint64_xor = (a, b) => wrapU64(BigInt(a) ^ BigInt(b));
/** `UInt64.complement`. */
export const $lean_uint64_complement = (a) => wrapU64(~BigInt(a));
/** `UInt64.shiftLeft`. */
export const $lean_uint64_shift_left = (a, b) => wrapU64(BigInt(a) << shift64(b));
/** `UInt64.shiftRight`; the shift is taken modulo 64, as Lean's is. */
export const $lean_uint64_shift_right = (a, b) => wrapU64(BigInt(a) >> shift64(b));

/**
 * `String.hash`.  Lean's own hash is not specified by the language, and nothing in a
 * compiled program may depend on its value — only on its being a function of the
 * string.  This is FNV-1a over the UTF-8 bytes, taken to 64 bits and then cut to the
 * 53 a number holds.
 */
export const $lean_string_hash = (s) => {
  let h = 0xcbf29ce484222325n;
  for (const b of encoder.encode(s)) {
    h = BigInt.asUintN(64, (h ^ BigInt(b)) * 0x100000001b3n);
  }
  return low53(h);
};

/** `instHashableString`: a `Hashable` is its one method. */
export const instHashableString = (s) => $lean_string_hash(s);

/** `instHashableNat`. */
export const instHashableNat = (n) => low53(n);

==== FILE: runtime/lean_runtime_nat_num.mjs ====
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

==== FILE: runtime/lean_runtime_usize_num.mjs ====
// The runtime functions that answer with a `USize`, where a `USize` is a JavaScript
// number (`usizeRepr = num`).
//
// A `USize` is 64 bits wide and a number holds only 53 of them exactly, so the wrap is
// computed over `BigInt` and the answer is read back as a number: the arithmetic is
// exact modulo `2^64` and then rounded, which is the trade-off this representation
// makes.  `lean_runtime_usize_bigint.mjs` makes the other one.

/** `x` taken modulo `2^64`, exactly, and then back to a number. */
const wrapU64 = (x) => Number(BigInt.asUintN(64, BigInt(x)));

/** The shift distance Lean uses at 64 bits: the argument taken modulo 64. */
const shift64 = (b) => ((BigInt(b) % 64n) + 64n) % 64n;

/** `USize.ofNat`. */
export const $lean_usize_of_nat = (n) => wrapU64(n);

/**
 * `UInt64.toUSize`.  A `USize` is a number here, so the value is cut to the 53 bits a
 * number holds exactly — the *low* bits, which are the ones a hash bucket is masked
 * out of.
 */
export const $lean_uint64_to_usize = (a) =>
  Number(BigInt.asUintN(64, BigInt(a)) & 0x1fffffffffffffn);

/** `USize.div`: rounds down, and `a / 0` is `0`. */
export const $lean_usize_div = (a, b) =>
  Number(b) === 0 ? 0 : wrapU64(BigInt(a) / BigInt(b));

/** `USize.neg`. */
export const $lean_usize_neg = (a) => wrapU64(-BigInt(a));

/** `USize.add`. */
export const $lean_usize_add = (a, b) => wrapU64(BigInt(a) + BigInt(b));
/** `USize.sub`. */
export const $lean_usize_sub = (a, b) => wrapU64(BigInt(a) - BigInt(b));
/** `USize.mul`. */
export const $lean_usize_mul = (a, b) => wrapU64(BigInt(a) * BigInt(b));

/** `USize.land`. */
export const $lean_usize_land = (a, b) => wrapU64(BigInt(a) & BigInt(b));
/** `USize.lor`. */
export const $lean_usize_lor = (a, b) => wrapU64(BigInt(a) | BigInt(b));
/** `USize.xor`. */
export const $lean_usize_xor = (a, b) => wrapU64(BigInt(a) ^ BigInt(b));
/** `USize.complement`. */
export const $lean_usize_complement = (a) => wrapU64(~BigInt(a));
/** `USize.shiftLeft`. */
export const $lean_usize_shift_left = (a, b) => wrapU64(BigInt(a) << shift64(b));
/** `USize.shiftRight`; the value is unsigned, so the shift brings in zeros. */
export const $lean_usize_shift_right = (a, b) => wrapU64(BigInt(a) >> shift64(b));
