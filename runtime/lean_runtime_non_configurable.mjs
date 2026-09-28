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

const $utf8At = (s, p) => {
  let off = 0;
  for (const ch of s) {
    const cp = ch.codePointAt(0);
    const n = cp < 128 ? 1 : cp < 2048 ? 2 : cp < 65536 ? 3 : 4;
    if (off === p) {
      return [ch, n];
    }
    if (off > p) {
      return undefined;
    }
    off = off + n;
  }
  return undefined;
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

const $utf8Extract = (s, b, e) => {
  if (b >= e) {
    return "";
  }
  let off = 0;
  let out = "";
  let started = false;
  for (const ch of s) {
    if (!started && off === b) {
      started = true;
    }
    if (started) {
      if (off === e) {
        return out;
      }
      out = out + ch;
    }
    const cp = ch.codePointAt(0);
    off = off + (cp < 128 ? 1 : cp < 2048 ? 2 : cp < 65536 ? 3 : 4);
  }
  return out;
};

const $utf8Set = (s, p, c) => {
  let off = 0;
  let i = 0;
  for (const ch of s) {
    if (off === p) {
      return s.slice(0, i) + c + s.slice(i + ch.length);
    }
    const cp = ch.codePointAt(0);
    off = off + (cp < 128 ? 1 : cp < 2048 ? 2 : cp < 65536 ? 3 : 4);
    i = i + ch.length;
  }
  return s;
};

/* ----------------------------------------------------- imported by the backend */

/** `Char.ofNatAux`. */
export const Char_ofNatAux = (a) => String.fromCodePoint(Number(a));

/** `Bool.toInt16`. */
export const $lean_bool_to_int16 = (a) => a ? 1 : 0;

/** `Bool.toInt32`. */
export const $lean_bool_to_int32 = (a) => a ? 1 : 0;

/** `Bool.toInt8`. */
export const $lean_bool_to_int8 = (a) => a ? 1 : 0;

/** `Bool.toUInt16`. */
export const $lean_bool_to_uint16 = (a) => a ? 1 : 0;

/** `Bool.toUInt32`. */
export const $lean_bool_to_uint32 = (a) => a ? 1 : 0;

/** `Bool.toUInt8`. */
export const $lean_bool_to_uint8 = (a) => a ? 1 : 0;

/** `Float32.add`. */
export const $lean_float32_add = (a, b) => Math.fround(a + b);

/** `Float32.beq`. */
export const $lean_float32_beq = (a, b) => a === b;

/** `Float32.le`, `Float32.decLe`. */
export const $lean_float32_decLe = (a, b) => a <= b;

/** `Float32.lt`, `Float32.decLt`. */
export const $lean_float32_decLt = (a, b) => a < b;

/** `Float32.div`. */
export const $lean_float32_div = (a, b) => Math.fround(a / b);

/** `Float32.isFinite`. */
export const $lean_float32_isfinite = (a) => Number.isFinite(a);

/** `Float32.isInf`. */
export const $lean_float32_isinf = (a) => a === Infinity || a === -Infinity;

/** `Float32.isNaN`. */
export const $lean_float32_isnan = (a) => Number.isNaN(a);

/** `Float32.mul`. */
export const $lean_float32_mul = (a, b) => Math.fround(a * b);

/** `Float32.neg`. */
export const $lean_float32_negate = (a) => -a;

/** `Float32.sub`. */
export const $lean_float32_sub = (a, b) => Math.fround(a - b);

/** `Float.isFinite`. */
export const $lean_float_isfinite = (a) => Number.isFinite(a);

/** `Float.isInf`. */
export const $lean_float_isinf = (a) => a === Infinity || a === -Infinity;

/** `Float.isNaN`. */
export const $lean_float_isnan = (a) => Number.isNaN(a);

/** `Float.neg`. */
export const $lean_float_negate = (a) => -a;

/** `Float.toFloat32`. */
export const $lean_float_to_float32 = (a) => Math.fround(a);

/** `Int16.abs`. */
export const $lean_int16_abs = (a) => (Math.abs(a) << 16) >> 16;

/** `Int16.add`. */
export const $lean_int16_add = (a, b) => ((a + b) << 16) >> 16;

/** `Int16.complement`. */
export const $lean_int16_complement = (a) => (~a << 16) >> 16;

/** `Int16.div`. */
export const $lean_int16_div = (a, b) => b === 0 ? 0 : (Math.trunc(a / b) << 16) >> 16;

/** `Int16.land`. */
export const $lean_int16_land = (a, b) => ((a & b) << 16) >> 16;

/** `Int16.lor`. */
export const $lean_int16_lor = (a, b) => ((a | b) << 16) >> 16;

/** `Int16.mod`. */
export const $lean_int16_mod = (a, b) => b === 0 ? a : a % b;

/** `Int16.mul`. */
export const $lean_int16_mul = (a, b) => ((a * b) << 16) >> 16;

/** `Int16.neg`. */
export const $lean_int16_neg = (a) => (-a << 16) >> 16;

/** `Int16.ofInt`: the argument may be a `BigInt` or a number. */
export const $lean_int16_of_int = (a) =>
  typeof a === "bigint" ? Number(BigInt.asIntN(16, a)) : (a << 16) >> 16;

/** `Int16.ofNat`: the argument may be a `BigInt` or a number. */
export const $lean_int16_of_nat = (a) =>
  typeof a === "bigint" ? Number(BigInt.asIntN(16, a)) : (a << 16) >> 16;

/** `Int16.shiftLeft`. */
export const $lean_int16_shift_left = (a, b) => ((a << (((b % 16) + 16) % 16)) << 16) >> 16;

/** `Int16.shiftRight`. */
export const $lean_int16_shift_right = (a, b) => a >> (((b % 16) + 16) % 16);

/** `Int16.sub`. */
export const $lean_int16_sub = (a, b) => ((a - b) << 16) >> 16;

/** `Int16.toInt8`. */
export const $lean_int16_to_int8 = (a) => (a << 24) >> 24;

/** `Int16.xor`. */
export const $lean_int16_xor = (a, b) => ((a ^ b) << 16) >> 16;

/** `Int32.abs`. */
export const $lean_int32_abs = (a) => Math.abs(a) | 0;

/** `Int32.add`. */
export const $lean_int32_add = (a, b) => (a + b) | 0;

/** `Int32.complement`. */
export const $lean_int32_complement = (a) => ~a | 0;

/** `Int32.div`. */
export const $lean_int32_div = (a, b) => b === 0 ? 0 : Math.trunc(a / b) | 0;

/** `Int32.land`. */
export const $lean_int32_land = (a, b) => (a & b) | 0;

/** `Int32.lor`. */
export const $lean_int32_lor = (a, b) => a | b | 0;

/** `Int32.mod`. */
export const $lean_int32_mod = (a, b) => b === 0 ? a : a % b;

/** `Int32.mul`. */
export const $lean_int32_mul = (a, b) => Math.imul(a, b) | 0;

/** `Int32.neg`. */
export const $lean_int32_neg = (a) => -a | 0;

/** `Int32.ofInt`: the argument may be a `BigInt` or a number. */
export const $lean_int32_of_int = (a) =>
  typeof a === "bigint" ? Number(BigInt.asIntN(32, a)) : a | 0;

/** `Int32.ofNat`: the argument may be a `BigInt` or a number. */
export const $lean_int32_of_nat = (a) =>
  typeof a === "bigint" ? Number(BigInt.asIntN(32, a)) : a | 0;

/** `Int32.shiftLeft`. */
export const $lean_int32_shift_left = (a, b) => (a << (((b % 32) + 32) % 32)) | 0;

/** `Int32.shiftRight`. */
export const $lean_int32_shift_right = (a, b) => a >> (((b % 32) + 32) % 32);

/** `Int32.sub`. */
export const $lean_int32_sub = (a, b) => (a - b) | 0;

/** `Int32.toInt16`. */
export const $lean_int32_to_int16 = (a) => (a << 16) >> 16;

/** `Int32.toInt8`. */
export const $lean_int32_to_int8 = (a) => (a << 24) >> 24;

/** `Int32.xor`. */
export const $lean_int32_xor = (a, b) => (a ^ b) | 0;

/** `Int64.toFloat`. */
export const $lean_int64_to_float = (a) => Number(a);

/** `Int64.toFloat32`. */
export const $lean_int64_to_float32 = (a) => Number(a);

/** `Int64.toInt16`. */
export const $lean_int64_to_int16 = (a) => Number(BigInt.asIntN(16, BigInt(a)));

/** `Int64.toInt32`. */
export const $lean_int64_to_int32 = (a) => Number(BigInt.asIntN(32, BigInt(a)));

/** `Int64.toInt8`. */
export const $lean_int64_to_int8 = (a) => Number(BigInt.asIntN(8, BigInt(a)));

/** `Int8.abs`. */
export const $lean_int8_abs = (a) => (Math.abs(a) << 24) >> 24;

/** `Int8.add`. */
export const $lean_int8_add = (a, b) => ((a + b) << 24) >> 24;

/** `Int8.complement`. */
export const $lean_int8_complement = (a) => (~a << 24) >> 24;

/** `Int8.div`. */
export const $lean_int8_div = (a, b) => b === 0 ? 0 : (Math.trunc(a / b) << 24) >> 24;

/** `Int8.land`. */
export const $lean_int8_land = (a, b) => ((a & b) << 24) >> 24;

/** `Int8.lor`. */
export const $lean_int8_lor = (a, b) => ((a | b) << 24) >> 24;

/** `Int8.mod`. */
export const $lean_int8_mod = (a, b) => b === 0 ? a : a % b;

/** `Int8.mul`. */
export const $lean_int8_mul = (a, b) => ((a * b) << 24) >> 24;

/** `Int8.neg`. */
export const $lean_int8_neg = (a) => (-a << 24) >> 24;

/** `Int8.ofInt`: the argument may be a `BigInt` or a number. */
export const $lean_int8_of_int = (a) =>
  typeof a === "bigint" ? Number(BigInt.asIntN(8, a)) : (a << 24) >> 24;

/** `Int8.ofNat`: the argument may be a `BigInt` or a number. */
export const $lean_int8_of_nat = (a) =>
  typeof a === "bigint" ? Number(BigInt.asIntN(8, a)) : (a << 24) >> 24;

/** `Int8.shiftLeft`. */
export const $lean_int8_shift_left = (a, b) => ((a << (((b % 8) + 8) % 8)) << 24) >> 24;

/** `Int8.shiftRight`. */
export const $lean_int8_shift_right = (a, b) => a >> (((b % 8) + 8) % 8);

/** `Int8.sub`. */
export const $lean_int8_sub = (a, b) => ((a - b) << 24) >> 24;

/** `Int8.xor`. */
export const $lean_int8_xor = (a, b) => ((a ^ b) << 24) >> 24;

/** `Int.decNonneg`: the argument may be a `BigInt` or a number. */
export const $lean_int_dec_nonneg = (a) => a >= 0;

/** `String.compare`. */
export const $lean_string_compare = (a, b) => a < b ? -1 : a === b ? 0 : 1;

/** `String.data`, `String.toList`. */
export const $lean_string_data = (a) => [...a];

/** `String.decidableLT`. */
export const $lean_string_dec_lt = (a, b) => a < b;

/** `String.Internal.isEmpty`. */
export const $lean_string_isempty = (a) => a.length === 0;

/** `String.ofList`, `String.mk`. */
export const $lean_string_mk = (a) => a.join("");

/** `String.Internal.pushn`: the count may be a `BigInt` or a number. */
export const $lean_string_pushn = (a, b, c) =>
  a + b.repeat(typeof c === "bigint" ? $toNum53(c) : c);

/** `String.Internal.atEnd`, `String.atEnd`, `String.Pos.Raw.atEnd`. */
export const $lean_string_utf8_at_end = (a, b) => b >= $utf8(a).length;

/** `String.Internal.extract`, `String.Pos.Raw.extract`. */
export const $lean_string_utf8_extract = (a, b, c) => $utf8Extract(a, b, c);

/** `String.Internal.get`, `String.Pos.Raw.get`, `String.get`. */
export const $lean_string_utf8_get = (a, b) => {
  const r = $utf8At(a, b);
  return r === undefined ? "A" : r[0];
};

/** `String.Internal.next`, `String.next`, `String.Pos.Raw.next`. */
export const $lean_string_utf8_next = (a, b) => {
  const r = $utf8At(a, b);
  return r === undefined ? b + 1 : b + r[1];
};

/** `String.Pos.Raw.set`, `String.set`. */
export const $lean_string_utf8_set = (a, b, c) => $utf8Set(a, b, c);

/** `UInt16.add`. */
export const $lean_uint16_add = (a, b) => (a + b) & 65535;

/** `UInt16.complement`. */
export const $lean_uint16_complement = (a) => ~a & 65535;

/** `UInt16.div`. */
export const $lean_uint16_div = (a, b) => b === 0 ? 0 : Math.floor(a / b);

/** `UInt16.land`. */
export const $lean_uint16_land = (a, b) => a & b & 65535;

/** `UInt16.log2`. */
export const $lean_uint16_log2 = (a) => a === 0 ? 0 : 31 - Math.clz32(a);

/** `UInt16.lor`. */
export const $lean_uint16_lor = (a, b) => (a | b) & 65535;

/** `UInt16.mod`. */
export const $lean_uint16_mod = (a, b) => b === 0 ? a : a % b;

/** `UInt16.mul`. */
export const $lean_uint16_mul = (a, b) => (a * b) & 65535;

/** `UInt16.neg`. */
export const $lean_uint16_neg = (a) => -a & 65535;

/** `UInt16.ofNat`, `UInt16.ofNatLT`: the argument may be a `BigInt` or a number. */
export const $lean_uint16_of_nat = (a) =>
  typeof a === "bigint" ? Number(BigInt.asUintN(16, a)) : ((a % 65536) + 65536) % 65536;

/** `UInt16.shiftLeft`. */
export const $lean_uint16_shift_left = (a, b) => (a << (((b % 16) + 16) % 16)) & 65535;

/** `UInt16.shiftRight`. */
export const $lean_uint16_shift_right = (a, b) => a >>> (b % 16);

/** `UInt16.sub`. */
export const $lean_uint16_sub = (a, b) => (a - b) & 65535;

/** `UInt16.toUInt8`. */
export const $lean_uint16_to_uint8 = (a) => a & 255;

/** `UInt16.xor`. */
export const $lean_uint16_xor = (a, b) => (a ^ b) & 65535;

/** `UInt32.add`. */
export const $lean_uint32_add = (a, b) => (a + b) >>> 0;

/** `UInt32.complement`. */
export const $lean_uint32_complement = (a) => ~a >>> 0;

/** `UInt32.div`. */
export const $lean_uint32_div = (a, b) => b === 0 ? 0 : Math.floor(a / b);

/** `UInt32.land`. */
export const $lean_uint32_land = (a, b) => (a & b) >>> 0;

/** `UInt32.log2`. */
export const $lean_uint32_log2 = (a) => a === 0 ? 0 : 31 - Math.clz32(a);

/** `UInt32.lor`. */
export const $lean_uint32_lor = (a, b) => (a | b) >>> 0;

/** `UInt32.mod`. */
export const $lean_uint32_mod = (a, b) => b === 0 ? a : a % b;

/** `UInt32.mul`. */
export const $lean_uint32_mul = (a, b) => Math.imul(a, b) >>> 0;

/** `UInt32.neg`. */
export const $lean_uint32_neg = (a) => -a >>> 0;

/** `UInt32.ofNat`, `UInt32.ofNatLT`: the argument may be a `BigInt` or a number. */
export const $lean_uint32_of_nat = (a) =>
  typeof a === "bigint" ? Number(BigInt.asUintN(32, a)) : ((a % 4294967296) + 4294967296) % 4294967296;

/** `UInt32.shiftLeft`. */
export const $lean_uint32_shift_left = (a, b) => (a << (((b % 32) + 32) % 32)) >>> 0;

/** `UInt32.shiftRight`. */
export const $lean_uint32_shift_right = (a, b) => a >>> (b % 32);

/** `UInt32.sub`. */
export const $lean_uint32_sub = (a, b) => (a - b) >>> 0;

/** `UInt32.toUInt16`. */
export const $lean_uint32_to_uint16 = (a) => a & 65535;

/** `UInt32.toUInt8`. */
export const $lean_uint32_to_uint8 = (a) => a & 255;

/** `UInt32.xor`. */
export const $lean_uint32_xor = (a, b) => (a ^ b) >>> 0;

/** `UInt64.toFloat`. */
export const $lean_uint64_to_float = (a) => Number(a);

/** `UInt64.toFloat32`. */
export const $lean_uint64_to_float32 = (a) => Number(a);

/** `UInt64.toUInt16`. */
export const $lean_uint64_to_uint16 = (a) => Number(BigInt.asUintN(16, BigInt(a)));

/** `UInt64.toUInt32`. */
export const $lean_uint64_to_uint32 = (a) => Number(BigInt.asUintN(32, BigInt(a)));

/** `UInt64.toUInt8`. */
export const $lean_uint64_to_uint8 = (a) => Number(BigInt.asUintN(8, BigInt(a)));

/** `UInt8.add`. */
export const $lean_uint8_add = (a, b) => (a + b) & 255;

/** `UInt8.complement`. */
export const $lean_uint8_complement = (a) => ~a & 255;

/** `UInt8.div`. */
export const $lean_uint8_div = (a, b) => b === 0 ? 0 : Math.floor(a / b);

/** `UInt8.land`. */
export const $lean_uint8_land = (a, b) => a & b & 255;

/** `UInt8.log2`. */
export const $lean_uint8_log2 = (a) => a === 0 ? 0 : 31 - Math.clz32(a);

/** `UInt8.lor`. */
export const $lean_uint8_lor = (a, b) => (a | b) & 255;

/** `UInt8.mod`. */
export const $lean_uint8_mod = (a, b) => b === 0 ? a : a % b;

/** `UInt8.mul`. */
export const $lean_uint8_mul = (a, b) => (a * b) & 255;

/** `UInt8.neg`. */
export const $lean_uint8_neg = (a) => -a & 255;

/** `UInt8.ofNat`, `UInt8.ofNatLT`: the argument may be a `BigInt` or a number. */
export const $lean_uint8_of_nat = (a) =>
  typeof a === "bigint" ? Number(BigInt.asUintN(8, a)) : ((a % 256) + 256) % 256;

/** `UInt8.shiftLeft`. */
export const $lean_uint8_shift_left = (a, b) => (a << (((b % 8) + 8) % 8)) & 255;

/** `UInt8.shiftRight`. */
export const $lean_uint8_shift_right = (a, b) => a >>> (b % 8);

/** `UInt8.sub`. */
export const $lean_uint8_sub = (a, b) => (a - b) & 255;

/** `UInt8.xor`. */
export const $lean_uint8_xor = (a, b) => (a ^ b) & 255;

/* ------------------------------------------------------------------------ arrays
 *
 * An array is a generic JavaScript `Array` or, where the configuration says so, a typed
 * array (`Uint8Array`, `Float64Array`, `BigUint64Array`, …).  An index or a count is a
 * `Nat`, so it is a `BigInt` or a number depending on `natRepr`: every function here
 * takes either.
 *
 * The functions without a suffix never mutate their argument: they answer with a copy.
 * The `_inplace` ones mutate it and answer with it; the backend calls them only on an
 * array nothing else refers to (one it has just built, and does not read again), where
 * the copy would be wasted work.
 */

/**
 * An index held as a `Nat`, as a number: a `BigInt` too large for a number becomes
 * `Infinity`, which is out of bounds of every array.
 */
const $idx = (i) =>
  typeof i === "bigint" ? (i > 9007199254740991n ? Infinity : Number(i)) : i;

/** A count held as a `Nat`, as a number (one too large for a number throws). */
const $count = (n) => (typeof n === "bigint" ? $toNum53(n) : n);

/** `Array.replicate`, on a generic array. */
export const $lean_mk_array = (n, v) => new Array($count(n)).fill(v);

/** `Array.replicate`, on the typed array of constructor `C` (`Uint8Array`, …). */
export const $lean_mk_typed_array = (C, n, v) => new C($count(n)).fill(v);

/** `Array.get!Internal`: `a[i]`, or the default `d` out of bounds. */
export const $lean_array_get = (d, a, i) => {
  const k = $idx(i);
  return k < a.length ? a[k] : d;
};

/** `Array.get!InternalBorrowed`: the same as `Array.get!Internal`. */
export const $lean_array_get_borrowed = $lean_array_get;

/** `Array.push`: a copy with one more element. */
export const $lean_array_push = (a, x) => {
  if (Array.isArray(a)) return [...a, x];
  const r = new a.constructor(a.length + 1);
  r.set(a);
  r[a.length] = x;
  return r;
};

/** `Array.push`, in place (a typed array cannot grow, so it is copied). */
export const $lean_array_push_inplace = (a, x) => {
  if (!Array.isArray(a)) return $lean_array_push(a, x);
  a.push(x);
  return a;
};

/** `Array.set!`: a copy with one element replaced (the array itself out of bounds). */
export const $lean_array_set = (a, i, x) => {
  const k = $idx(i);
  if (k >= a.length) return a;
  const r = a.slice();
  r[k] = x;
  return r;
};

/** `Array.set`: the same as `Array.set!` (the proof of the bound is erased). */
export const $lean_array_fset = $lean_array_set;

/** `Array.set!`, in place. */
export const $lean_array_set_inplace = (a, i, x) => {
  const k = $idx(i);
  if (k < a.length) a[k] = x;
  return a;
};

/** `Array.swapIfInBounds`: a copy with two elements swapped (the array itself out of bounds). */
export const $lean_array_swap = (a, i, j) => {
  const k = $idx(i);
  const l = $idx(j);
  if (k >= a.length || l >= a.length) return a;
  const r = a.slice();
  const t = r[k];
  r[k] = r[l];
  r[l] = t;
  return r;
};

/** `Array.swap`: the same as `Array.swapIfInBounds` (the proofs of the bounds are erased). */
export const $lean_array_fswap = $lean_array_swap;

/** `Array.swapIfInBounds`, in place. */
export const $lean_array_swap_inplace = (a, i, j) => {
  const k = $idx(i);
  const l = $idx(j);
  if (k < a.length && l < a.length) {
    const t = a[k];
    a[k] = a[l];
    a[l] = t;
  }
  return a;
};

/** `Array.pop`: a copy without the last element. */
export const $lean_array_pop = (a) => a.slice(0, Math.max(a.length - 1, 0));

/** `Array.pop`, in place (a typed array cannot shrink, so it is copied). */
export const $lean_array_pop_inplace = (a) => {
  if (!Array.isArray(a)) return $lean_array_pop(a);
  a.pop();
  return a;
};

/**
 * `Array.mk`: the array of a `List`.  A list is a JavaScript array too, so this is a
 * copy (arrays and lists are never shared, so the backend may mutate the array).
 */
export const $lean_array_mk = (xs) => xs.slice();

/** `Array.toList`: the list of an array, generic or typed (a list is a generic array). */
export const $lean_array_to_list = (a) => Array.from(a);

/* ------------------------------------------------------------------------ thunks */

/** `Thunk.pure`: a memoised delay whose value is already known. */
export const $lean_thunk_pure = (v) => ({ f: undefined, v, done: true });

/** `Thunk.mk`: a memoised delay of the function `f`. */
export const $lean_mk_thunk = (f) => ({ f, v: undefined, done: false });

/** `Thunk.get`: the value of a memoised delay, computed the first time. */
export const $lean_thunk_get_own = (t) => {
  if (!t.done) {
    t.v = t.f();
    t.done = true;
    t.f = undefined;
  }
  return t.v;
};

/* ------------------------------------------------------------ missing externs */

/** Called in place of an extern that has no JavaScript implementation yet. */
export const $lean_extern_unimplemented = (name) => {
  throw new Error(`LeanScript: the extern ${name} has no JavaScript implementation yet`);
};

/* -------------------------------------- not imported by the current backend */

/** `Array.uget`. */
export const $lean_array_uget = (a, i) => a[Number(i)];

/** `Array.uset`: persistent, so it answers with a copy. */
export const $lean_array_uset = (a, i, v) => {
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

/* ------------------------------------------ the narrow bitwise operations
 *
 * Lean takes the shift distance of a `w`-bit type modulo `w` (a negative distance
 * counts from the top), and the answer is the `w`-bit pattern.  The work goes through
 * `BigInt`, which is exact at every width, and comes back as the number the type is
 * held as.
 */

/** The shift distance Lean uses at `w` bits: the argument taken modulo `w`. */

/** An unsigned `w`-bit answer, out of the `BigInt` that computed it. */

/** A signed `w`-bit answer, out of the `BigInt` that computed it. */

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
