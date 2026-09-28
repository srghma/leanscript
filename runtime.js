// The runtime of the JavaScript that LeanScript generates: one module.
//
// Every function exported here is an operation of `JsTerm/OpsImported.lean`, of the same
// name: the name of the extern it implements, behind the JavaScript representation of its
// arguments and result (`bigint_nat__lean_nat_div` on `BigInt`s, `uint53__lean_nat_div`
// on numbers below 2^53; see `scripts/gen_js_ops.py` for the naming).  A generated module
// imports the operations it calls.  The operations that are one JavaScript operator are
// not here: they are written inline (`JsTerm/OpsInlined.lean`).
//
// Every function is pure (it never mutates an argument), except the `_inplace` array
// updates, which the backend calls only on an array nothing else refers to.

/* ------------------------------------------------------------ private helpers */

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

/**
 * An index held as a `Nat`, as a number: a `BigInt` too large for a number becomes
 * `Infinity`, which is out of bounds of every array.
 */
const $idx = (i) =>
  typeof i === "bigint" ? (i > 9007199254740991n ? Infinity : Number(i)) : i;

/** A count held as a `Nat`, as a number (one too large for a number throws). */
const $count = (n) => (typeof n === "bigint" ? $toNum53(n) : n);

const encoder = new TextEncoder();

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

const $chk53 = (x) => {
  if (!Number.isSafeInteger(x)) {
    throw new RangeError(
      "LeanScript: integer overflow: the result does not fit in a number (use the bigint representation)",
    );
  }
  return x;
};

/** `x` taken modulo `2^64`. */
const U64 = (x) => BigInt.asUintN(64, BigInt(x));

/** `x` cut to the 53 bits a JavaScript number holds exactly, keeping the low ones. */
const low53 = (x) => Number(BigInt.asUintN(64, BigInt(x)) & 0x1fffffffffffffn);

/* ------------------------------------------------------------ non_configurable */

/** `Array.pop`: a copy without the last element. */
export const array__lean_array_pop = (a) => a.slice(0, Math.max(a.length - 1, 0));

/** `Array.pop`, in place (a typed array cannot shrink, so it is copied). */
export const array__lean_array_pop_inplace = (a) => {
  if (!Array.isArray(a)) return array__lean_array_pop(a);
  a.pop();
  return a;
};

/** `Array.push`: a copy with one more element. */
export const array__lean_array_push = (a, x) => {
  if (Array.isArray(a)) return [...a, x];
  const r = new a.constructor(a.length + 1);
  r.set(a);
  r[a.length] = x;
  return r;
};

/** `Array.push`, in place (a typed array cannot grow, so it is copied). */
export const array__lean_array_push_inplace = (a, x) => {
  if (!Array.isArray(a)) return array__lean_array_push(a, x);
  a.push(x);
  return a;
};

/** `Int16.ofInt`: the argument may be a `BigInt` or a number. */
export const bigint_int__lean_int16_of_int = (a) =>
  typeof a === "bigint" ? Number(BigInt.asIntN(16, a)) : (a << 16) >> 16;

/** `Int32.ofInt`: the argument may be a `BigInt` or a number. */
export const bigint_int__lean_int32_of_int = (a) =>
  typeof a === "bigint" ? Number(BigInt.asIntN(32, a)) : a | 0;

/** `Int64.toInt16`. */
export const bigint_int__lean_int64_to_int16 = (a) => Number(BigInt.asIntN(16, BigInt(a)));

/** `Int64.toInt32`. */
export const bigint_int__lean_int64_to_int32 = (a) => Number(BigInt.asIntN(32, BigInt(a)));

/** `Int64.toInt8`. */
export const bigint_int__lean_int64_to_int8 = (a) => Number(BigInt.asIntN(8, BigInt(a)));

/** `Int8.ofInt`: the argument may be a `BigInt` or a number. */
export const bigint_int__lean_int8_of_int = (a) =>
  typeof a === "bigint" ? Number(BigInt.asIntN(8, a)) : (a << 24) >> 24;

/** `Array.set`: the same as `Array.set!` (the proof of the bound is erased). */

/** `Array.swap`: the same as `Array.swapIfInBounds` (the proofs of the bounds are erased). */

/** `Array.get!Internal`: `a[i]`, or the default `d` out of bounds. */
export const bigint_nat__lean_array_get = (d, a, i) => {
  const k = $idx(i);
  return k < a.length ? a[k] : d;
};

/** `Array.get!InternalBorrowed`: the same as `Array.get!Internal`. */

/** `Array.set!`: a copy with one element replaced (the array itself out of bounds). */
export const bigint_nat__lean_array_set = (a, i, x) => {
  const k = $idx(i);
  if (k >= a.length) return a;
  const r = a.slice();
  r[k] = x;
  return r;
};

/** `Array.set!`, in place. */
export const bigint_nat__lean_array_set_inplace = (a, i, x) => {
  const k = $idx(i);
  if (k < a.length) a[k] = x;
  return a;
};

/** `Array.swapIfInBounds`: a copy with two elements swapped (the array itself out of bounds). */
export const bigint_nat__lean_array_swap = (a, i, j) => {
  const k = $idx(i);
  const l = $idx(j);
  if (k >= a.length || l >= a.length) return a;
  const r = a.slice();
  const t = r[k];
  r[k] = r[l];
  r[l] = t;
  return r;
};

/** `Array.swapIfInBounds`, in place. */
export const bigint_nat__lean_array_swap_inplace = (a, i, j) => {
  const k = $idx(i);
  const l = $idx(j);
  if (k < a.length && l < a.length) {
    const t = a[k];
    a[k] = a[l];
    a[l] = t;
  }
  return a;
};

/** `Int16.ofNat`: the argument may be a `BigInt` or a number. */
export const bigint_nat__lean_int16_of_nat = (a) =>
  typeof a === "bigint" ? Number(BigInt.asIntN(16, a)) : (a << 16) >> 16;

/** `Int32.ofNat`: the argument may be a `BigInt` or a number. */
export const bigint_nat__lean_int32_of_nat = (a) =>
  typeof a === "bigint" ? Number(BigInt.asIntN(32, a)) : a | 0;

/** `Int8.ofNat`: the argument may be a `BigInt` or a number. */
export const bigint_nat__lean_int8_of_nat = (a) =>
  typeof a === "bigint" ? Number(BigInt.asIntN(8, a)) : (a << 24) >> 24;

/** `Array.replicate`, on a generic array. */
export const bigint_nat__lean_mk_array = (n, v) => new Array($count(n)).fill(v);

/** `String.Internal.pushn`: the count may be a `BigInt` or a number. */
export const bigint_nat__lean_string_pushn = (a, b, c) =>
  a + b.repeat(typeof c === "bigint" ? $toNum53(c) : c);

/** `UInt16.ofNat`, `UInt16.ofNatLT`: the argument may be a `BigInt` or a number. */
export const bigint_nat__lean_uint16_of_nat__UInt16_ofNat = (a) =>
  typeof a === "bigint" ? Number(BigInt.asUintN(16, a)) : ((a % 65536) + 65536) % 65536;

/** `Char.ofNatAux`. */
export const bigint_nat__lean_uint32_of_nat__Char_ofNatAux = (a) => String.fromCodePoint(Number(a));

/** `UInt32.ofNat`, `UInt32.ofNatLT`: the argument may be a `BigInt` or a number. */
export const bigint_nat__lean_uint32_of_nat__UInt32_ofNat = (a) =>
  typeof a === "bigint" ? Number(BigInt.asUintN(32, a)) : ((a % 4294967296) + 4294967296) % 4294967296;

/** `UInt64.toUInt16`. */
export const bigint_nat__lean_uint64_to_uint16 = (a) => Number(BigInt.asUintN(16, BigInt(a)));

/** `UInt64.toUInt32`. */
export const bigint_nat__lean_uint64_to_uint32 = (a) => Number(BigInt.asUintN(32, BigInt(a)));

/** `UInt64.toUInt8`. */
export const bigint_nat__lean_uint64_to_uint8 = (a) => Number(BigInt.asUintN(8, BigInt(a)));

/** `UInt8.ofNat`, `UInt8.ofNatLT`: the argument may be a `BigInt` or a number. */
export const bigint_nat__lean_uint8_of_nat__UInt8_ofNat = (a) =>
  typeof a === "bigint" ? Number(BigInt.asUintN(8, a)) : ((a % 256) + 256) % 256;

/** `Bool.toInt16`. */
export const bool__lean_bool_to_int16 = (a) => a ? 1 : 0;

/** `Bool.toInt32`. */
export const bool__lean_bool_to_int32 = (a) => a ? 1 : 0;

/** `Bool.toInt8`. */
export const bool__lean_bool_to_int8 = (a) => a ? 1 : 0;

/** `Bool.toUInt16`. */
export const bool__lean_bool_to_uint16 = (a) => a ? 1 : 0;

/** `Bool.toUInt32`. */
export const bool__lean_bool_to_uint32 = (a) => a ? 1 : 0;

/** `Bool.toUInt8`. */
export const bool__lean_bool_to_uint8 = (a) => a ? 1 : 0;

/** `Float32.add`. */
export const float32__lean_float32_add = (a, b) => Math.fround(a + b);

/** `Float32.div`. */
export const float32__lean_float32_div = (a, b) => Math.fround(a / b);

/** `Float32.isFinite`. */
export const float32__lean_float32_isfinite = (a) => Number.isFinite(a);

/** `Float32.isInf`. */
export const float32__lean_float32_isinf = (a) => a === Infinity || a === -Infinity;

/** `Float32.isNaN`. */
export const float32__lean_float32_isnan = (a) => Number.isNaN(a);

/** `Float32.mul`. */
export const float32__lean_float32_mul = (a, b) => Math.fround(a * b);

/** `Float32.sub`. */
export const float32__lean_float32_sub = (a, b) => Math.fround(a - b);

/** `Float.isFinite`. */
export const float__lean_float_isfinite = (a) => Number.isFinite(a);

/** `Float.isInf`. */
export const float__lean_float_isinf = (a) => a === Infinity || a === -Infinity;

/** `Float.isNaN`. */
export const float__lean_float_isnan = (a) => Number.isNaN(a);

/** `Float.toFloat32`. */
export const float__lean_float_to_float32 = (a) => Math.fround(a);

/** `Int16.abs`. */
export const int16__lean_int16_abs = (a) => (Math.abs(a) << 16) >> 16;

/** `Int16.add`. */
export const int16__lean_int16_add = (a, b) => ((a + b) << 16) >> 16;

/** `Int16.complement`. */
export const int16__lean_int16_complement = (a) => (~a << 16) >> 16;

/** `Int16.div`. */
export const int16__lean_int16_div = (a, b) => b === 0 ? 0 : (Math.trunc(a / b) << 16) >> 16;

/** `Int16.land`. */
export const int16__lean_int16_land = (a, b) => ((a & b) << 16) >> 16;

/** `Int16.lor`. */
export const int16__lean_int16_lor = (a, b) => ((a | b) << 16) >> 16;

/** `Int16.mod`. */
export const int16__lean_int16_mod = (a, b) => b === 0 ? a : a % b;

/** `Int16.mul`. */
export const int16__lean_int16_mul = (a, b) => ((a * b) << 16) >> 16;

/** `Int16.neg`. */
export const int16__lean_int16_neg = (a) => (-a << 16) >> 16;

/** `Int16.shiftLeft`. */
export const int16__lean_int16_shift_left = (a, b) => ((a << (((b % 16) + 16) % 16)) << 16) >> 16;

/** `Int16.shiftRight`. */
export const int16__lean_int16_shift_right = (a, b) => a >> (((b % 16) + 16) % 16);

/** `Int16.sub`. */
export const int16__lean_int16_sub = (a, b) => ((a - b) << 16) >> 16;

/** `Int16.toInt8`. */
export const int16__lean_int16_to_int8 = (a) => (a << 24) >> 24;

/** `Int16.xor`. */
export const int16__lean_int16_xor = (a, b) => ((a ^ b) << 16) >> 16;

/** `Int32.abs`. */
export const int32__lean_int32_abs = (a) => Math.abs(a) | 0;

/** `Int32.add`. */
export const int32__lean_int32_add = (a, b) => (a + b) | 0;

/** `Int32.complement`. */
export const int32__lean_int32_complement = (a) => ~a | 0;

/** `Int32.div`. */
export const int32__lean_int32_div = (a, b) => b === 0 ? 0 : Math.trunc(a / b) | 0;

/** `Int32.land`. */
export const int32__lean_int32_land = (a, b) => (a & b) | 0;

/** `Int32.lor`. */
export const int32__lean_int32_lor = (a, b) => a | b | 0;

/** `Int32.mod`. */
export const int32__lean_int32_mod = (a, b) => b === 0 ? a : a % b;

/** `Int32.mul`. */
export const int32__lean_int32_mul = (a, b) => Math.imul(a, b) | 0;

/** `Int32.neg`. */
export const int32__lean_int32_neg = (a) => -a | 0;

/** `Int32.shiftLeft`. */
export const int32__lean_int32_shift_left = (a, b) => (a << (((b % 32) + 32) % 32)) | 0;

/** `Int32.shiftRight`. */
export const int32__lean_int32_shift_right = (a, b) => a >> (((b % 32) + 32) % 32);

/** `Int32.sub`. */
export const int32__lean_int32_sub = (a, b) => (a - b) | 0;

/** `Int32.toInt16`. */
export const int32__lean_int32_to_int16 = (a) => (a << 16) >> 16;

/** `Int32.toInt8`. */
export const int32__lean_int32_to_int8 = (a) => (a << 24) >> 24;

/** `Int32.xor`. */
export const int32__lean_int32_xor = (a, b) => (a ^ b) | 0;

/** `Int8.abs`. */
export const int8__lean_int8_abs = (a) => (Math.abs(a) << 24) >> 24;

/** `Int8.add`. */
export const int8__lean_int8_add = (a, b) => ((a + b) << 24) >> 24;

/** `Int8.complement`. */
export const int8__lean_int8_complement = (a) => (~a << 24) >> 24;

/** `Int8.div`. */
export const int8__lean_int8_div = (a, b) => b === 0 ? 0 : (Math.trunc(a / b) << 24) >> 24;

/** `Int8.land`. */
export const int8__lean_int8_land = (a, b) => ((a & b) << 24) >> 24;

/** `Int8.lor`. */
export const int8__lean_int8_lor = (a, b) => ((a | b) << 24) >> 24;

/** `Int8.mod`. */
export const int8__lean_int8_mod = (a, b) => b === 0 ? a : a % b;

/** `Int8.mul`. */
export const int8__lean_int8_mul = (a, b) => ((a * b) << 24) >> 24;

/** `Int8.neg`. */
export const int8__lean_int8_neg = (a) => (-a << 24) >> 24;

/** `Int8.shiftLeft`. */
export const int8__lean_int8_shift_left = (a, b) => ((a << (((b % 8) + 8) % 8)) << 24) >> 24;

/** `Int8.shiftRight`. */
export const int8__lean_int8_shift_right = (a, b) => a >> (((b % 8) + 8) % 8);

/** `Int8.sub`. */
export const int8__lean_int8_sub = (a, b) => ((a - b) << 24) >> 24;

/** `Int8.xor`. */
export const int8__lean_int8_xor = (a, b) => ((a ^ b) << 24) >> 24;

/** `String.compare`. */
export const string__lean_string_compare = (a, b) => a < b ? -1 : a === b ? 0 : 1;

/** `String.data`, `String.toList`. */
export const string__lean_string_data__String_data = (a) => [...a];

/** `String.Internal.isEmpty`. */
export const string__lean_string_isempty = (a) => a.length === 0;

/**
 * `String.Slice.Pattern.Internal.memcmpStr`: are the `len` bytes of `lhs` at `lstart`
 * the same as the `len` bytes of `rhs` at `rstart`?
 */
export const string__lean_string_memcmp = (lhs, rhs, lstart, rstart, len) => {
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

/** `String.ofList`, `String.mk`. */
export const string__lean_string_mk__String_mk = (a) => a.join("");

/** `String.Internal.atEnd`, `String.atEnd`, `String.Pos.Raw.atEnd`. */
export const string__lean_string_utf8_at_end__String_Internal_atEnd = (a, b) => b >= $utf8(a).length;

/** `String.Internal.extract`, `String.Pos.Raw.extract`. */
export const string__lean_string_utf8_extract__String_Internal_extract = (a, b, c) => $utf8Extract(a, b, c);

/** `String.Internal.get`, `String.Pos.Raw.get`, `String.get`. */
export const string__lean_string_utf8_get__String_Internal_get = (a, b) => {
  const r = $utf8At(a, b);
  return r === undefined ? "A" : r[0];
};

/** `String.Internal.next`, `String.next`, `String.Pos.Raw.next`. */
export const string__lean_string_utf8_next__String_Internal_next = (a, b) => {
  const r = $utf8At(a, b);
  return r === undefined ? b + 1 : b + r[1];
};

/** `String.Pos.Raw.set`, `String.set`. */
export const string__lean_string_utf8_set__String_Pos_Raw_set = (a, b, c) => $utf8Set(a, b, c);

/** `Thunk.mk`: a memoised delay of the function `f`. */
export const thunk__lean_mk_thunk = (f) => ({ f, v: undefined, done: false });

/** `Thunk.get`: the value of a memoised delay, computed the first time. */
export const thunk__lean_thunk_get_own = (t) => {
  if (!t.done) {
    t.v = t.f();
    t.done = true;
    t.f = undefined;
  }
  return t.v;
};

/** `Thunk.pure`: a memoised delay whose value is already known. */
export const thunk__lean_thunk_pure = (v) => ({ f: undefined, v, done: true });

/** `Array.replicate`, on the typed array of constructor `C` (`Uint8Array`, …). */
export const typedArray__bigint_nat__lean_mk_array = (C, n, v) => new C($count(n)).fill(v);

/** `Array.toList`: the list of an array, generic or typed (a list is a generic array). */
export const typedArray__lean_array_to_list = (a) => Array.from(a);

/** `Array.replicate`, on the typed array of constructor `C` (`Uint8Array`, …). */
export const typedArray__uint53__lean_mk_array = (C, n, v) => new C(n).fill(v);

/** `UInt16.add`. */
export const uint16__lean_uint16_add = (a, b) => (a + b) & 65535;

/** `UInt16.complement`. */
export const uint16__lean_uint16_complement = (a) => ~a & 65535;

/** `UInt16.div`. */
export const uint16__lean_uint16_div = (a, b) => b === 0 ? 0 : Math.floor(a / b);

/** `UInt16.land`. */
export const uint16__lean_uint16_land = (a, b) => a & b & 65535;

/** `UInt16.log2`. */
export const uint16__lean_uint16_log2 = (a) => a === 0 ? 0 : 31 - Math.clz32(a);

/** `UInt16.lor`. */
export const uint16__lean_uint16_lor = (a, b) => (a | b) & 65535;

/** `UInt16.mod`. */
export const uint16__lean_uint16_mod = (a, b) => b === 0 ? a : a % b;

/** `UInt16.mul`. */
export const uint16__lean_uint16_mul = (a, b) => (a * b) & 65535;

/** `UInt16.neg`. */
export const uint16__lean_uint16_neg = (a) => -a & 65535;

/** `UInt16.shiftLeft`. */
export const uint16__lean_uint16_shift_left = (a, b) => (a << (((b % 16) + 16) % 16)) & 65535;

/** `UInt16.shiftRight`. */
export const uint16__lean_uint16_shift_right = (a, b) => a >>> (b % 16);

/** `UInt16.sub`. */
export const uint16__lean_uint16_sub = (a, b) => (a - b) & 65535;

/** `UInt16.toUInt8`. */
export const uint16__lean_uint16_to_uint8 = (a) => a & 255;

/** `UInt16.xor`. */
export const uint16__lean_uint16_xor = (a, b) => (a ^ b) & 65535;

/** `UInt32.add`. */
export const uint32__lean_uint32_add = (a, b) => (a + b) >>> 0;

/** `UInt32.complement`. */
export const uint32__lean_uint32_complement = (a) => ~a >>> 0;

/** `UInt32.div`. */
export const uint32__lean_uint32_div = (a, b) => b === 0 ? 0 : Math.floor(a / b);

/** `UInt32.land`. */
export const uint32__lean_uint32_land = (a, b) => (a & b) >>> 0;

/** `UInt32.log2`. */
export const uint32__lean_uint32_log2 = (a) => a === 0 ? 0 : 31 - Math.clz32(a);

/** `UInt32.lor`. */
export const uint32__lean_uint32_lor = (a, b) => (a | b) >>> 0;

/** `UInt32.mod`. */
export const uint32__lean_uint32_mod = (a, b) => b === 0 ? a : a % b;

/** `UInt32.mul`. */
export const uint32__lean_uint32_mul = (a, b) => Math.imul(a, b) >>> 0;

/** `UInt32.neg`. */
export const uint32__lean_uint32_neg = (a) => -a >>> 0;

/** `UInt32.shiftLeft`. */
export const uint32__lean_uint32_shift_left = (a, b) => (a << (((b % 32) + 32) % 32)) >>> 0;

/** `UInt32.shiftRight`. */
export const uint32__lean_uint32_shift_right = (a, b) => a >>> (b % 32);

/** `UInt32.sub`. */
export const uint32__lean_uint32_sub = (a, b) => (a - b) >>> 0;

/** `UInt32.toUInt16`. */
export const uint32__lean_uint32_to_uint16 = (a) => a & 65535;

/** `UInt32.toUInt8`. */
export const uint32__lean_uint32_to_uint8 = (a) => a & 255;

/** `UInt32.xor`. */
export const uint32__lean_uint32_xor = (a, b) => (a ^ b) >>> 0;

/** `Array.set`: the same as `Array.set!` (the proof of the bound is erased). */

/** `Array.swap`: the same as `Array.swapIfInBounds` (the proofs of the bounds are erased). */

/** `Array.get!Internal`: `a[i]`, or the default `d` out of bounds. */
export const uint53__lean_array_get = (d, a, i) => {
  const k = i;
  return k < a.length ? a[k] : d;
};

/** `Array.get!InternalBorrowed`: the same as `Array.get!Internal`. */

/** `Array.set!`: a copy with one element replaced (the array itself out of bounds). */
export const uint53__lean_array_set = (a, i, x) => {
  const k = i;
  if (k >= a.length) return a;
  const r = a.slice();
  r[k] = x;
  return r;
};

/** `Array.set!`, in place. */
export const uint53__lean_array_set_inplace = (a, i, x) => {
  const k = i;
  if (k < a.length) a[k] = x;
  return a;
};

/** `Array.swapIfInBounds`: a copy with two elements swapped (the array itself out of bounds). */
export const uint53__lean_array_swap = (a, i, j) => {
  const k = i;
  const l = j;
  if (k >= a.length || l >= a.length) return a;
  const r = a.slice();
  const t = r[k];
  r[k] = r[l];
  r[l] = t;
  return r;
};

/** `Array.swapIfInBounds`, in place. */
export const uint53__lean_array_swap_inplace = (a, i, j) => {
  const k = i;
  const l = j;
  if (k < a.length && l < a.length) {
    const t = a[k];
    a[k] = a[l];
    a[l] = t;
  }
  return a;
};

/** `Int16.ofNat`: the argument may be a `BigInt` or a number. */
export const uint53__lean_int16_of_nat = (a) =>
  typeof a === "bigint" ? Number(BigInt.asIntN(16, a)) : (a << 16) >> 16;

/** `Int32.ofNat`: the argument may be a `BigInt` or a number. */
export const uint53__lean_int32_of_nat = (a) =>
  typeof a === "bigint" ? Number(BigInt.asIntN(32, a)) : a | 0;

/** `Int8.ofNat`: the argument may be a `BigInt` or a number. */
export const uint53__lean_int8_of_nat = (a) =>
  typeof a === "bigint" ? Number(BigInt.asIntN(8, a)) : (a << 24) >> 24;

/** `Array.replicate`, on a generic array. */
export const uint53__lean_mk_array = (n, v) => new Array(n).fill(v);

/** `String.Internal.pushn`: the count may be a `BigInt` or a number. */
export const uint53__lean_string_pushn = (a, b, c) =>
  a + b.repeat(typeof c === "bigint" ? $toNum53(c) : c);

/** `String.Pos.Raw.set`, `String.set`. */
export const uint53__lean_string_utf8_set__String_Pos_set = (a, b, c) => $utf8Set(a, b, c);

/** `UInt16.ofNat`, `UInt16.ofNatLT`: the argument may be a `BigInt` or a number. */
export const uint53__lean_uint16_of_nat__UInt16_ofNat = (a) =>
  typeof a === "bigint" ? Number(BigInt.asUintN(16, a)) : ((a % 65536) + 65536) % 65536;

/** `Char.ofNatAux`. */
export const uint53__lean_uint32_of_nat__Char_ofNatAux = (a) => String.fromCodePoint(Number(a));

/** `UInt32.ofNat`, `UInt32.ofNatLT`: the argument may be a `BigInt` or a number. */
export const uint53__lean_uint32_of_nat__UInt32_ofNat = (a) =>
  typeof a === "bigint" ? Number(BigInt.asUintN(32, a)) : ((a % 4294967296) + 4294967296) % 4294967296;

/** `UInt64.toUInt16`. */
export const uint53__lean_uint64_to_uint16 = (a) => Number(BigInt.asUintN(16, BigInt(a)));

/** `UInt64.toUInt32`. */
export const uint53__lean_uint64_to_uint32 = (a) => Number(BigInt.asUintN(32, BigInt(a)));

/** `UInt64.toUInt8`. */
export const uint53__lean_uint64_to_uint8 = (a) => Number(BigInt.asUintN(8, BigInt(a)));

/** `UInt8.ofNat`, `UInt8.ofNatLT`: the argument may be a `BigInt` or a number. */
export const uint53__lean_uint8_of_nat__UInt8_ofNat = (a) =>
  typeof a === "bigint" ? Number(BigInt.asUintN(8, a)) : ((a % 256) + 256) % 256;

/** `UInt8.add`. */
export const uint8__lean_uint8_add = (a, b) => (a + b) & 255;

/** `UInt8.complement`. */
export const uint8__lean_uint8_complement = (a) => ~a & 255;

/** `UInt8.div`. */
export const uint8__lean_uint8_div = (a, b) => b === 0 ? 0 : Math.floor(a / b);

/** `UInt8.land`. */
export const uint8__lean_uint8_land = (a, b) => a & b & 255;

/** `UInt8.log2`. */
export const uint8__lean_uint8_log2 = (a) => a === 0 ? 0 : 31 - Math.clz32(a);

/** `UInt8.lor`. */
export const uint8__lean_uint8_lor = (a, b) => (a | b) & 255;

/** `UInt8.mod`. */
export const uint8__lean_uint8_mod = (a, b) => b === 0 ? a : a % b;

/** `UInt8.mul`. */
export const uint8__lean_uint8_mul = (a, b) => (a * b) & 255;

/** `UInt8.neg`. */
export const uint8__lean_uint8_neg = (a) => -a & 255;

/** `UInt8.shiftLeft`. */
export const uint8__lean_uint8_shift_left = (a, b) => (a << (((b % 8) + 8) % 8)) & 255;

/** `UInt8.shiftRight`. */
export const uint8__lean_uint8_shift_right = (a, b) => a >>> (b % 8);

/** `UInt8.sub`. */
export const uint8__lean_uint8_sub = (a, b) => (a - b) & 255;

/** `UInt8.xor`. */
export const uint8__lean_uint8_xor = (a, b) => (a ^ b) & 255;

/* ------------------------------------------------------------ nat_bigint */

/** `Int.natAbs`. */
export const bigint_int__bigint_nat__lean_nat_abs = (a) => {
  a = BigInt(a);
  return a < 0n ? -a : a;
};

/** `Nat.div`. */
export const bigint_nat__lean_nat_div = (a, b) => b === 0n ? 0n : a / b;

/** `Nat.divExact`. */
export const bigint_nat__lean_nat_div_exact = (a, b) => b === 0n ? 0n : a / b;

/** `Nat.log2`. */
export const bigint_nat__lean_nat_log2 = (a) => a === 0n ? 0n : BigInt(a.toString(2).length - 1);

/** `Nat.modCore`, `Nat.mod`. */
export const bigint_nat__lean_nat_mod__Nat_mod = (a, b) => b === 0n ? a : a % b;

/** `Nat.pow`. */
export const bigint_nat__lean_nat_pow = (a, b) => $bigPow(a, b);

/** `Nat.pred`. */
export const bigint_nat__lean_nat_pred = (a) => a > 0n ? a - 1n : 0n;

/** `Nat.sub`. */
export const bigint_nat__lean_nat_sub = (a, b) => a > b ? a - b : 0n;

/** `String.Internal.length`, `String.length`. */
export const bigint_nat__lean_string_length__String_Internal_length = (a) => BigInt([...a].length);

/** `String.utf8ByteSize`. */
export const bigint_nat__lean_string_utf8_byte_size = (a) => BigInt($utf8(a).length);

/* ------------------------------------------------------------ nat_num */

/** `Int.natAbs`. */
export const bigint_int__uint53__lean_nat_abs = (a) =>
  typeof a === "bigint" ? $toNum53(a < 0n ? -a : a) : a < 0 ? -a : a;

/** `UInt64.toNat`: the argument may be a `BigInt` or a number. */
export const bigint_nat__uint53__lean_uint64_to_nat__UInt64_toNat = (a) => (typeof a === "bigint" ? $toNum53(a) : a);

/** `Nat.add`. */
export const uint53__lean_nat_add = (a, b) => $chk53(a + b);

/** `Nat.div`. */
export const uint53__lean_nat_div = (a, b) => b === 0 ? 0 : Math.floor(a / b);

/** `Nat.divExact`. */
export const uint53__lean_nat_div_exact = (a, b) => b === 0 ? 0 : Math.floor(a / b);

/** `Nat.land`. */
export const uint53__lean_nat_land = (a, b) => {
  // Fast path: both numbers fit in 32 bits (most common case in practice)
  if (a < 0x100000000 && b < 0x100000000) {
    return (a & b) >>> 0;
  }
  // 53-bit safe path: split into high 21 bits and low 32 bits
  const lo = (a & b) >>> 0;
  const hi = ((a / 0x100000000) | 0) & ((b / 0x100000000) | 0);
  return hi * 0x100000000 + lo;
};

/** `Nat.log2`. */
export const uint53__lean_nat_log2 = (a) => a === 0 ? 0 : a.toString(2).length - 1;

/** `Nat.lor`. */
export const uint53__lean_nat_lor = (a, b) => Number(BigInt(a) | BigInt(b));

/** `Nat.xor`. */
export const uint53__lean_nat_lxor = (a, b) => Number(BigInt(a) ^ BigInt(b));

/** `Nat.modCore`, `Nat.mod`. */
export const uint53__lean_nat_mod__Nat_mod = (a, b) => b === 0 ? a : a % b;

/** `Nat.mul`. */
export const uint53__lean_nat_mul = (a, b) => $chk53(a * b);

/** `Nat.pow`. */
export const uint53__lean_nat_pow = (a, b) => $chk53(Math.pow(a, b));

/** `Nat.pred`. */
export const uint53__lean_nat_pred = (a) => a > 0 ? a - 1 : 0;

/** `Nat.shiftLeft`. */
export const uint53__lean_nat_shiftl = (a, b) => $chk53(a * Math.pow(2, b));

/** `Nat.shiftRight`. */
export const uint53__lean_nat_shiftr = (a, b) => Math.floor(a / Math.pow(2, b));

/** `Nat.sub`. */
export const uint53__lean_nat_sub = (a, b) => a > b ? a - b : 0;

/** `String.Internal.length`, `String.length`. */
export const uint53__lean_string_length__String_Internal_length = (a) => [...a].length;

/** `String.utf8ByteSize`. */
export const uint53__lean_string_utf8_byte_size = (a) => $utf8(a).length;

/* ------------------------------------------------------------ int_bigint */

/** `Int.tdiv`. */
export const bigint_int__lean_int_div = (a, b) => b === 0n ? 0n : a / b;

/** `Int.divExact`. */
export const bigint_int__lean_int_div_exact = (a, b) =>
  b === 0n
  ? 0n
  : a % b < 0n
    ? b > 0n
      ? a / b - 1n
      : a / b + 1n
    : a / b;

/** `Int.ediv`. */
export const bigint_int__lean_int_ediv = (a, b) =>
  b === 0n
  ? 0n
  : a % b < 0n
    ? b > 0n
      ? a / b - 1n
      : a / b + 1n
    : a / b;

/** `Int.emod`. */
export const bigint_int__lean_int_emod = (a, b) => b === 0n ? a : ((a % b) + (b < 0n ? -b : b)) % (b < 0n ? -b : b);

/** `Int.tmod`. */
export const bigint_int__lean_int_mod = (a, b) => b === 0n ? a : a % b;

/** `Int.negSucc`. */
export const bigint_nat__bigint_int__lean_int_neg_succ_of_nat = (a) => -BigInt(a) - 1n;

/* ------------------------------------------------------------ int_num */

/** `Int64.toInt`: the argument may be a `BigInt` or a number. */
export const bigint_int__int53__lean_int64_to_int_sint = (a) => (typeof a === "bigint" ? $toNum53(a) : a);

/** `Int.negSucc`. */
export const bigint_nat__int53__lean_int_neg_succ_of_nat = (a) =>
  typeof a === "bigint" ? $toNum53(-a - 1n) : -a - 1;

/** `Int.ofNat`: the argument may be a `BigInt` or a number. */
export const bigint_nat__int53__lean_nat_to_int = (a) => (typeof a === "bigint" ? $toNum53(a) : a);

/** `Int.add`. */
export const int53__lean_int_add = (a, b) => $chk53(a + b);

/** `Int.tdiv`. */
export const int53__lean_int_div = (a, b) => b === 0 ? 0 : Math.trunc(a / b);

/** `Int.divExact`. */
export const int53__lean_int_div_exact = (a, b) =>
  b === 0
  ? 0
  : a % b < 0
    ? b > 0
      ? Math.trunc(a / b) - 1
      : Math.trunc(a / b) + 1
    : Math.trunc(a / b);

/** `Int.ediv`. */
export const int53__lean_int_ediv = (a, b) =>
  b === 0
  ? 0
  : a % b < 0
    ? b > 0
      ? Math.trunc(a / b) - 1
      : Math.trunc(a / b) + 1
    : Math.trunc(a / b);

/** `Int.emod`. */
export const int53__lean_int_emod = (a, b) => b === 0 ? a : ((a % b) + Math.abs(b)) % Math.abs(b);

/** `Int.tmod`. */
export const int53__lean_int_mod = (a, b) => b === 0 ? a : a % b;

/** `Int.mul`. */
export const int53__lean_int_mul = (a, b) => $chk53(a * b);

/** `Int.neg`. */
export const int53__lean_int_neg = (a) => 0 - a;

/** `Int.sub`. */
export const int53__lean_int_sub = (a, b) => $chk53(a - b);

/* ------------------------------------------------------------ uint64_bigint */

/** `Bool.toUInt64`. */
export const bigint_nat__lean_bool_to_uint64 = (a) => a ? 1n : 0n;

/**
 * `String.hash`: FNV-1a over the UTF-8 bytes, taken to 64 bits.  Lean's own hash is
 * not specified by the language, and nothing in a compiled program may depend on its
 * value — only on its being a function of the string.
 */
export const bigint_nat__lean_string_hash = (s) => {
  let h = 0xcbf29ce484222325n;
  for (const b of encoder.encode(s)) {
    h = U64((h ^ BigInt(b)) * 0x100000001b3n);
  }
  return h;
};

/** `UInt64.add`. */
export const bigint_nat__lean_uint64_add = (a, b) => BigInt.asUintN(64, a + b);

/** `UInt64.complement`. */
export const bigint_nat__lean_uint64_complement = (a) => BigInt.asUintN(64, ~a);

/** `UInt64.div`. */
export const bigint_nat__lean_uint64_div = (a, b) => b === 0n ? 0n : BigInt.asUintN(64, a / b);

/** `UInt64.land`. */
export const bigint_nat__lean_uint64_land = (a, b) => BigInt.asUintN(64, a & b);

/** `UInt64.log2`. */
export const bigint_nat__lean_uint64_log2 = (a) => a === 0n ? 0n : BigInt(a.toString(2).length - 1);

/** `UInt64.lor`. */
export const bigint_nat__lean_uint64_lor = (a, b) => BigInt.asUintN(64, a | b);

/** `UInt64.mod`. */
export const bigint_nat__lean_uint64_mod = (a, b) => b === 0n ? a : a % b;

/** `UInt64.mul`. */
export const bigint_nat__lean_uint64_mul = (a, b) => BigInt.asUintN(64, a * b);

/** `UInt64.neg`. */
export const bigint_nat__lean_uint64_neg = (a) => BigInt.asUintN(64, -a);

/** `UInt64.ofNat`, `UInt64.ofNatLT`. */
export const bigint_nat__lean_uint64_of_nat__UInt64_ofNat = (a) => BigInt.asUintN(64, BigInt(a));

/** `UInt64.shiftLeft`. */
export const bigint_nat__lean_uint64_shift_left = (a, b) => BigInt.asUintN(64, a << (((b % 64n) + 64n) % 64n));

/** `UInt64.shiftRight`. */
export const bigint_nat__lean_uint64_shift_right = (a, b) => a >> (((b % 64n) + 64n) % 64n);

/** `UInt64.sub`. */
export const bigint_nat__lean_uint64_sub = (a, b) => BigInt.asUintN(64, a - b);

/** `UInt64.xor`. */
export const bigint_nat__lean_uint64_xor = (a, b) => BigInt.asUintN(64, a ^ b);

/* ------------------------------------------------------------ uint64_num */

/** `UInt64.ofBitVec`: the argument may be a `BigInt` or a number. */
export const bigint_bitvec64__uint53__lean_uint64_of_nat_mk = (a) => (typeof a === "bigint" ? $toNum53(a) : a);

/** `UInt64.ofNatLT`, `UInt64.ofNat`. */
export const bigint_nat__uint53__lean_uint64_of_nat__UInt64_ofNat = (a) => {
  a = BigInt(a);
  return $toNum53(BigInt.asUintN(64, a));
};

/** `Bool.toUInt64`. */
export const uint53__lean_bool_to_uint64 = (a) => a ? 1 : 0;

/**
 * `String.hash`.  Lean's own hash is not specified by the language, and nothing in a
 * compiled program may depend on its value — only on its being a function of the
 * string.  This is FNV-1a over the UTF-8 bytes, taken to 64 bits and then cut to the
 * 53 a number holds.
 */
export const uint53__lean_string_hash = (s) => {
  let h = 0xcbf29ce484222325n;
  for (const b of encoder.encode(s)) {
    h = BigInt.asUintN(64, (h ^ BigInt(b)) * 0x100000001b3n);
  }
  return low53(h);
};

/** `UInt64.add`. */
export const uint53__lean_uint64_add = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(BigInt.asUintN(64, a + b));
};

/** `UInt64.complement`. */
export const uint53__lean_uint64_complement = (a) => {
  a = BigInt(a);
  return $toNum53(BigInt.asUintN(64, ~a));
};

/** `UInt64.div`. */
export const uint53__lean_uint64_div = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(b === 0n ? 0n : BigInt.asUintN(64, a / b));
};

/** `UInt64.land`. */
export const uint53__lean_uint64_land = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(BigInt.asUintN(64, a & b));
};

/** `UInt64.log2`. */
export const uint53__lean_uint64_log2 = (a) => {
  a = BigInt(a);
  return $toNum53(a === 0n ? 0n : BigInt(a.toString(2).length - 1));
};

/** `UInt64.lor`. */
export const uint53__lean_uint64_lor = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(BigInt.asUintN(64, a | b));
};

/** `UInt64.mod`. */
export const uint53__lean_uint64_mod = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(b === 0n ? a : a % b);
};

/** `UInt64.mul`. */
export const uint53__lean_uint64_mul = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(BigInt.asUintN(64, a * b));
};

/** `UInt64.neg`. */
export const uint53__lean_uint64_neg = (a) => {
  a = BigInt(a);
  return $toNum53(BigInt.asUintN(64, -a));
};

/** `UInt64.shiftLeft`. */
export const uint53__lean_uint64_shift_left = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(BigInt.asUintN(64, a << (((b % 64n) + 64n) % 64n)));
};

/** `UInt64.shiftRight`. */
export const uint53__lean_uint64_shift_right = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(a >> (((b % 64n) + 64n) % 64n));
};

/** `UInt64.sub`. */
export const uint53__lean_uint64_sub = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(BigInt.asUintN(64, a - b));
};

/** `UInt64.xor`. */
export const uint53__lean_uint64_xor = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(BigInt.asUintN(64, a ^ b));
};

/* ------------------------------------------------------------ int64_bigint */

/** `Bool.toInt64`. */
export const bigint_int__lean_bool_to_int64 = (a) => a ? 1n : 0n;

/** `Int64.abs`. */
export const bigint_int__lean_int64_abs = (a) => BigInt.asIntN(64, a < 0n ? -a : a);

/** `Int64.add`. */
export const bigint_int__lean_int64_add = (a, b) => BigInt.asIntN(64, a + b);

/** `Int64.complement`. */
export const bigint_int__lean_int64_complement = (a) => BigInt.asIntN(64, ~a);

/** `Int64.div`. */
export const bigint_int__lean_int64_div = (a, b) => b === 0n ? 0n : BigInt.asIntN(64, a / b);

/** `Int64.land`. */
export const bigint_int__lean_int64_land = (a, b) => BigInt.asIntN(64, a & b);

/** `Int64.lor`. */
export const bigint_int__lean_int64_lor = (a, b) => BigInt.asIntN(64, a | b);

/** `Int64.mod`. */
export const bigint_int__lean_int64_mod = (a, b) => b === 0n ? a : a % b;

/** `Int64.mul`. */
export const bigint_int__lean_int64_mul = (a, b) => BigInt.asIntN(64, a * b);

/** `Int64.neg`. */
export const bigint_int__lean_int64_neg = (a) => BigInt.asIntN(64, -a);

/** `Int64.ofInt`. */
export const bigint_int__lean_int64_of_int = (a) => BigInt.asIntN(64, BigInt(a));

/** `Int64.shiftLeft`. */
export const bigint_int__lean_int64_shift_left = (a, b) => BigInt.asIntN(64, a << (((b % 64n) + 64n) % 64n));

/** `Int64.shiftRight`. */
export const bigint_int__lean_int64_shift_right = (a, b) => a >> (((b % 64n) + 64n) % 64n);

/** `Int64.sub`. */
export const bigint_int__lean_int64_sub = (a, b) => BigInt.asIntN(64, a - b);

/** `Int64.xor`. */
export const bigint_int__lean_int64_xor = (a, b) => BigInt.asIntN(64, a ^ b);

/** `Int64.ofNat`. */
export const bigint_nat__bigint_int__lean_int64_of_nat = (a) => BigInt.asIntN(64, BigInt(a));

/* ------------------------------------------------------------ int64_num */

/** `Int64.ofInt`. */
export const bigint_int__int53__lean_int64_of_int = (a) => {
  a = BigInt(a);
  return $toNum53(BigInt.asIntN(64, a));
};

/** `Int64.ofNat`. */
export const bigint_nat__int53__lean_int64_of_nat = (a) => {
  a = BigInt(a);
  return $toNum53(BigInt.asIntN(64, a));
};

/** `Bool.toInt64`. */
export const int53__lean_bool_to_int64 = (a) => a ? 1 : 0;

/** `Int64.abs`. */
export const int53__lean_int64_abs = (a) => {
  a = BigInt(a);
  return $toNum53(BigInt.asIntN(64, a < 0n ? -a : a));
};

/** `Int64.add`. */
export const int53__lean_int64_add = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(BigInt.asIntN(64, a + b));
};

/** `Int64.complement`. */
export const int53__lean_int64_complement = (a) => {
  a = BigInt(a);
  return $toNum53(BigInt.asIntN(64, ~a));
};

/** `Int64.div`. */
export const int53__lean_int64_div = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(b === 0n ? 0n : BigInt.asIntN(64, a / b));
};

/** `Int64.land`. */
export const int53__lean_int64_land = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(BigInt.asIntN(64, a & b));
};

/** `Int64.lor`. */
export const int53__lean_int64_lor = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(BigInt.asIntN(64, a | b));
};

/** `Int64.mod`. */
export const int53__lean_int64_mod = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(b === 0n ? a : a % b);
};

/** `Int64.mul`. */
export const int53__lean_int64_mul = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(BigInt.asIntN(64, a * b));
};

/** `Int64.neg`. */
export const int53__lean_int64_neg = (a) => {
  a = BigInt(a);
  return $toNum53(BigInt.asIntN(64, -a));
};

/** `Int64.shiftLeft`. */
export const int53__lean_int64_shift_left = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(BigInt.asIntN(64, a << (((b % 64n) + 64n) % 64n)));
};

/** `Int64.shiftRight`. */
export const int53__lean_int64_shift_right = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(a >> (((b % 64n) + 64n) % 64n));
};

/** `Int64.sub`. */
export const int53__lean_int64_sub = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(BigInt.asIntN(64, a - b));
};

/** `Int64.xor`. */
export const int53__lean_int64_xor = (a, b) => {
  a = BigInt(a);
  b = BigInt(b);
  return $toNum53(BigInt.asIntN(64, a ^ b));
};

/* ------------------------------------------------------------ bitvec_bigint */

/* ------------------------------------------------------------ bitvec_num */

/** `UInt64.toBitVec`: the argument may be a `BigInt` or a number. */
export const bigint_nat__int53_bitvec64__lean_uint64_to_nat__UInt64_toBitVec = (a) => (typeof a === "bigint" ? $toNum53(a) : a);

/* ------------------------------------------------------------ missing externs */

/** Called in place of an extern that has no JavaScript implementation yet. */
export const lean_extern_unimplemented = (name) => {
  throw new Error(`LeanScript: the extern ${name} has no JavaScript implementation yet`);
};

/* ------------------------------------------------------------ operations that share a function */

export const int53__lean_int16_of_int = bigint_int__lean_int16_of_int;
export const int53__lean_int32_of_int = bigint_int__lean_int32_of_int;
export const int53__lean_int64_to_int16 = bigint_int__lean_int64_to_int16;
export const int53__lean_int64_to_int32 = bigint_int__lean_int64_to_int32;
export const int53__lean_int64_to_int8 = bigint_int__lean_int64_to_int8;
export const int53__lean_int8_of_int = bigint_int__lean_int8_of_int;
export const bigint_nat__lean_array_fset = bigint_nat__lean_array_set;
export const bigint_nat__lean_array_fswap = bigint_nat__lean_array_swap;
export const bigint_nat__lean_array_get_borrowed = bigint_nat__lean_array_get;
export const bigint_nat__lean_uint16_of_nat__UInt16_ofNatLT = bigint_nat__lean_uint16_of_nat__UInt16_ofNat;
export const bigint_nat__lean_uint32_of_nat__UInt32_ofNatLT = bigint_nat__lean_uint32_of_nat__UInt32_ofNat;
export const bigint_nat__lean_uint8_of_nat__UInt8_ofNatLT = bigint_nat__lean_uint8_of_nat__UInt8_ofNat;
export const string__lean_string_data__String_toList = string__lean_string_data__String_data;
export const string__lean_string_mk__String_ofList = string__lean_string_mk__String_mk;
export const string__lean_string_utf8_at_end__String_Pos_Raw_atEnd = string__lean_string_utf8_at_end__String_Internal_atEnd;
export const string__lean_string_utf8_at_end__String_atEnd = string__lean_string_utf8_at_end__String_Internal_atEnd;
export const string__lean_string_utf8_extract__String_Pos_Raw_extract = string__lean_string_utf8_extract__String_Internal_extract;
export const string__lean_string_utf8_get__String_Pos_Raw_get = string__lean_string_utf8_get__String_Internal_get;
export const string__lean_string_utf8_get__String_get = string__lean_string_utf8_get__String_Internal_get;
export const string__lean_string_utf8_next__String_Pos_Raw_next = string__lean_string_utf8_next__String_Internal_next;
export const string__lean_string_utf8_next__String_next = string__lean_string_utf8_next__String_Internal_next;
export const string__lean_string_utf8_set__String_set = string__lean_string_utf8_set__String_Pos_Raw_set;
export const uint53__lean_array_fset = uint53__lean_array_set;
export const uint53__lean_array_fswap = uint53__lean_array_swap;
export const uint53__lean_array_get_borrowed = uint53__lean_array_get;
export const uint53__lean_uint16_of_nat__UInt16_ofNatLT = uint53__lean_uint16_of_nat__UInt16_ofNat;
export const uint53__lean_uint32_of_nat__UInt32_ofNatLT = uint53__lean_uint32_of_nat__UInt32_ofNat;
export const uint53__lean_uint8_of_nat__UInt8_ofNatLT = uint53__lean_uint8_of_nat__UInt8_ofNat;
export const int53__bigint_nat__lean_nat_abs = bigint_int__bigint_nat__lean_nat_abs;
export const bigint_nat__lean_nat_mod__Nat_modCore = bigint_nat__lean_nat_mod__Nat_mod;
export const bigint_nat__lean_string_length__String_length = bigint_nat__lean_string_length__String_Internal_length;
export const int53__uint53__lean_nat_abs = bigint_int__uint53__lean_nat_abs;
export const uint53__lean_nat_mod__Nat_modCore = uint53__lean_nat_mod__Nat_mod;
export const uint53__lean_string_length__String_length = uint53__lean_string_length__String_Internal_length;
export const uint53__bigint_int__lean_int_neg_succ_of_nat = bigint_nat__bigint_int__lean_int_neg_succ_of_nat;
export const uint53__int53__lean_int_neg_succ_of_nat = bigint_nat__int53__lean_int_neg_succ_of_nat;
export const bigint_nat__lean_uint64_of_nat__UInt64_ofNatLT = bigint_nat__lean_uint64_of_nat__UInt64_ofNat;
export const uint53__bigint_nat__lean_uint64_of_nat__UInt64_ofNat = bigint_nat__lean_uint64_of_nat__UInt64_ofNat;
export const uint53__bigint_nat__lean_uint64_of_nat__UInt64_ofNatLT = bigint_nat__lean_uint64_of_nat__UInt64_ofNat;
export const bigint_nat__uint53__lean_uint64_of_nat__UInt64_ofNatLT = bigint_nat__uint53__lean_uint64_of_nat__UInt64_ofNat;
export const uint53__lean_uint64_of_nat__UInt64_ofNat = bigint_nat__uint53__lean_uint64_of_nat__UInt64_ofNat;
export const uint53__lean_uint64_of_nat__UInt64_ofNatLT = bigint_nat__uint53__lean_uint64_of_nat__UInt64_ofNat;
export const int53__bigint_int__lean_int64_of_int = bigint_int__lean_int64_of_int;
export const uint53__bigint_int__lean_int64_of_nat = bigint_nat__bigint_int__lean_int64_of_nat;
export const int53__lean_int64_of_int = bigint_int__int53__lean_int64_of_int;
export const uint53__int53__lean_int64_of_nat = bigint_nat__int53__lean_int64_of_nat;
