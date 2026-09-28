// The runtime of the JavaScript that LeanScript generates: one module.
//
// Every function exported here is an operation of `JsTerm/Ops.lean` (`JsOpImported`), of
// the same name: the name of the extern it implements, behind the JavaScript representation
// of its arguments and result (`bigint_nat__lean_nat_div` on `BigInt`s, `uint53__lean_nat_div`
// on numbers below 2^53; see `scripts/gen_js_ops.py` for the naming).  A generated module
// imports the operations it calls.  The operations that are one JavaScript operator or call
// of a global are not here: they are written inline (`JsOpInlinable`).
//
// An alias `export const a = b;` of an operation at the same signature is not an operation of
// its own: the extern of `a` is compiled to `b` (`lean_array_fset` is `lean_array_set`).
//
// Every function is pure (it never mutates an argument), except the `_mutable` array
// updates, which the backend calls only on an array nothing else refers to (their
// `_immutable` versions return an updated copy).  A function that may throw is one that
// contains a `throw` or calls one that may: the generator reads that off this file.

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

/** Lean's hash of a sequence of bytes (`hash_str` of the Lean runtime: MurmurHash64A). */
const $hashBytes = (bytes, seed = 11n) => {
  const m = 0xc6a4a7935bd1e995n;
  const len = bytes.length;
  let h = U64(seed ^ U64(BigInt(len) * m));
  const n8 = len - (len % 8);
  for (let i = 0; i < n8; i += 8) {
    let k = 0n;
    for (let j = 7; j >= 0; j--) k = (k << 8n) | BigInt(bytes[i + j]);
    k = U64(k * m);
    k ^= k >> 47n;
    k = U64(k * m);
    h ^= k;
    h = U64(h * m);
  }
  if (len % 8 > 0) {
    for (let j = (len % 8) - 1; j >= 0; j--) h ^= BigInt(bytes[n8 + j]) << BigInt(8 * j);
    h = U64(h * m);
  }
  h ^= h >> 47n;
  h = U64(h * m);
  h ^= h >> 47n;
  return h;
};

/** `lean_uint64_mix_hash` of the Lean runtime, on `BigInt`s. */
const $mixHash = (h, k) => {
  const m = 0xc6a4a7935bd1e995n;
  k = U64(k * m);
  k ^= k >> 47n;
  k ^= m;
  h ^= k;
  return U64(h * m);
};

/** The UTF-8 size of the character of code point `cp`. */
const $cpSize = (cp) => (cp < 128 ? 1 : cp < 2048 ? 2 : cp < 65536 ? 3 : 4);

/** The byte positions at which the characters of `s` start, and the end position. */
const $starts = (s) => {
  const out = [];
  let off = 0;
  for (const ch of s) {
    out.push(off);
    off += $cpSize(ch.codePointAt(0));
  }
  return [out, off];
};

/** `String.Pos.Raw.get`: the character that starts at `p`, or `'A'`. */
const $get = (s, p) => {
  const r = $utf8At(s, p);
  return r === undefined ? "A" : r[0];
};

/** `String.Pos.Raw.next`: the position after the character at `p` (`p + 1` if none starts there). */
const $next = (s, p) => {
  const r = $utf8At(s, p);
  return r === undefined ? p + 1 : p + r[1];
};

/** `String.Pos.Raw.prev`: the start of the last character before `p` (`p - 1` past the end). */
const $prev = (s, p) => {
  if (p === 0) return 0;
  const [st, end] = $starts(s);
  if (p > end) return p - 1;
  let r = 0;
  for (const i of st) {
    if (i < p) r = i;
    else break;
  }
  return r;
};

/** Is `b` the first byte of the UTF-8 encoding of a character? */
const $isFirstByte = (b) =>
  (b & 0x80) === 0 || (b & 0xe0) === 0xc0 || (b & 0xf0) === 0xe0 || (b & 0xf8) === 0xf0;

/** `String.Pos.Raw.isValid`. */
const $isValid = (s, p) => {
  const bytes = encoder.encode(s);
  return p < bytes.length ? $isFirstByte(bytes[p]) : p === bytes.length;
};

/** The code point order of two strings (`-1`, `0`, `1`), which is Lean's order on `String`
 *  (JavaScript's `<` compares UTF-16 code units, which differs above `U+FFFF`). */
const $cmpStr = (a, b) => {
  const n = Math.min(a.length, b.length);
  for (let i = 0; i < n; i++) {
    let x = a.charCodeAt(i);
    let y = b.charCodeAt(i);
    if (x !== y) {
      if (x >= 0xd800 && y >= 0xd800) {
        x = x >= 0xe000 ? x - 0x800 : x + 0x2000;
        y = y >= 0xe000 ? y - 0x800 : y + 0x2000;
      }
      return x < y ? -1 : 1;
    }
  }
  return a.length < b.length ? -1 : a.length === b.length ? 0 : 1;
};

/** A count or index held as a `Nat` (a `BigInt` or a number), as a number, capped at `2^53`
 *  (no string or array is that long, so the cap never changes a result). */
const $capNat = (n) => (typeof n === "bigint" ? (n > 9007199254740992n ? 9007199254740992 : Number(n)) : n);

/** Whitespace, as Lean's `Char.isWhitespace`. */
const $isWs = (c) => c === " " || c === "\t" || c === "\r" || c === "\n";

/** A double as `m * 2^e` exactly (`m` a `BigInt`, `x` finite and non-negative). */
const $decompose = (x) => {
  const dv = new DataView(new ArrayBuffer(8));
  dv.setFloat64(0, x);
  const bits = dv.getBigUint64(0);
  const ex = Number((bits >> 52n) & 0x7ffn);
  const frac = bits & 0xfffffffffffffn;
  return ex === 0 ? [frac, -1074] : [frac | 0x10000000000000n, ex - 1075];
};

/** `Float.toString`: C's `%f` (six decimals, rounded to nearest, ties to even, of the exact
 *  value), `NaN`, `inf` and `-inf`. */
const $fmtF6 = (x) => {
  if (Number.isNaN(x)) return "NaN";
  if (x === Infinity) return "inf";
  if (x === -Infinity) return "-inf";
  const neg = x < 0 || Object.is(x, -0);
  const [m, e] = $decompose(Math.abs(x));
  let num = m * 1000000n;
  let den = 1n;
  if (e >= 0) num <<= BigInt(e);
  else den <<= BigInt(-e);
  let q = num / den;
  const r2 = (num % den) * 2n;
  if (r2 > den || (r2 === den && (q & 1n) === 1n)) q += 1n;
  const d = q.toString().padStart(7, "0");
  return (neg ? "-" : "") + d.slice(0, -6) + "." + d.slice(-6);
};

/** `Float.round`: to the nearest integer, halves away from zero (C's `round`). */
const $round = (x) => (x < 0 ? -Math.round(-x) : Math.round(x));

/** A float truncated towards zero into `[lo, hi]` (`NaN` is `0`), as Lean's conversions of a
 *  float to a fixed-width integer do (on numbers). */
const $satNum = (x, lo, hi) => (Number.isNaN(x) ? 0 : x <= lo ? lo : x >= hi ? hi : Math.trunc(x) + 0);

/** The same, on `BigInt`s. */
const $satBig = (x, lo, hi) =>
  Number.isNaN(x) ? 0n : x <= Number(lo) ? lo : x >= Number(hi) ? hi : BigInt(Math.trunc(x));

/** `frexp`: `[m, e]` with `x = m * 2^e` and `0.5 <= |m| < 1` (`[x, 0]` for zeros, infinities and
 *  `NaN`). */
const $frexp = (x) => {
  if (x === 0 || !Number.isFinite(x)) return [x, 0];
  const dv = new DataView(new ArrayBuffer(8));
  dv.setFloat64(0, x);
  const hi = dv.getUint32(0);
  const ex = (hi >>> 20) & 0x7ff;
  if (ex === 0) {
    const [m, e] = $frexp(x * 2 ** 64);
    return [m, e - 64];
  }
  dv.setUint32(0, ((hi & 0x800fffff) | (1022 << 20)) >>> 0);
  return [dv.getFloat64(0), ex - 1022];
};

/** An exponent held as an `Int` (a `BigInt` or a number), as a number clamped to `±5000`
 *  (beyond that every scaling overflows or underflows alike). */
const $clampExp = (n) => {
  if (typeof n === "bigint") return n > 5000n ? 5000 : n < -5000n ? -5000 : Number(n);
  return n > 5000 ? 5000 : n < -5000 ? -5000 : n;
};

/** `scalbn`: `x * 2^n`, rounded once (musl's algorithm). */
const $scalbn = (x, n) => {
  let y = x;
  if (n > 1023) {
    y *= 2 ** 1023;
    n -= 1023;
    if (n > 1023) {
      y *= 2 ** 1023;
      n -= 1023;
      if (n > 1023) n = 1023;
    }
  } else if (n < -1022) {
    y *= 2 ** -969;
    n += 969;
    if (n < -1022) {
      y *= 2 ** -969;
      n += 969;
      if (n < -1022) n = -1022;
    }
  }
  return y * 2 ** n;
};

/** `scalbnf`: the same in single precision (musl's algorithm). */
const $scalbnf = (x, n) => {
  const f = Math.fround;
  let y = x;
  if (n > 127) {
    y = f(y * 2 ** 127);
    n -= 127;
    if (n > 127) {
      y = f(y * 2 ** 127);
      n -= 127;
      if (n > 127) n = 127;
    }
  } else if (n < -126) {
    y = f(y * 2 ** -102);
    n += 102;
    if (n < -126) {
      y = f(y * 2 ** -102);
      n += 102;
      if (n < -126) n = -126;
    }
  }
  return f(y * 2 ** n);
};

/** The bits of a double, as a `BigInt`. */
const $toBits = (x) => {
  const dv = new DataView(new ArrayBuffer(8));
  dv.setFloat64(0, x);
  return dv.getBigUint64(0);
};

/** The double of the given bits (a `BigInt`). */
const $ofBits = (b) => {
  const dv = new DataView(new ArrayBuffer(8));
  dv.setBigUint64(0, BigInt(b));
  return dv.getFloat64(0);
};

/** A `Substring.Raw` or a `String.Slice` `[s, b, e]`, as the string of its bytes `[b, e)`. */
const $sliceBytes = (ss) => encoder.encode(ss[0]).subarray(ss[1], ss[2]);

/** `Substring.Raw.next`: the relative position after the relative position `p`. */
const $subNext = (ss, p) => {
  const absP = ss[1] + p;
  return absP === ss[2] ? p : $next(ss[0], absP) - ss[1];
};

/* ------------------------------------------------------------ non_configurable */

/** `Array.pop`: a copy without the last element. */
export const array__lean_array_pop_immutable = (a) => a.slice(0, Math.max(a.length - 1, 0));

/** `Array.pop`, in place (on a generic array only: a typed array cannot shrink). */
export const array__lean_array_pop_mutable = (a) => {
  a.pop();
  return a;
};

/** `Array.push`: a copy with one more element. */
export const array__lean_array_push_immutable = (a, x) => {
  if (Array.isArray(a)) return [...a, x];
  const r = new a.constructor(a.length + 1);
  r.set(a);
  r[a.length] = x;
  return r;
};

/** `Array.push`, in place (on a generic array only: a typed array cannot grow). */
export const array__lean_array_push_mutable = (a, x) => {
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
export const bigint_nat__lean_array_set_immutable = (a, i, x) => {
  const k = $idx(i);
  if (k >= a.length) return a;
  const r = a.slice();
  r[k] = x;
  return r;
};

/** `Array.set!`, in place. */
export const bigint_nat__lean_array_set_mutable = (a, i, x) => {
  const k = $idx(i);
  if (k < a.length) a[k] = x;
  return a;
};

/** `Array.swapIfInBounds`: a copy with two elements swapped (the array itself out of bounds). */
export const bigint_nat__lean_array_swap_immutable = (a, i, j) => {
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
export const bigint_nat__lean_array_swap_mutable = (a, i, j) => {
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
export const uint53__lean_array_set_immutable = (a, i, x) => {
  const k = i;
  if (k >= a.length) return a;
  const r = a.slice();
  r[k] = x;
  return r;
};

/** `Array.set!`, in place. */
export const uint53__lean_array_set_mutable = (a, i, x) => {
  const k = i;
  if (k < a.length) a[k] = x;
  return a;
};

/** `Array.swapIfInBounds`: a copy with two elements swapped (the array itself out of bounds). */
export const uint53__lean_array_swap_immutable = (a, i, j) => {
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
export const uint53__lean_array_swap_mutable = (a, i, j) => {
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
export const string__lean_string_utf8_set__String_Pos_set = (a, b, c) => $utf8Set(a, b, c);

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

/** `String.hash`: Lean's hash of the UTF-8 bytes (MurmurHash64A, seed 11). */
export const bigint_nat__lean_string_hash = (s) => $hashBytes(encoder.encode(s));

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

/** `String.hash`: Lean's hash of the UTF-8 bytes (MurmurHash64A, seed 11). */
export const uint53__lean_string_hash = (s) => $toNum53($hashBytes(encoder.encode(s)));

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


/* ------------------------------------------------------------ floats */

/** `Float.round`. */
export const float__round = (a) => $round(a);

/** `Float32.round`. */
export const float32__roundf = (a) => $round(a);

/** `Float.toString`. */
export const float__lean_float_to_string = (a) => $fmtF6(a);

/** `Float32.toString`. */
export const float32__lean_float32_to_string = (a) => $fmtF6(a);

/** `Float.toUInt8` (saturating; `NaN` is `0`). */
export const float__lean_float_to_uint8 = (a) => $satNum(a, 0, 255);

/** `Float.toUInt16` (saturating; `NaN` is `0`). */
export const float__lean_float_to_uint16 = (a) => $satNum(a, 0, 65535);

/** `Float.toUInt32` (saturating; `NaN` is `0`). */
export const float__lean_float_to_uint32 = (a) => $satNum(a, 0, 4294967295);

/** `Float.toUInt64` (saturating; `NaN` is `0`). */
export const bigint_nat__lean_float_to_uint64 = (a) => $satBig(a, 0n, 18446744073709551615n);

/** `Float.toUInt64` (saturating; `NaN` is `0`), a result of `2^53` or more throws. */
export const uint53__lean_float_to_uint64 = (a) => $toNum53($satBig(a, 0n, 18446744073709551615n));

/** `Float.toInt8` (saturating; `NaN` is `0`). */
export const float__lean_float_to_int8 = (a) => $satNum(a, -128, 127);

/** `Float.toInt16` (saturating; `NaN` is `0`). */
export const float__lean_float_to_int16 = (a) => $satNum(a, -32768, 32767);

/** `Float.toInt32` (saturating; `NaN` is `0`). */
export const float__lean_float_to_int32 = (a) => $satNum(a, -2147483648, 2147483647);

/** `Float.toInt64` (saturating; `NaN` is `0`). */
export const bigint_int__lean_float_to_int64 = (a) =>
  $satBig(a, -9223372036854775808n, 9223372036854775807n);

/** `Float.toInt64` (saturating; `NaN` is `0`), a result of absolute value `2^53` or more throws. */
export const int53__lean_float_to_int64 = (a) =>
  $toNum53($satBig(a, -9223372036854775808n, 9223372036854775807n));

/** `Float32.toUInt8` (saturating; `NaN` is `0`). */
export const float32__lean_float32_to_uint8 = (a) => $satNum(a, 0, 255);

/** `Float32.toUInt16` (saturating; `NaN` is `0`). */
export const float32__lean_float32_to_uint16 = (a) => $satNum(a, 0, 65535);

/** `Float32.toUInt32` (saturating; `NaN` is `0`). */
export const float32__lean_float32_to_uint32 = (a) => $satNum(a, 0, 4294967295);

/** `Float32.toUInt64` (saturating; `NaN` is `0`). */
export const bigint_nat__lean_float32_to_uint64 = (a) => $satBig(a, 0n, 18446744073709551615n);

/** `Float32.toUInt64` (saturating; `NaN` is `0`), a result of `2^53` or more throws. */
export const uint53__lean_float32_to_uint64 = (a) => $toNum53($satBig(a, 0n, 18446744073709551615n));

/** `Float32.toInt8` (saturating; `NaN` is `0`). */
export const float32__lean_float32_to_int8 = (a) => $satNum(a, -128, 127);

/** `Float32.toInt16` (saturating; `NaN` is `0`). */
export const float32__lean_float32_to_int16 = (a) => $satNum(a, -32768, 32767);

/** `Float32.toInt32` (saturating; `NaN` is `0`). */
export const float32__lean_float32_to_int32 = (a) => $satNum(a, -2147483648, 2147483647);

/** `Float32.toInt64` (saturating; `NaN` is `0`). */
export const bigint_int__lean_float32_to_int64 = (a) =>
  $satBig(a, -9223372036854775808n, 9223372036854775807n);

/** `Float32.toInt64` (saturating; `NaN` is `0`), a result of absolute value `2^53` or more throws. */
export const int53__lean_float32_to_int64 = (a) =>
  $toNum53($satBig(a, -9223372036854775808n, 9223372036854775807n));

/** `Float.toBits`. */
export const bigint_nat__lean_float_to_bits__Float_toBits = (a) => $toBits(a);

/** `Float.toBits`; bits of `2^53` or more (every double of absolute value at least `2^-1021`,
 *  and every negative one) throw. */
export const uint53__lean_float_to_bits__Float_toBits = (a) => $toNum53($toBits(a));

/** `Float.ofBits`. */
export const bigint_nat__lean_float_of_bits__Float_ofBits = (a) => $ofBits(a);

/** `Float.ofBits`. */
export const uint53__lean_float_of_bits__Float_ofBits = (a) => $ofBits(a);

/** `Float32.toBits`. */
export const float32__lean_float32_to_bits__Float32_toBits = (a) => {
  const dv = new DataView(new ArrayBuffer(4));
  dv.setFloat32(0, a);
  return dv.getUint32(0);
};

/** `Float32.ofBits`. */
export const uint32__lean_float32_of_bits__Float32_ofBits = (a) => {
  const dv = new DataView(new ArrayBuffer(4));
  dv.setUint32(0, a);
  return dv.getFloat32(0);
};

/** `Float.frExp`. */
export const bigint_int__lean_float_frexp = (a) => {
  const [m, e] = $frexp(a);
  return { _1: m, _2: BigInt(e) };
};

/** `Float.frExp`. */
export const int53__lean_float_frexp = (a) => {
  const [m, e] = $frexp(a);
  return { _1: m, _2: e };
};

/** `Float32.frExp`. */
export const bigint_int__lean_float32_frexp = (a) => {
  const [m, e] = $frexp(a);
  return { _1: m, _2: BigInt(e) };
};

/** `Float32.frExp`. */
export const int53__lean_float32_frexp = (a) => {
  const [m, e] = $frexp(a);
  return { _1: m, _2: e };
};

/** `Float.scaleB`. */
export const bigint_int__lean_float_scaleb = (a, n) => $scalbn(a, $clampExp(n));

/** `Float.scaleB`. */
export const int53__lean_float_scaleb = (a, n) => $scalbn(a, $clampExp(n));

/** `Float32.scaleB`. */
export const bigint_int__lean_float32_scaleb = (a, n) => $scalbnf(a, $clampExp(n));

/** `Float32.scaleB`. */
export const int53__lean_float32_scaleb = (a, n) => $scalbnf(a, $clampExp(n));

/* ------------------------------------------------------------ strings */

/** `String.Internal.drop`: without its first `n` characters. */
export const bigint_nat__lean_string_drop = (s, n) => [...s].slice($capNat(n)).join("");

/** `String.Internal.drop`: without its first `n` characters. */
export const uint53__lean_string_drop = bigint_nat__lean_string_drop;

/** `String.Internal.dropRight`: without its last `n` characters. */
export const bigint_nat__lean_string_dropright = (s, n) => {
  const cs = [...s];
  return cs.slice(0, Math.max(cs.length - $capNat(n), 0)).join("");
};

/** `String.Internal.dropRight`: without its last `n` characters. */
export const uint53__lean_string_dropright = bigint_nat__lean_string_dropright;

/** `String.Internal.trim`: without the whitespace (`Char.isWhitespace`) at both ends. */
export const string__lean_string_trim = (s) => {
  const cs = [...s];
  let b = 0;
  let e = cs.length;
  while (b < e && $isWs(cs[b])) b++;
  while (e > b && $isWs(cs[e - 1])) e--;
  return cs.slice(b, e).join("");
};

/** `String.Internal.foldl`. */
export const string__lean_string_foldl = (f, init, s) => {
  let acc = init;
  for (const c of s) acc = f(acc, c);
  return acc;
};

/** `String.Internal.isPrefixOf`. */
export const string__lean_string_isprefixof = (p, s) => s.startsWith(p);

/** `String.Internal.contains`. */
export const string__lean_string_contains = (s, c) => s.includes(c);

/** `String.Internal.front`: the first character (`'A'` for the empty string). */
export const string__lean_string_front = (s) => (s.length === 0 ? "A" : String.fromCodePoint(s.codePointAt(0)));

/** `String.Internal.posOf`: the position of the first `c`, or the end position. */
export const string__lean_string_posof = (s, c) => {
  const i = s.indexOf(c);
  return encoder.encode(i < 0 ? s : s.slice(0, i)).length;
};

/** `String.Internal.intercalate`. */
export const string__lean_string_intercalate = (sep, xs) => xs.join(sep);

/** `String.Internal.nextWhile`: from `i`, the position of the first character that fails `p`
 *  (or the end). */
export const string__lean_string_nextwhile = (s, p, i) => {
  const end = $utf8(s).length;
  while (i < end && p($get(s, i))) i = $next(s, i);
  return i;
};

/** `String.Internal.any`. */
export const string__lean_string_any = (s, p) => {
  for (const c of s) if (p(c)) return true;
  return false;
};

/** `String.Internal.capitalize`: the first character in upper case (ASCII only). */
export const string__lean_string_capitalize = (s) => {
  const c = s.charCodeAt(0);
  return c >= 97 && c <= 122 ? String.fromCharCode(c - 32) + s.slice(1) : s;
};

/** `String.Internal.offsetOfPos`: the number of characters that start before `p`. */
export const bigint_nat__lean_string_offsetofpos = (s, p) => BigInt(uint53__lean_string_offsetofpos(s, p));

/** `String.Internal.offsetOfPos`: the number of characters that start before `p`. */
export const uint53__lean_string_offsetofpos = (s, p) => {
  let n = 0;
  let off = 0;
  for (const ch of s) {
    if (off >= p) break;
    n++;
    off += $cpSize(ch.codePointAt(0));
  }
  return n;
};

/** `String.Internal.getUTF8Byte`: byte `n` of the UTF-8 encoding. */
export const bigint_nat__lean_string_get_byte_fast__String_Internal_getUTF8Byte = (s, n) =>
  encoder.encode(s)[Number(n)];

/** `String.Internal.getUTF8Byte`: byte `n` of the UTF-8 encoding. */
export const uint53__lean_string_get_byte_fast__String_Internal_getUTF8Byte = (s, n) => encoder.encode(s)[n];

/** `String.getUTF8Byte`: the byte at position `p`. */
export const string__lean_string_get_byte_fast__String_getUTF8Byte = (s, p) => encoder.encode(s)[p];

/** `String.getUtf8Byte`. */
export const string__lean_string_get_byte_fast__String_getUtf8Byte = string__lean_string_get_byte_fast__String_getUTF8Byte;

/** `String.Pos.Raw.get?`, `String.get?`: the character that starts at `p`, if one does. */
export const string__lean_string_utf8_get_opt__String_Pos_Raw_get$3F = (s, p) => {
  const r = $utf8At(s, p);
  return r === undefined ? { tag: 0 } : { tag: 1, _1: r[0] };
};

/** `String.Pos.Raw.get!`, `String.get!`, `String.Pos.Raw.get'`, `String.get'`: the character at `p`
 *  (`'A'` if none starts there). */
export const string__lean_string_utf8_get_bang__String_Pos_Raw_get$21 = (s, p) => $get(s, p);

/** `String.Pos.Raw.prev`, `String.prev`. */
export const string__lean_string_utf8_prev__String_Pos_Raw_prev = (s, p) => $prev(s, p);

/** `String.get?`. */
export const string__lean_string_utf8_get_opt__String_get$3F = string__lean_string_utf8_get_opt__String_Pos_Raw_get$3F;

/** `String.get!`. */
export const string__lean_string_utf8_get_bang__String_get$21 = string__lean_string_utf8_get_bang__String_Pos_Raw_get$21;

/** `String.get'`. */
export const string__lean_string_utf8_get_fast__String_get$27 = string__lean_string_utf8_get_bang__String_Pos_Raw_get$21;

/** `String.Pos.Raw.get'`. */
export const string__lean_string_utf8_get_fast__String_Pos_Raw_get$27 = string__lean_string_utf8_get_bang__String_Pos_Raw_get$21;

/** `String.prev`. */
export const string__lean_string_utf8_prev__String_prev = string__lean_string_utf8_prev__String_Pos_Raw_prev;

/** `dbgTraceIfShared msg a`: `a` (JavaScript does not tell whether a value is shared). */
export const string__lean_dbg_trace_if_shared = (msg, a) => a;

/** `String.next'`. */
export const string__lean_string_utf8_next_fast__String_next$27 = (s, p) => $next(s, p);

/** `String.Pos.next` (on a position of the string `s` given first). */
export const string__lean_string_utf8_next_fast__String_Pos_next = (s, p) => $next(s, p);

/** `String.extract` (on positions of the string `s` given first). */
export const string__lean_string_utf8_extract_fast = (s, b, e) => $utf8Extract(s, b, e);

/** `String.Pos.Raw.isValid`. */
export const string__lean_string_is_valid_pos = (s, p) => $isValid(s, p);

/** `String.Pos.Raw.Internal.min`. */
export const uint53__lean_string_pos_min = (a, b) => Math.min(a, b);

/** `String.Pos.Raw.Internal.sub`. */
export const uint53__lean_string_pos_sub = (a, b) => Math.max(a - b, 0);

/** `Substring.Raw.Internal.toString`. */
export const substring__lean_substring_tostring = (ss) => $utf8Extract(ss[0], ss[1], ss[2]);

/** `Substring.Raw.Internal.get`. */
export const substring__lean_substring_get = (ss, p) => $get(ss[0], ss[1] + p);

/** `Substring.Raw.Internal.front`. */
export const substring__lean_substring_front = (ss) => $get(ss[0], ss[1]);

/** `Substring.Raw.Internal.isEmpty`. */
export const substring__lean_substring_isempty = (ss) => ss[2] <= ss[1];

/** `Substring.Raw.Internal.prev`. */
export const substring__lean_substring_prev = (ss, p) => {
  const absP = ss[1] + p;
  return absP === ss[1] ? p : Math.max($prev(ss[0], absP) - ss[1], 0);
};

/** `Substring.Raw.Internal.drop`: without its first `n` characters. */
export const bigint_nat__lean_substring_drop = (ss, n) => {
  let k = $capNat(n);
  let p = 0;
  while (k > 0) {
    const q = $subNext(ss, p);
    if (q === p) break;
    p = q;
    k--;
  }
  return [ss[0], ss[1] + p, ss[2]];
};

/** `Substring.Raw.Internal.drop`: without its first `n` characters. */
export const uint53__lean_substring_drop = bigint_nat__lean_substring_drop;

/** `Substring.Raw.Internal.extract`. */
export const substring__lean_substring_extract = (ss, b, e) =>
  b >= e ? ["", 0, 0] : [ss[0], Math.min(ss[2], ss[1] + b), Math.min(ss[2], ss[1] + e)];

/** `Substring.Raw.Internal.takeWhile`. */
export const substring__lean_substring_takewhile = (ss, p) => {
  let i = ss[1];
  while (i < ss[2] && p($get(ss[0], i))) i = $next(ss[0], i);
  return [ss[0], ss[1], i];
};

/** `Substring.Raw.Internal.all` (`true` for a substring whose bounds are not valid). */
export const substring__lean_substring_all = (ss, p) => {
  const [s, b, e] = ss;
  if (!($isValid(s, b) && $isValid(s, e) && b <= e)) return true;
  for (let i = b; i < e; i = $next(s, i)) if (!p($get(s, i))) return false;
  return true;
};

/** `Substring.Raw.Internal.beq`: the same bytes (after moving an invalid bound to the end). */
export const substring__lean_substring_beq = (x, y) => {
  const fix = ([s, b, e]) => {
    const n = $utf8(s).length;
    return [s, $isValid(s, b) ? b : n, $isValid(s, e) ? e : n];
  };
  const a = $sliceBytes(fix(x));
  const b = $sliceBytes(fix(y));
  if (a.length !== b.length) return false;
  for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return false;
  return true;
};

/** `String.Slice` `<`: the order of the strings of the slices. */
export const stringSlice__lean_slice_dec_lt = (a, b) =>
  $cmpStr($utf8Extract(a[0], a[1], a[2]), $utf8Extract(b[0], b[1], b[2])) < 0;

/** `String.Slice.hash`: the hash of the string of the slice. */
export const bigint_nat__lean_slice_hash = (a) => $hashBytes($sliceBytes(a));

/** `String.Slice.hash`: the hash of the string of the slice (`2^53` or more throws). */
export const uint53__lean_slice_hash = (a) => $toNum53($hashBytes($sliceBytes(a)));

/* ------------------------------------------------------------ hashes */

/** `mixHash`. */
export const bigint_nat__lean_uint64_mix_hash = (h, k) => $mixHash(h, k);

/** `mixHash` (a result of `2^53` or more throws). */
export const uint53__lean_uint64_mix_hash = (h, k) => $toNum53($mixHash(BigInt(h), BigInt(k)));

/* ------------------------------------------------------------ version and platform */
// The values of the Lean toolchain the snapshots are checked against (4.34.0 on
// x86_64-unknown-linux-gnu); `Tests/Main.lean` checks them against the Lean that runs it.

/** `Lean.version.getMajor`. */
export const bigint_nat__lean_version_get_major = () => () => 4n;

/** `Lean.version.getMajor`. */
export const uint53__lean_version_get_major = () => () => 4;

/** `Lean.version.getMinor`. */
export const bigint_nat__lean_version_get_minor = () => () => 34n;

/** `Lean.version.getMinor`. */
export const uint53__lean_version_get_minor = () => () => 34;

/** `Lean.version.getPatch`. */
export const bigint_nat__lean_version_get_patch = () => () => 0n;

/** `Lean.version.getPatch`. */
export const uint53__lean_version_get_patch = () => () => 0;

/** `Lean.version.getIsRelease`. */
export const bool__lean_version_get_is_release = () => () => true;

/** `Lean.version.getSpecialDesc`. */
export const string__lean_version_get_special_desc = () => () => "";

/** `Lean.getGithash`. */
export const string__lean_get_githash = () => () => "293d5d0c0c3f3dded4688b3ccd6a33939ac5102b";

/** `System.Platform.getTarget`. */
export const string__lean_system_platform_target = () => () => "x86_64-unknown-linux-gnu";

/** `System.Platform.getIsEmscripten`. */
export const bool__lean_system_platform_emscripten = () => () => false;

/** `Lean.Internal.isStage0`. */
export const bool__lean_internal_is_stage0 = () => () => false;

/** `Lean.Internal.hasLLVMBackend`. */
export const bool__lean_internal_has_llvm_backend = () => () => false;

/* ------------------------------------------------------------ operations that share a function */

export const int53__lean_int16_of_int = bigint_int__lean_int16_of_int;
export const int53__lean_int32_of_int = bigint_int__lean_int32_of_int;
export const int53__lean_int64_to_int16 = bigint_int__lean_int64_to_int16;
export const int53__lean_int64_to_int32 = bigint_int__lean_int64_to_int32;
export const int53__lean_int64_to_int8 = bigint_int__lean_int64_to_int8;
export const int53__lean_int8_of_int = bigint_int__lean_int8_of_int;
export const bigint_nat__lean_array_fset = bigint_nat__lean_array_set_immutable;
export const bigint_nat__lean_array_fswap = bigint_nat__lean_array_swap_immutable;
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
export const uint53__lean_array_fset = uint53__lean_array_set_immutable;
export const uint53__lean_array_fswap = uint53__lean_array_swap_immutable;
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
