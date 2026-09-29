// The runtime of the JavaScript that LeanScript generates: one module.
//
// Every function exported here is an operation of `JsTerm/Ops/Imported.lean` (`JsOpImported`), of
// the same name: the name of the extern it implements, behind the JavaScript representation
// of its arguments and result (`bigint_nat__lean_nat_div` on `BigInt`s, `uint53__lean_nat_div`
// on numbers below 2^53; see `scripts/gen_js_ops.py` for the naming).  A generated module
// imports the operations it calls.  The operations that are one JavaScript operator or call
// of a global are not here: they are written inline (`JsOpInlinable`).
//
// An alias `export const a = b;` of an operation at the same signature is not an operation of
// its own: the extern of `a` is compiled to `b` (`lean_array_get_borrowed` is `lean_array_get`).
//
// Every function is pure (it never mutates an argument), except the `_mutable` array
// updates, which the backend calls only on an array nothing else refers to.  Every array
// update comes as the pair of the operations of `JsTerm/Ops/Imported.lean` that
// `JsOpImported.toMutable?` relates, at the same signature:
//
//   `…_immutable` (pure: returns an updated copy)  `…_mutable` (effectful: updates in place)
//   `array__lean_array_push_immutable`            `array__lean_array_push_mutable`
//   `array__lean_array_pop_immutable`             `array__lean_array_pop_mutable`
//   `<ix>__lean_array_set_immutable`              `<ix>__lean_array_set_mutable`
//   `<ix>__lean_array_swap_immutable`             `<ix>__lean_array_swap_mutable`
//   `<ix>__lean_array_fset_immutable`             `<ix>__lean_array_fset_mutable`
//   `<ix>__lean_array_fswap_immutable`            `<ix>__lean_array_fswap_mutable`
//
// where `<ix>` is the representation of the index (`bigint_nat` or `uint53`).  `push` / `pop`
// on a typed array (`typedArray__lean_array_push_immutable`, `…_pop_immutable`) have only the
// `_immutable` version: a typed array cannot grow or shrink.  A function that may throw is
// one that contains a `throw` or calls one that may: the generator reads that off this file.
//
// Every function gets exactly the representations its name says (a `bigint_nat` argument is
// always a `BigInt`, a `uint53` one always a safe non-negative number, …), so no function
// tests the type of an argument or converts one it does not need to.  The only throws are the
// results of a `uint53` / `int53` operation that are not safe integers; a function whose
// result always is one (`uint53__lean_uint64_div`, `int53__lean_int64_abs`, …) does not
// check, and so does not throw.  A count too large for memory (`Array.replicate`,
// `String.pushn`) fails in JavaScript's own allocation, as it runs out of memory in Lean.
//
// The `@param` / `@returns` tags of every exported function give the JavaScript type and the
// `JsTy` of its arguments and result, from its signature in `JsTerm/Ops/Imported.lean`; they are written
// by `python3 scripts/annotate_runtime.py` (run it again after changing a signature).

/* ------------------------------------------------------------ private helpers */

const encoder = new TextEncoder();

/** The UTF-8 size of the character of code point `cp`. */
const $cpSize = (cp) => (cp < 128 ? 1 : cp < 2048 ? 2 : cp < 65536 ? 3 : 4);

const $utf8At = (s, p) => {
  let off = 0;
  for (const ch of s) {
    const n = $cpSize(ch.codePointAt(0));
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

const $utf8 = (s) => encoder.encode(s);

/** The error of a `uint53` / `int53` result that is not a safe integer. */
const $overflow = () => {
  throw new RangeError(
    "LeanScript: integer overflow: the result does not fit in a number (use the bigint representation)",
  );
};

/** A `BigInt` result as a safe integer (one that is not throws). */
const $toNum53 = (x) => (x > 9007199254740991n || x < -9007199254740991n ? $overflow() : Number(x));

/** A number result that must be a safe integer (one that is not throws). */
const $chk53 = (x) => (Number.isSafeInteger(x) ? x : $overflow());

// `a ** e` of a safe integer `a` and a `number` `e >= 0`, exactly, by squaring (`Math.pow` need not be
// exact): every product is checked, and a square is only taken when it is multiplied into the
// result later, so it overflows only when the result does.
const $pow53 = (a, e) => {
  let r = 1;
  let x = a;
  while (e > 0) {
    if (e % 2 === 1) {
      r = $chk53(r * x);
    }
    e = Math.floor(e / 2);
    if (e > 0) {
      x = $chk53(x * x);
    }
  }
  return r;
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
    off = off + $cpSize(ch.codePointAt(0));
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
    off = off + $cpSize(ch.codePointAt(0));
    i = i + ch.length;
  }
  return s;
};

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

/** `Nat.land` below `2^53`: on the high 21 bits and the low 32 bits apart. */
const $land53 = (a, b) => (((a / 0x100000000) | 0) & ((b / 0x100000000) | 0)) * 0x100000000 + ((a & b) >>> 0);

/** `Nat.lor` below `2^53`. */
const $lor53 = (a, b) => (((a / 0x100000000) | 0) | ((b / 0x100000000) | 0)) * 0x100000000 + ((a | b) >>> 0);

/** `Nat.xor` below `2^53`. */
const $xor53 = (a, b) => (((a / 0x100000000) | 0) ^ ((b / 0x100000000) | 0)) * 0x100000000 + ((a ^ b) >>> 0);

/** `Nat.log2` below `2^53`. */
const $log2_53 = (a) => (a < 0x100000000 ? (a === 0 ? 0 : 31 - Math.clz32(a)) : 63 - Math.clz32(a / 0x100000000));

/** The `BigInt` `x` taken modulo `2^64`. */
const U64 = (x) => BigInt.asUintN(64, x);

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

/** An exponent held as a `BigInt`, as a number clamped to `±5000` (beyond that every scaling
 *  overflows or underflows alike). */
const $clampExp = (n) => (n > 5000n ? 5000 : n < -5000n ? -5000 : Number(n));

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

/** A `BigInt` as a `float32`: rounded once, to nearest, ties to even (C's `(float)` cast of a
 *  64-bit integer).  `Math.fround(Number(x))` would round twice (to a double, then to a
 *  float), which differs on e.g. `2n ** 63n + 2n ** 39n + 1n`: the double is the midpoint
 *  `2^63 + 2^39` of two floats, which `Math.fround` rounds to even, down to `2^63`, while the
 *  integer is above it and rounds up to `2^63 + 2^40`.  So a wide `x` is first cut to its 30
 *  leading bits, the lowest of them set when a dropped bit is (a sticky bit): that number is a
 *  double exactly and lies on the same side of every midpoint of floats as `x`. */
const $bigToF32 = (x) => {
  const neg = x < 0n;
  let m = neg ? -x : x;
  if (m >= 9007199254740992n) {
    const s = BigInt(m.toString(2).length - 30);
    const dropped = m & ((1n << s) - 1n);
    m = ((m >> s) | (dropped === 0n ? 0n : 1n)) << s;
  }
  const f = Math.fround(Number(m));
  return neg ? -f : f;
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
  dv.setBigUint64(0, b);
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

/** `Array.pop`: a copy without the last element (on a generic array).
 *  @template α the element type
 *  @param {Array<α>} a `array α`
 *  @returns {Array<α>} `array α` */
export const array__lean_array_pop_immutable = (a) => a.slice(0, -1);

/** `Array.pop`, in place (on a generic array only: a typed array cannot shrink).
 *  @template α the element type
 *  @param {Array<α>} a `array α`
 *  @returns {Array<α>} `array α` */
export const array__lean_array_pop_mutable = (a) => {
  a.pop();
  return a;
};

/** `Array.push`: a copy with one more element (on a generic array).
 *  @template α the element type
 *  @param {Array<α>} a `array α`
 *  @param {α} x `α`
 *  @returns {Array<α>} `array α` */
export const array__lean_array_push_immutable = (a, x) => [...a, x];

/** `Array.push`, in place (on a generic array only: a typed array cannot grow).
 *  @template α the element type
 *  @param {Array<α>} a `array α`
 *  @param {α} x `α`
 *  @returns {Array<α>} `array α` */
export const array__lean_array_push_mutable = (a, x) => {
  a.push(x);
  return a;
};

/** `Array.pop`: a copy without the last element, on a typed array (which cannot shrink, so
 *  this has no `_mutable` version).
 *  @template t the typed-array element (`JsTypedElem`); `TypedArray` is `t.kind`
 *  @param {TypedArray} a `typedArray t`
 *  @returns {TypedArray} `typedArray t` */
export const typedArray__lean_array_pop_immutable = (a) => a.slice(0, -1);

/** `Array.push`: a copy with one more element, on a typed array (which cannot grow, so this
 *  has no `_mutable` version).
 *  @template t the typed-array element (`JsTypedElem`); `TypedArray` is `t.kind`
 *  @param {TypedArray} a `typedArray t`
 *  @param {number|bigint} x `t.leaf`
 *  @returns {TypedArray} `typedArray t` */
export const typedArray__lean_array_push_immutable = (a, x) => {
  const r = new a.constructor(a.length + 1);
  r.set(a);
  r[a.length] = x;
  return r;
};

/** `Int16.ofInt`.
 *  @param {bigint} a `bigint_int`
 *  @returns {number} `int16` */
export const bigint_int__lean_int16_of_int = (a) => Number(BigInt.asIntN(16, a));

/** `Int32.ofInt`.
 *  @param {bigint} a `bigint_int`
 *  @returns {number} `int32` */
export const bigint_int__lean_int32_of_int = (a) => Number(BigInt.asIntN(32, a));

/** `Int8.ofInt`.
 *  @param {bigint} a `bigint_int`
 *  @returns {number} `int8` */
export const bigint_int__lean_int8_of_int = (a) => Number(BigInt.asIntN(8, a));

/** `Int64.toInt16`.
 *  @param {bigint} a `bigint_int`
 *  @returns {number} `int16` */
export const bigint_int__lean_int64_to_int16 = (a) => Number(BigInt.asIntN(16, a));

/** `Int64.toInt32`.
 *  @param {bigint} a `bigint_int`
 *  @returns {number} `int32` */
export const bigint_int__lean_int64_to_int32 = (a) => Number(BigInt.asIntN(32, a));

/** `Int64.toInt8`.
 *  @param {bigint} a `bigint_int`
 *  @returns {number} `int8` */
export const bigint_int__lean_int64_to_int8 = (a) => Number(BigInt.asIntN(8, a));

/** `Int16.ofInt` (`ToInt32` takes a safe integer modulo `2^32`).
 *  @param {number} a `int53`
 *  @returns {number} `int16` */
export const int53__lean_int16_of_int = (a) => (a << 16) >> 16;

/** `Int32.ofInt`.
 *  @param {number} a `int53`
 *  @returns {number} `int32` */
export const int53__lean_int32_of_int = (a) => a | 0;

/** `Int8.ofInt`.
 *  @param {number} a `int53`
 *  @returns {number} `int8` */
export const int53__lean_int8_of_int = (a) => (a << 24) >> 24;

/** `Int64.toInt16`.
 *  @param {number} a `int53`
 *  @returns {number} `int16` */
export const int53__lean_int64_to_int16 = (a) => (a << 16) >> 16;

/** `Int64.toInt32`.
 *  @param {number} a `int53`
 *  @returns {number} `int32` */
export const int53__lean_int64_to_int32 = (a) => a | 0;

/** `Int64.toInt8`.
 *  @param {number} a `int53`
 *  @returns {number} `int8` */
export const int53__lean_int64_to_int8 = (a) => (a << 24) >> 24;

/** `Array.get!Internal`: `a[i]`, or the default `d` out of bounds.
 *  @template A, E the array layout `l : JsArrayLayout A E`: `A` is `array E`, or `typedArray t` with `E` = `terminal t.leaf`
 *  @param {E} d `E`
 *  @param {Array<E>|TypedArray} a `A`
 *  @param {bigint} i `bigint_nat`
 *  @returns {E} `E` */
export const bigint_nat__lean_array_get = (d, a, i) => {
  const k = Number(i);
  return k < a.length ? a[k] : d;
};

/** `Array.set!`: a copy with one element replaced (the array itself out of bounds).
 *  @template A, E the array layout `l : JsArrayLayout A E`: `A` is `array E`, or `typedArray t` with `E` = `terminal t.leaf`
 *  @param {Array<E>|TypedArray} a `A`
 *  @param {bigint} i `bigint_nat`
 *  @param {E} x `E`
 *  @returns {Array<E>|TypedArray} `A` */
export const bigint_nat__lean_array_set_immutable = (a, i, x) => {
  const k = Number(i);
  if (k >= a.length) return a;
  const r = a.slice();
  r[k] = x;
  return r;
};

/** `Array.set!`, in place.
 *  @template A, E the array layout `l : JsArrayLayout A E`: `A` is `array E`, or `typedArray t` with `E` = `terminal t.leaf`
 *  @param {Array<E>|TypedArray} a `A`
 *  @param {bigint} i `bigint_nat`
 *  @param {E} x `E`
 *  @returns {Array<E>|TypedArray} `A` */
export const bigint_nat__lean_array_set_mutable = (a, i, x) => {
  const k = Number(i);
  if (k < a.length) a[k] = x;
  return a;
};

/** `Array.swapIfInBounds`: a copy with two elements swapped (the array itself out of bounds).
 *  @template A, E the array layout `l : JsArrayLayout A E`: `A` is `array E`, or `typedArray t` with `E` = `terminal t.leaf`
 *  @param {Array<E>|TypedArray} a `A`
 *  @param {bigint} i `bigint_nat`
 *  @param {bigint} j `bigint_nat`
 *  @returns {Array<E>|TypedArray} `A` */
export const bigint_nat__lean_array_swap_immutable = (a, i, j) => {
  const k = Number(i);
  const l = Number(j);
  if (k >= a.length || l >= a.length) return a;
  const r = a.slice();
  const t = r[k];
  r[k] = r[l];
  r[l] = t;
  return r;
};

/** `Array.swapIfInBounds`, in place.
 *  @template A, E the array layout `l : JsArrayLayout A E`: `A` is `array E`, or `typedArray t` with `E` = `terminal t.leaf`
 *  @param {Array<E>|TypedArray} a `A`
 *  @param {bigint} i `bigint_nat`
 *  @param {bigint} j `bigint_nat`
 *  @returns {Array<E>|TypedArray} `A` */
export const bigint_nat__lean_array_swap_mutable = (a, i, j) => {
  const k = Number(i);
  const l = Number(j);
  if (k < a.length && l < a.length) {
    const t = a[k];
    a[k] = a[l];
    a[l] = t;
  }
  return a;
};

/** `Array.set`: a copy with one element replaced (the bound `i < a.size` is proved, so it is
 *  not checked).
 *  @template A, E the array layout `l : JsArrayLayout A E`: `A` is `array E`, or `typedArray t` with `E` = `terminal t.leaf`
 *  @param {Array<E>|TypedArray} a `A`
 *  @param {bigint} i `bigint_nat`
 *  @param {E} x `E`
 *  @returns {Array<E>|TypedArray} `A` */
export const bigint_nat__lean_array_fset_immutable = (a, i, x) => {
  const r = a.slice();
  r[Number(i)] = x;
  return r;
};

/** `Array.set`, in place (the bound is proved).
 *  @template A, E the array layout `l : JsArrayLayout A E`: `A` is `array E`, or `typedArray t` with `E` = `terminal t.leaf`
 *  @param {Array<E>|TypedArray} a `A`
 *  @param {bigint} i `bigint_nat`
 *  @param {E} x `E`
 *  @returns {Array<E>|TypedArray} `A` */
export const bigint_nat__lean_array_fset_mutable = (a, i, x) => {
  a[Number(i)] = x;
  return a;
};

/** `Array.swap`: a copy with two elements swapped (the bounds are proved, so they are not
 *  checked).
 *  @template A, E the array layout `l : JsArrayLayout A E`: `A` is `array E`, or `typedArray t` with `E` = `terminal t.leaf`
 *  @param {Array<E>|TypedArray} a `A`
 *  @param {bigint} i `bigint_nat`
 *  @param {bigint} j `bigint_nat`
 *  @returns {Array<E>|TypedArray} `A` */
export const bigint_nat__lean_array_fswap_immutable = (a, i, j) => {
  const k = Number(i);
  const l = Number(j);
  const r = a.slice();
  const t = r[k];
  r[k] = r[l];
  r[l] = t;
  return r;
};

/** `Array.swap`, in place (the bounds are proved).
 *  @template A, E the array layout `l : JsArrayLayout A E`: `A` is `array E`, or `typedArray t` with `E` = `terminal t.leaf`
 *  @param {Array<E>|TypedArray} a `A`
 *  @param {bigint} i `bigint_nat`
 *  @param {bigint} j `bigint_nat`
 *  @returns {Array<E>|TypedArray} `A` */
export const bigint_nat__lean_array_fswap_mutable = (a, i, j) => {
  const k = Number(i);
  const l = Number(j);
  const t = a[k];
  a[k] = a[l];
  a[l] = t;
  return a;
};

/** `Int16.ofNat`.
 *  @param {bigint} a `bigint_nat`
 *  @returns {number} `int16` */
export const bigint_nat__lean_int16_of_nat = bigint_int__lean_int16_of_int;

/** `Int32.ofNat`.
 *  @param {bigint} a `bigint_nat`
 *  @returns {number} `int32` */
export const bigint_nat__lean_int32_of_nat = bigint_int__lean_int32_of_int;

/** `Int8.ofNat`.
 *  @param {bigint} a `bigint_nat`
 *  @returns {number} `int8` */
export const bigint_nat__lean_int8_of_nat = bigint_int__lean_int8_of_int;

/** `Array.replicate`, on a generic array.
 *  @template α the element type
 *  @param {bigint} n `bigint_nat`
 *  @param {α} v `α`
 *  @returns {Array<α>} `array α` */
export const bigint_nat__lean_mk_array = (n, v) => new Array(Number(n)).fill(v);

/** `String.Internal.pushn`.
 *  @param {string} a `string`
 *  @param {string} b `string`
 *  @param {bigint} c `bigint_nat`
 *  @returns {string} `string` */
export const bigint_nat__lean_string_pushn = (a, b, c) => a + b.repeat(Number(c));

/** `UInt16.ofNat`, `UInt16.ofNatLT`.
 *  @param {bigint} a `bigint_nat`
 *  @returns {number} `uint16` */
export const bigint_nat__lean_uint16_of_nat__UInt16_ofNat = (a) => Number(BigInt.asUintN(16, a));

/** `Char.ofNatAux`.
 *  @param {bigint} a `bigint_nat`
 *  @returns {string} `string` */
export const bigint_nat__lean_uint32_of_nat__Char_ofNatAux = (a) => String.fromCodePoint(Number(a));

/** `UInt32.ofNat`, `UInt32.ofNatLT`.
 *  @param {bigint} a `bigint_nat`
 *  @returns {number} `uint32` */
export const bigint_nat__lean_uint32_of_nat__UInt32_ofNat = (a) => Number(BigInt.asUintN(32, a));

/** `UInt64.toUInt16`.
 *  @param {bigint} a `bigint_nat`
 *  @returns {number} `uint16` */
export const bigint_nat__lean_uint64_to_uint16 = (a) => Number(BigInt.asUintN(16, a));

/** `UInt64.toUInt32`.
 *  @param {bigint} a `bigint_nat`
 *  @returns {number} `uint32` */
export const bigint_nat__lean_uint64_to_uint32 = (a) => Number(BigInt.asUintN(32, a));

/** `UInt64.toUInt8`.
 *  @param {bigint} a `bigint_nat`
 *  @returns {number} `uint8` */
export const bigint_nat__lean_uint64_to_uint8 = (a) => Number(BigInt.asUintN(8, a));

/** `UInt8.ofNat`, `UInt8.ofNatLT`.
 *  @param {bigint} a `bigint_nat`
 *  @returns {number} `uint8` */
export const bigint_nat__lean_uint8_of_nat__UInt8_ofNat = (a) => Number(BigInt.asUintN(8, a));

/** `Bool.toInt16`.
 *  @param {boolean} a `bool`
 *  @returns {number} `int16` */
export const bool__lean_bool_to_int16 = (a) => a ? 1 : 0;

/** `Bool.toInt32`.
 *  @param {boolean} a `bool`
 *  @returns {number} `int32` */
export const bool__lean_bool_to_int32 = (a) => a ? 1 : 0;

/** `Bool.toInt8`.
 *  @param {boolean} a `bool`
 *  @returns {number} `int8` */
export const bool__lean_bool_to_int8 = (a) => a ? 1 : 0;

/** `Bool.toUInt16`.
 *  @param {boolean} a `bool`
 *  @returns {number} `uint16` */
export const bool__lean_bool_to_uint16 = (a) => a ? 1 : 0;

/** `Bool.toUInt32`.
 *  @param {boolean} a `bool`
 *  @returns {number} `uint32` */
export const bool__lean_bool_to_uint32 = (a) => a ? 1 : 0;

/** `Bool.toUInt8`.
 *  @param {boolean} a `bool`
 *  @returns {number} `uint8` */
export const bool__lean_bool_to_uint8 = (a) => a ? 1 : 0;

/** `Float32.add`.
 *  @param {number} a `float32`
 *  @param {number} b `float32`
 *  @returns {number} `float32` */
export const float32__lean_float32_add = (a, b) => Math.fround(a + b);

/** `Float32.div`.
 *  @param {number} a `float32`
 *  @param {number} b `float32`
 *  @returns {number} `float32` */
export const float32__lean_float32_div = (a, b) => Math.fround(a / b);

/** `Float32.isFinite`.
 *  @param {number} a `float32`
 *  @returns {boolean} `bool` */
export const float32__lean_float32_isfinite = (a) => Number.isFinite(a);

/** `Float32.isInf`.
 *  @param {number} a `float32`
 *  @returns {boolean} `bool` */
export const float32__lean_float32_isinf = (a) => a === Infinity || a === -Infinity;

/** `Float32.isNaN`.
 *  @param {number} a `float32`
 *  @returns {boolean} `bool` */
export const float32__lean_float32_isnan = (a) => Number.isNaN(a);

/** `Float32.mul`.
 *  @param {number} a `float32`
 *  @param {number} b `float32`
 *  @returns {number} `float32` */
export const float32__lean_float32_mul = (a, b) => Math.fround(a * b);

/** `Float32.sub`.
 *  @param {number} a `float32`
 *  @param {number} b `float32`
 *  @returns {number} `float32` */
export const float32__lean_float32_sub = (a, b) => Math.fround(a - b);

/** `Float.isFinite`.
 *  @param {number} a `float`
 *  @returns {boolean} `bool` */
export const float__lean_float_isfinite = (a) => Number.isFinite(a);

/** `Float.isInf`.
 *  @param {number} a `float`
 *  @returns {boolean} `bool` */
export const float__lean_float_isinf = (a) => a === Infinity || a === -Infinity;

/** `Float.isNaN`.
 *  @param {number} a `float`
 *  @returns {boolean} `bool` */
export const float__lean_float_isnan = (a) => Number.isNaN(a);

/** `Float.toFloat32`.
 *  @param {number} a `float`
 *  @returns {number} `float32` */
export const float__lean_float_to_float32 = (a) => Math.fround(a);

/** `UInt64.toFloat32` (on `BigInt`s).
 *  @param {bigint} a `bigint_nat`
 *  @returns {number} `float32` */
export const bigint_nat__lean_uint64_to_float32 = (a) => $bigToF32(a);

/** `Int64.toFloat32` (on `BigInt`s).
 *  @param {bigint} a `bigint_int`
 *  @returns {number} `float32` */
export const bigint_int__lean_int64_to_float32 = (a) => $bigToF32(a);

/** `Int16.abs`.
 *  @param {number} a `int16`
 *  @returns {number} `int16` */
export const int16__lean_int16_abs = (a) => (Math.abs(a) << 16) >> 16;

/** `Int16.add`.
 *  @param {number} a `int16`
 *  @param {number} b `int16`
 *  @returns {number} `int16` */
export const int16__lean_int16_add = (a, b) => ((a + b) << 16) >> 16;

/** `Int16.complement`.
 *  @param {number} a `int16`
 *  @returns {number} `int16` */
export const int16__lean_int16_complement = (a) => (~a << 16) >> 16;

/** `Int16.div`.
 *  @param {number} a `int16`
 *  @param {number} b `int16`
 *  @returns {number} `int16` */
export const int16__lean_int16_div = (a, b) => b === 0 ? 0 : (Math.trunc(a / b) << 16) >> 16;

/** `Int16.land`.
 *  @param {number} a `int16`
 *  @param {number} b `int16`
 *  @returns {number} `int16` */
export const int16__lean_int16_land = (a, b) => ((a & b) << 16) >> 16;

/** `Int16.lor`.
 *  @param {number} a `int16`
 *  @param {number} b `int16`
 *  @returns {number} `int16` */
export const int16__lean_int16_lor = (a, b) => ((a | b) << 16) >> 16;

/** `Int16.mod`.
 *  @param {number} a `int16`
 *  @param {number} b `int16`
 *  @returns {number} `int16` */
export const int16__lean_int16_mod = (a, b) => b === 0 ? a : a % b;

/** `Int16.mul`.
 *  @param {number} a `int16`
 *  @param {number} b `int16`
 *  @returns {number} `int16` */
export const int16__lean_int16_mul = (a, b) => ((a * b) << 16) >> 16;

/** `Int16.neg`.
 *  @param {number} a `int16`
 *  @returns {number} `int16` */
export const int16__lean_int16_neg = (a) => (-a << 16) >> 16;

/** `Int16.shiftLeft`.
 *  @param {number} a `int16`
 *  @param {number} b `int16`
 *  @returns {number} `int16` */
export const int16__lean_int16_shift_left = (a, b) => ((a << (((b % 16) + 16) % 16)) << 16) >> 16;

/** `Int16.shiftRight`.
 *  @param {number} a `int16`
 *  @param {number} b `int16`
 *  @returns {number} `int16` */
export const int16__lean_int16_shift_right = (a, b) => a >> (((b % 16) + 16) % 16);

/** `Int16.sub`.
 *  @param {number} a `int16`
 *  @param {number} b `int16`
 *  @returns {number} `int16` */
export const int16__lean_int16_sub = (a, b) => ((a - b) << 16) >> 16;

/** `Int16.toInt8`.
 *  @param {number} a `int16`
 *  @returns {number} `int8` */
export const int16__lean_int16_to_int8 = (a) => (a << 24) >> 24;

/** `Int16.xor`.
 *  @param {number} a `int16`
 *  @param {number} b `int16`
 *  @returns {number} `int16` */
export const int16__lean_int16_xor = (a, b) => ((a ^ b) << 16) >> 16;

/** `Int32.abs`.
 *  @param {number} a `int32`
 *  @returns {number} `int32` */
export const int32__lean_int32_abs = (a) => Math.abs(a) | 0;

/** `Int32.add`.
 *  @param {number} a `int32`
 *  @param {number} b `int32`
 *  @returns {number} `int32` */
export const int32__lean_int32_add = (a, b) => (a + b) | 0;

/** `Int32.complement`.
 *  @param {number} a `int32`
 *  @returns {number} `int32` */
export const int32__lean_int32_complement = (a) => ~a | 0;

/** `Int32.div`.
 *  @param {number} a `int32`
 *  @param {number} b `int32`
 *  @returns {number} `int32` */
export const int32__lean_int32_div = (a, b) => b === 0 ? 0 : Math.trunc(a / b) | 0;

/** `Int32.land`.
 *  @param {number} a `int32`
 *  @param {number} b `int32`
 *  @returns {number} `int32` */
export const int32__lean_int32_land = (a, b) => (a & b) | 0;

/** `Int32.lor`.
 *  @param {number} a `int32`
 *  @param {number} b `int32`
 *  @returns {number} `int32` */
export const int32__lean_int32_lor = (a, b) => a | b | 0;

/** `Int32.mod`.
 *  @param {number} a `int32`
 *  @param {number} b `int32`
 *  @returns {number} `int32` */
export const int32__lean_int32_mod = (a, b) => b === 0 ? a : a % b;

/** `Int32.mul`.
 *  @param {number} a `int32`
 *  @param {number} b `int32`
 *  @returns {number} `int32` */
export const int32__lean_int32_mul = (a, b) => Math.imul(a, b) | 0;

/** `Int32.neg`.
 *  @param {number} a `int32`
 *  @returns {number} `int32` */
export const int32__lean_int32_neg = (a) => -a | 0;

/** `Int32.shiftLeft`.
 *  @param {number} a `int32`
 *  @param {number} b `int32`
 *  @returns {number} `int32` */
export const int32__lean_int32_shift_left = (a, b) => (a << (((b % 32) + 32) % 32)) | 0;

/** `Int32.shiftRight`.
 *  @param {number} a `int32`
 *  @param {number} b `int32`
 *  @returns {number} `int32` */
export const int32__lean_int32_shift_right = (a, b) => a >> (((b % 32) + 32) % 32);

/** `Int32.sub`.
 *  @param {number} a `int32`
 *  @param {number} b `int32`
 *  @returns {number} `int32` */
export const int32__lean_int32_sub = (a, b) => (a - b) | 0;

/** `Int32.toInt16`.
 *  @param {number} a `int32`
 *  @returns {number} `int16` */
export const int32__lean_int32_to_int16 = (a) => (a << 16) >> 16;

/** `Int32.toInt8`.
 *  @param {number} a `int32`
 *  @returns {number} `int8` */
export const int32__lean_int32_to_int8 = (a) => (a << 24) >> 24;

/** `Int32.xor`.
 *  @param {number} a `int32`
 *  @param {number} b `int32`
 *  @returns {number} `int32` */
export const int32__lean_int32_xor = (a, b) => (a ^ b) | 0;

/** `Int8.abs`.
 *  @param {number} a `int8`
 *  @returns {number} `int8` */
export const int8__lean_int8_abs = (a) => (Math.abs(a) << 24) >> 24;

/** `Int8.add`.
 *  @param {number} a `int8`
 *  @param {number} b `int8`
 *  @returns {number} `int8` */
export const int8__lean_int8_add = (a, b) => ((a + b) << 24) >> 24;

/** `Int8.complement`.
 *  @param {number} a `int8`
 *  @returns {number} `int8` */
export const int8__lean_int8_complement = (a) => (~a << 24) >> 24;

/** `Int8.div`.
 *  @param {number} a `int8`
 *  @param {number} b `int8`
 *  @returns {number} `int8` */
export const int8__lean_int8_div = (a, b) => b === 0 ? 0 : (Math.trunc(a / b) << 24) >> 24;

/** `Int8.land`.
 *  @param {number} a `int8`
 *  @param {number} b `int8`
 *  @returns {number} `int8` */
export const int8__lean_int8_land = (a, b) => ((a & b) << 24) >> 24;

/** `Int8.lor`.
 *  @param {number} a `int8`
 *  @param {number} b `int8`
 *  @returns {number} `int8` */
export const int8__lean_int8_lor = (a, b) => ((a | b) << 24) >> 24;

/** `Int8.mod`.
 *  @param {number} a `int8`
 *  @param {number} b `int8`
 *  @returns {number} `int8` */
export const int8__lean_int8_mod = (a, b) => b === 0 ? a : a % b;

/** `Int8.mul`.
 *  @param {number} a `int8`
 *  @param {number} b `int8`
 *  @returns {number} `int8` */
export const int8__lean_int8_mul = (a, b) => ((a * b) << 24) >> 24;

/** `Int8.neg`.
 *  @param {number} a `int8`
 *  @returns {number} `int8` */
export const int8__lean_int8_neg = (a) => (-a << 24) >> 24;

/** `Int8.shiftLeft`.
 *  @param {number} a `int8`
 *  @param {number} b `int8`
 *  @returns {number} `int8` */
export const int8__lean_int8_shift_left = (a, b) => ((a << (((b % 8) + 8) % 8)) << 24) >> 24;

/** `Int8.shiftRight`.
 *  @param {number} a `int8`
 *  @param {number} b `int8`
 *  @returns {number} `int8` */
export const int8__lean_int8_shift_right = (a, b) => a >> (((b % 8) + 8) % 8);

/** `Int8.sub`.
 *  @param {number} a `int8`
 *  @param {number} b `int8`
 *  @returns {number} `int8` */
export const int8__lean_int8_sub = (a, b) => ((a - b) << 24) >> 24;

/** `Int8.xor`.
 *  @param {number} a `int8`
 *  @param {number} b `int8`
 *  @returns {number} `int8` */
export const int8__lean_int8_xor = (a, b) => ((a ^ b) << 24) >> 24;

/** `String.compare`.
 *  @param {string} a `string`
 *  @param {string} b `string`
 *  @returns {number} `enum 3 (-1)` */
export const string__lean_string_compare = (a, b) => a < b ? -1 : a === b ? 0 : 1;

/** `String.data`, `String.toList`.
 *  @param {string} a `string`
 *  @returns {Array<string>} `list string` */
export const string__lean_string_data__String_data = (a) => [...a];

/** `String.Internal.isEmpty`.
 *  @param {string} a `string`
 *  @returns {boolean} `bool` */
export const string__lean_string_isempty = (a) => a.length === 0;

/**
 * `String.Slice.Pattern.Internal.memcmpStr`: are the `len` bytes of `lhs` at `lstart`
 * the same as the `len` bytes of `rhs` at `rstart`?
 *  @param {string} lhs `string`
 *  @param {string} rhs `string`
 *  @param {number} lstart `uint53`
 *  @param {number} rstart `uint53`
 *  @param {number} len `uint53`
 *  @returns {boolean} `bool` */
export const string__lean_string_memcmp = (lhs, rhs, lstart, rstart, len) => {
  const l = encoder.encode(lhs);
  const r = encoder.encode(rhs);
  for (let i = 0; i < len; i++) {
    if (l[lstart + i] !== r[rstart + i]) return false;
  }
  return true;
};

/** `String.ofList`, `String.mk`.
 *  @param {Array<string>} a `list string`
 *  @returns {string} `string` */
export const string__lean_string_mk__String_mk = (a) => a.join("");

/** `String.Internal.atEnd`, `String.atEnd`, `String.Pos.Raw.atEnd`.
 *  @param {string} a `string`
 *  @param {number} b `uint53`
 *  @returns {boolean} `bool` */
export const string__lean_string_utf8_at_end__String_Internal_atEnd = (a, b) => b >= $utf8(a).length;

/** `String.Internal.extract`, `String.Pos.Raw.extract`.
 *  @param {string} a `string`
 *  @param {number} b `uint53`
 *  @param {number} c `uint53`
 *  @returns {string} `string` */
export const string__lean_string_utf8_extract__String_Internal_extract = (a, b, c) => $utf8Extract(a, b, c);

/** `String.Internal.get`, `String.Pos.Raw.get`, `String.get`.
 *  @param {string} a `string`
 *  @param {number} b `uint53`
 *  @returns {string} `string` */
export const string__lean_string_utf8_get__String_Internal_get = (a, b) => $get(a, b);

/** `String.Internal.next`, `String.next`, `String.Pos.Raw.next`.
 *  @param {string} a `string`
 *  @param {number} b `uint53`
 *  @returns {number} `uint53` */
export const string__lean_string_utf8_next__String_Internal_next = (a, b) => $next(a, b);

/** `String.Pos.Raw.set`, `String.set`.
 *  @param {string} a `string`
 *  @param {number} b `uint53`
 *  @param {string} c `string`
 *  @returns {string} `string` */
export const string__lean_string_utf8_set__String_Pos_Raw_set = (a, b, c) => $utf8Set(a, b, c);

/** `Thunk.mk`: a memoised delay of the function `f`.
 *  @template α the delayed type
 *  @param {function(): α} f `fn [] α`
 *  @returns {Thunk<α>} `thunk α` */
export const thunk__lean_mk_thunk = (f) => ({ f, v: undefined, done: false });

/** `Thunk.get`: the value of a memoised delay, computed the first time.
 *  @template α the delayed type
 *  @param {Thunk<α>} t `thunk α`
 *  @returns {α} `α` */
export const thunk__lean_thunk_get_own = (t) => {
  if (!t.done) {
    t.v = t.f();
    t.done = true;
    t.f = undefined;
  }
  return t.v;
};

/** `Thunk.pure`: a memoised delay whose value is already known.
 *  @template α the delayed type
 *  @param {α} v `α`
 *  @returns {Thunk<α>} `thunk α` */
export const thunk__lean_thunk_pure = (v) => ({ f: undefined, v, done: true });

/** `Array.replicate`, on the typed array of constructor `C` (`Uint8Array`, …).
 *  @template t the typed-array element (`JsTypedElem`); `TypedArray` is `t.kind`
 *  @param {function(new:TypedArray, number)} C `t.kind` (the typed-array constructor)
 *  @param {bigint} n `bigint_nat`
 *  @param {number|bigint} v `t.leaf`
 *  @returns {TypedArray} `typedArray t` */
export const typedArray__bigint_nat__lean_mk_array = (C, n, v) => new C(Number(n)).fill(v);

/** `Array.toList`: the list of an array, generic or typed (a list is a generic array).
 *  @template t the typed-array element (`JsTypedElem`); `TypedArray` is `t.kind`
 *  @param {TypedArray} a `typedArray t`
 *  @returns {Array<number|bigint>} `list t.leaf` */
export const typedArray__lean_array_to_list = (a) => Array.from(a);

/** The empty list of cons cells (`ListRepr.taggedUnion`): `{ tag: 0 }`, shared. */
const $consNil = Object.freeze({ tag: 0 });

/** A `List` as cons cells (`ListRepr.taggedUnion`) from its array layout: `[a, b]` is
 *  `{ tag: 1, _1: a, _2: { tag: 1, _1: b, _2: { tag: 0 } } }`.  Linear, built from the end.
 *  @template α
 *  @param {Array<α>} a `list α`
 *  @returns {({tag: 0}|{tag: 1, _1: α, _2: *})} `consList α` */
export const consList__of_array = (a) => consList__of_array_onto(a, $consNil);

/** The cons cells of the elements of an array in front of the cons cells `l`, which are shared,
 *  not copied (`ListRepr.taggedUnion`): `(a.toList ++ l)` in `O(a.length)`.
 *  @template α
 *  @param {Array<α>} a `list α`
 *  @param {({tag: 0}|{tag: 1, _1: α, _2: *})} l `consList α`
 *  @returns {({tag: 0}|{tag: 1, _1: α, _2: *})} `consList α` */
export const consList__of_array_onto = (a, l) => {
  for (let i = a.length - 1; i >= 0; i--) l = { tag: 1, _1: a[i], _2: l };
  return l;
};

/** `l ++ t` on cons cells (`ListRepr.taggedUnion`): copies of the cells of `l` in front of the
 *  cells `t`, which are shared (`l` itself when `t` is empty).
 *  @template α
 *  @param {({tag: 0}|{tag: 1, _1: α, _2: *})} l `consList α`
 *  @param {({tag: 0}|{tag: 1, _1: α, _2: *})} t `consList α`
 *  @returns {({tag: 0}|{tag: 1, _1: α, _2: *})} `consList α` */
export const consList__append = (l, t) =>
  t.tag === 0 ? l : consList__of_array_onto(consList__to_array(l), t);

/** The array layout of a `List` of cons cells (`ListRepr.taggedUnion`): the elements, in order.
 *  @template α
 *  @param {({tag: 0}|{tag: 1, _1: α, _2: *})} l `consList α`
 *  @returns {Array<α>} `list α` */
export const consList__to_array = (l) => {
  const a = [];
  for (; l.tag === 1; l = l._2) a.push(l._1);
  return a;
};

/** A union whose constructors are all objects (`JsRepr.cells`: `{ tag: i }` for a constructor
 *  without fields), with its constructors without fields as the numbers of their positions
 *  (`JsRepr.smallIntNullary`): how the generated code takes a union an operation answers.
 *  A constructor without fields is the object with no field `_1`.
 *  @param {{tag: number}} u `obj (union ar cells) args`
 *  @returns {number|{tag: number}} `obj (union ar smallIntNullary) args` */
export const obj__nullary_to_int = (u) => ("_1" in u ? u : u.tag);

/** A union whose constructors without fields are numbers (`JsRepr.smallIntNullary`), with every
 *  constructor an object (`JsRepr.cells`): how the generated code passes a union to an
 *  operation.
 *  @param {number|{tag: number}} u `obj (union ar smallIntNullary) args`
 *  @returns {{tag: number}} `obj (union ar cells) args` */
export const obj__nullary_to_cells = (u) => (typeof u === "number" ? { tag: u } : u);

/** `Array.replicate`, on the typed array of constructor `C` (`Uint8Array`, …).
 *  @template t the typed-array element (`JsTypedElem`); `TypedArray` is `t.kind`
 *  @param {function(new:TypedArray, number)} C `t.kind` (the typed-array constructor)
 *  @param {number} n `uint53`
 *  @param {number|bigint} v `t.leaf`
 *  @returns {TypedArray} `typedArray t` */
export const typedArray__uint53__lean_mk_array = (C, n, v) => new C(n).fill(v);

/** `UInt16.add`.
 *  @param {number} a `uint16`
 *  @param {number} b `uint16`
 *  @returns {number} `uint16` */
export const uint16__lean_uint16_add = (a, b) => (a + b) & 65535;

/** `UInt16.complement`.
 *  @param {number} a `uint16`
 *  @returns {number} `uint16` */
export const uint16__lean_uint16_complement = (a) => ~a & 65535;

/** `UInt16.div`.
 *  @param {number} a `uint16`
 *  @param {number} b `uint16`
 *  @returns {number} `uint16` */
export const uint16__lean_uint16_div = (a, b) => b === 0 ? 0 : Math.floor(a / b);

/** `UInt16.land`.
 *  @param {number} a `uint16`
 *  @param {number} b `uint16`
 *  @returns {number} `uint16` */
export const uint16__lean_uint16_land = (a, b) => a & b & 65535;

/** `UInt16.log2`.
 *  @param {number} a `uint16`
 *  @returns {number} `uint16` */
export const uint16__lean_uint16_log2 = (a) => a === 0 ? 0 : 31 - Math.clz32(a);

/** `UInt16.lor`.
 *  @param {number} a `uint16`
 *  @param {number} b `uint16`
 *  @returns {number} `uint16` */
export const uint16__lean_uint16_lor = (a, b) => (a | b) & 65535;

/** `UInt16.mod`.
 *  @param {number} a `uint16`
 *  @param {number} b `uint16`
 *  @returns {number} `uint16` */
export const uint16__lean_uint16_mod = (a, b) => b === 0 ? a : a % b;

/** `UInt16.mul`.
 *  @param {number} a `uint16`
 *  @param {number} b `uint16`
 *  @returns {number} `uint16` */
export const uint16__lean_uint16_mul = (a, b) => (a * b) & 65535;

/** `UInt16.neg`.
 *  @param {number} a `uint16`
 *  @returns {number} `uint16` */
export const uint16__lean_uint16_neg = (a) => -a & 65535;

/** `UInt16.shiftLeft`.
 *  @param {number} a `uint16`
 *  @param {number} b `uint16`
 *  @returns {number} `uint16` */
export const uint16__lean_uint16_shift_left = (a, b) => (a << (((b % 16) + 16) % 16)) & 65535;

/** `UInt16.shiftRight`.
 *  @param {number} a `uint16`
 *  @param {number} b `uint16`
 *  @returns {number} `uint16` */
export const uint16__lean_uint16_shift_right = (a, b) => a >>> (b % 16);

/** `UInt16.sub`.
 *  @param {number} a `uint16`
 *  @param {number} b `uint16`
 *  @returns {number} `uint16` */
export const uint16__lean_uint16_sub = (a, b) => (a - b) & 65535;

/** `UInt16.toUInt8`.
 *  @param {number} a `uint16`
 *  @returns {number} `uint8` */
export const uint16__lean_uint16_to_uint8 = (a) => a & 255;

/** `UInt16.xor`.
 *  @param {number} a `uint16`
 *  @param {number} b `uint16`
 *  @returns {number} `uint16` */
export const uint16__lean_uint16_xor = (a, b) => (a ^ b) & 65535;

/** `UInt32.add`.
 *  @param {number} a `uint32`
 *  @param {number} b `uint32`
 *  @returns {number} `uint32` */
export const uint32__lean_uint32_add = (a, b) => (a + b) >>> 0;

/** `UInt32.complement`.
 *  @param {number} a `uint32`
 *  @returns {number} `uint32` */
export const uint32__lean_uint32_complement = (a) => ~a >>> 0;

/** `UInt32.div`.
 *  @param {number} a `uint32`
 *  @param {number} b `uint32`
 *  @returns {number} `uint32` */
export const uint32__lean_uint32_div = (a, b) => b === 0 ? 0 : Math.floor(a / b);

/** `UInt32.land`.
 *  @param {number} a `uint32`
 *  @param {number} b `uint32`
 *  @returns {number} `uint32` */
export const uint32__lean_uint32_land = (a, b) => (a & b) >>> 0;

/** `UInt32.log2`.
 *  @param {number} a `uint32`
 *  @returns {number} `uint32` */
export const uint32__lean_uint32_log2 = (a) => a === 0 ? 0 : 31 - Math.clz32(a);

/** `UInt32.lor`.
 *  @param {number} a `uint32`
 *  @param {number} b `uint32`
 *  @returns {number} `uint32` */
export const uint32__lean_uint32_lor = (a, b) => (a | b) >>> 0;

/** `UInt32.mod`.
 *  @param {number} a `uint32`
 *  @param {number} b `uint32`
 *  @returns {number} `uint32` */
export const uint32__lean_uint32_mod = (a, b) => b === 0 ? a : a % b;

/** `UInt32.mul`.
 *  @param {number} a `uint32`
 *  @param {number} b `uint32`
 *  @returns {number} `uint32` */
export const uint32__lean_uint32_mul = (a, b) => Math.imul(a, b) >>> 0;

/** `UInt32.neg`.
 *  @param {number} a `uint32`
 *  @returns {number} `uint32` */
export const uint32__lean_uint32_neg = (a) => -a >>> 0;

/** `UInt32.shiftLeft`.
 *  @param {number} a `uint32`
 *  @param {number} b `uint32`
 *  @returns {number} `uint32` */
export const uint32__lean_uint32_shift_left = (a, b) => (a << (((b % 32) + 32) % 32)) >>> 0;

/** `UInt32.shiftRight`.
 *  @param {number} a `uint32`
 *  @param {number} b `uint32`
 *  @returns {number} `uint32` */
export const uint32__lean_uint32_shift_right = (a, b) => a >>> (b % 32);

/** `UInt32.sub`.
 *  @param {number} a `uint32`
 *  @param {number} b `uint32`
 *  @returns {number} `uint32` */
export const uint32__lean_uint32_sub = (a, b) => (a - b) >>> 0;

/** `UInt32.toUInt16`.
 *  @param {number} a `uint32`
 *  @returns {number} `uint16` */
export const uint32__lean_uint32_to_uint16 = (a) => a & 65535;

/** `UInt32.toUInt8`.
 *  @param {number} a `uint32`
 *  @returns {number} `uint8` */
export const uint32__lean_uint32_to_uint8 = (a) => a & 255;

/** `UInt32.xor`.
 *  @param {number} a `uint32`
 *  @param {number} b `uint32`
 *  @returns {number} `uint32` */
export const uint32__lean_uint32_xor = (a, b) => (a ^ b) >>> 0;

/** `Array.get!Internal`: `a[i]`, or the default `d` out of bounds.
 *  @template A, E the array layout `l : JsArrayLayout A E`: `A` is `array E`, or `typedArray t` with `E` = `terminal t.leaf`
 *  @param {E} d `E`
 *  @param {Array<E>|TypedArray} a `A`
 *  @param {number} i `uint53`
 *  @returns {E} `E` */
export const uint53__lean_array_get = (d, a, i) => (i < a.length ? a[i] : d);

/** `Array.set!`: a copy with one element replaced (the array itself out of bounds).
 *  @template A, E the array layout `l : JsArrayLayout A E`: `A` is `array E`, or `typedArray t` with `E` = `terminal t.leaf`
 *  @param {Array<E>|TypedArray} a `A`
 *  @param {number} i `uint53`
 *  @param {E} x `E`
 *  @returns {Array<E>|TypedArray} `A` */
export const uint53__lean_array_set_immutable = (a, i, x) => {
  if (i >= a.length) return a;
  const r = a.slice();
  r[i] = x;
  return r;
};

/** `Array.set!`, in place.
 *  @template A, E the array layout `l : JsArrayLayout A E`: `A` is `array E`, or `typedArray t` with `E` = `terminal t.leaf`
 *  @param {Array<E>|TypedArray} a `A`
 *  @param {number} i `uint53`
 *  @param {E} x `E`
 *  @returns {Array<E>|TypedArray} `A` */
export const uint53__lean_array_set_mutable = (a, i, x) => {
  if (i < a.length) a[i] = x;
  return a;
};

/** `Array.swapIfInBounds`: a copy with two elements swapped (the array itself out of bounds).
 *  @template A, E the array layout `l : JsArrayLayout A E`: `A` is `array E`, or `typedArray t` with `E` = `terminal t.leaf`
 *  @param {Array<E>|TypedArray} a `A`
 *  @param {number} i `uint53`
 *  @param {number} j `uint53`
 *  @returns {Array<E>|TypedArray} `A` */
export const uint53__lean_array_swap_immutable = (a, i, j) => {
  if (i >= a.length || j >= a.length) return a;
  const r = a.slice();
  const t = r[i];
  r[i] = r[j];
  r[j] = t;
  return r;
};

/** `Array.swapIfInBounds`, in place.
 *  @template A, E the array layout `l : JsArrayLayout A E`: `A` is `array E`, or `typedArray t` with `E` = `terminal t.leaf`
 *  @param {Array<E>|TypedArray} a `A`
 *  @param {number} i `uint53`
 *  @param {number} j `uint53`
 *  @returns {Array<E>|TypedArray} `A` */
export const uint53__lean_array_swap_mutable = (a, i, j) => {
  if (i < a.length && j < a.length) {
    const t = a[i];
    a[i] = a[j];
    a[j] = t;
  }
  return a;
};

/** `Array.set`: a copy with one element replaced (the bound `i < a.size` is proved, so it is
 *  not checked).
 *  @template A, E the array layout `l : JsArrayLayout A E`: `A` is `array E`, or `typedArray t` with `E` = `terminal t.leaf`
 *  @param {Array<E>|TypedArray} a `A`
 *  @param {number} i `uint53`
 *  @param {E} x `E`
 *  @returns {Array<E>|TypedArray} `A` */
export const uint53__lean_array_fset_immutable = (a, i, x) => {
  const r = a.slice();
  r[i] = x;
  return r;
};

/** `Array.set`, in place (the bound is proved).
 *  @template A, E the array layout `l : JsArrayLayout A E`: `A` is `array E`, or `typedArray t` with `E` = `terminal t.leaf`
 *  @param {Array<E>|TypedArray} a `A`
 *  @param {number} i `uint53`
 *  @param {E} x `E`
 *  @returns {Array<E>|TypedArray} `A` */
export const uint53__lean_array_fset_mutable = (a, i, x) => {
  a[i] = x;
  return a;
};

/** `Array.swap`: a copy with two elements swapped (the bounds are proved, so they are not
 *  checked).
 *  @template A, E the array layout `l : JsArrayLayout A E`: `A` is `array E`, or `typedArray t` with `E` = `terminal t.leaf`
 *  @param {Array<E>|TypedArray} a `A`
 *  @param {number} i `uint53`
 *  @param {number} j `uint53`
 *  @returns {Array<E>|TypedArray} `A` */
export const uint53__lean_array_fswap_immutable = (a, i, j) => {
  const r = a.slice();
  const t = r[i];
  r[i] = r[j];
  r[j] = t;
  return r;
};

/** `Array.swap`, in place (the bounds are proved).
 *  @template A, E the array layout `l : JsArrayLayout A E`: `A` is `array E`, or `typedArray t` with `E` = `terminal t.leaf`
 *  @param {Array<E>|TypedArray} a `A`
 *  @param {number} i `uint53`
 *  @param {number} j `uint53`
 *  @returns {Array<E>|TypedArray} `A` */
export const uint53__lean_array_fswap_mutable = (a, i, j) => {
  const t = a[i];
  a[i] = a[j];
  a[j] = t;
  return a;
};

/** `Int16.ofNat`.
 *  @param {number} a `uint53`
 *  @returns {number} `int16` */
export const uint53__lean_int16_of_nat = int53__lean_int16_of_int;

/** `Int32.ofNat`.
 *  @param {number} a `uint53`
 *  @returns {number} `int32` */
export const uint53__lean_int32_of_nat = int53__lean_int32_of_int;

/** `Int8.ofNat`.
 *  @param {number} a `uint53`
 *  @returns {number} `int8` */
export const uint53__lean_int8_of_nat = int53__lean_int8_of_int;

/** `Array.replicate`, on a generic array.
 *  @template α the element type
 *  @param {number} n `uint53`
 *  @param {α} v `α`
 *  @returns {Array<α>} `array α` */
export const uint53__lean_mk_array = (n, v) => new Array(n).fill(v);

/** `String.Internal.pushn`.
 *  @param {string} a `string`
 *  @param {string} b `string`
 *  @param {number} c `uint53`
 *  @returns {string} `string` */
export const uint53__lean_string_pushn = (a, b, c) => a + b.repeat(c);

/** `String.Pos.Raw.set`, `String.set`.
 *  @param {string} a `string`
 *  @param {number} b `uint53`
 *  @param {string} c `string`
 *  @returns {string} `string` */
export const string__lean_string_utf8_set__String_Pos_set = (a, b, c) => $utf8Set(a, b, c);

/** `UInt16.ofNat`, `UInt16.ofNatLT` (`ToInt32` takes a safe integer modulo `2^32`).
 *  @param {number} a `uint53`
 *  @returns {number} `uint16` */
export const uint53__lean_uint16_of_nat__UInt16_ofNat = (a) => a & 65535;

/** `Char.ofNatAux`.
 *  @param {number} a `uint53`
 *  @returns {string} `string` */
export const uint53__lean_uint32_of_nat__Char_ofNatAux = (a) => String.fromCodePoint(a);

/** `UInt32.ofNat`, `UInt32.ofNatLT`.
 *  @param {number} a `uint53`
 *  @returns {number} `uint32` */
export const uint53__lean_uint32_of_nat__UInt32_ofNat = (a) => a >>> 0;

/** `UInt64.toUInt16`.
 *  @param {number} a `uint53`
 *  @returns {number} `uint16` */
export const uint53__lean_uint64_to_uint16 = (a) => a & 65535;

/** `UInt64.toUInt32`.
 *  @param {number} a `uint53`
 *  @returns {number} `uint32` */
export const uint53__lean_uint64_to_uint32 = (a) => a >>> 0;

/** `UInt64.toUInt8`.
 *  @param {number} a `uint53`
 *  @returns {number} `uint8` */
export const uint53__lean_uint64_to_uint8 = (a) => a & 255;

/** `UInt8.ofNat`, `UInt8.ofNatLT`.
 *  @param {number} a `uint53`
 *  @returns {number} `uint8` */
export const uint53__lean_uint8_of_nat__UInt8_ofNat = (a) => a & 255;

/** `UInt8.add`.
 *  @param {number} a `uint8`
 *  @param {number} b `uint8`
 *  @returns {number} `uint8` */
export const uint8__lean_uint8_add = (a, b) => (a + b) & 255;

/** `UInt8.complement`.
 *  @param {number} a `uint8`
 *  @returns {number} `uint8` */
export const uint8__lean_uint8_complement = (a) => ~a & 255;

/** `UInt8.div`.
 *  @param {number} a `uint8`
 *  @param {number} b `uint8`
 *  @returns {number} `uint8` */
export const uint8__lean_uint8_div = (a, b) => b === 0 ? 0 : Math.floor(a / b);

/** `UInt8.land`.
 *  @param {number} a `uint8`
 *  @param {number} b `uint8`
 *  @returns {number} `uint8` */
export const uint8__lean_uint8_land = (a, b) => a & b & 255;

/** `UInt8.log2`.
 *  @param {number} a `uint8`
 *  @returns {number} `uint8` */
export const uint8__lean_uint8_log2 = (a) => a === 0 ? 0 : 31 - Math.clz32(a);

/** `UInt8.lor`.
 *  @param {number} a `uint8`
 *  @param {number} b `uint8`
 *  @returns {number} `uint8` */
export const uint8__lean_uint8_lor = (a, b) => (a | b) & 255;

/** `UInt8.mod`.
 *  @param {number} a `uint8`
 *  @param {number} b `uint8`
 *  @returns {number} `uint8` */
export const uint8__lean_uint8_mod = (a, b) => b === 0 ? a : a % b;

/** `UInt8.mul`.
 *  @param {number} a `uint8`
 *  @param {number} b `uint8`
 *  @returns {number} `uint8` */
export const uint8__lean_uint8_mul = (a, b) => (a * b) & 255;

/** `UInt8.neg`.
 *  @param {number} a `uint8`
 *  @returns {number} `uint8` */
export const uint8__lean_uint8_neg = (a) => -a & 255;

/** `UInt8.shiftLeft`.
 *  @param {number} a `uint8`
 *  @param {number} b `uint8`
 *  @returns {number} `uint8` */
export const uint8__lean_uint8_shift_left = (a, b) => (a << (((b % 8) + 8) % 8)) & 255;

/** `UInt8.shiftRight`.
 *  @param {number} a `uint8`
 *  @param {number} b `uint8`
 *  @returns {number} `uint8` */
export const uint8__lean_uint8_shift_right = (a, b) => a >>> (b % 8);

/** `UInt8.sub`.
 *  @param {number} a `uint8`
 *  @param {number} b `uint8`
 *  @returns {number} `uint8` */
export const uint8__lean_uint8_sub = (a, b) => (a - b) & 255;

/** `UInt8.xor`.
 *  @param {number} a `uint8`
 *  @param {number} b `uint8`
 *  @returns {number} `uint8` */
export const uint8__lean_uint8_xor = (a, b) => (a ^ b) & 255;

/* ------------------------------------------------------------ nat_bigint */

/** `Int.natAbs`.
 *  @param {bigint} a `bigint_int`
 *  @returns {bigint} `bigint_nat` */
export const bigint_int__bigint_nat__lean_nat_abs = (a) => (a < 0n ? -a : a);

/** `Nat.div`.
 *  @param {bigint} a `bigint_nat`
 *  @param {bigint} b `bigint_nat`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_nat_div = (a, b) => b === 0n ? 0n : a / b;

/** `Nat.divExact`.
 *  @param {bigint} a `bigint_nat`
 *  @param {bigint} b `bigint_nat`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_nat_div_exact = (a, b) => b === 0n ? 0n : a / b;

/** `Nat.log2`.
 *  @param {bigint} a `bigint_nat`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_nat_log2 = (a) => a === 0n ? 0n : BigInt(a.toString(2).length - 1);

/** `Nat.modCore`, `Nat.mod`.
 *  @param {bigint} a `bigint_nat`
 *  @param {bigint} b `bigint_nat`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_nat_mod__Nat_mod = (a, b) => b === 0n ? a : a % b;

/** `Nat.pow`.
 *  @param {bigint} a `bigint_nat`
 *  @param {bigint} b `bigint_nat`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_nat_pow = (a, b) => $bigPow(a, b);

/** `Nat.pred`.
 *  @param {bigint} a `bigint_nat`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_nat_pred = (a) => a > 0n ? a - 1n : 0n;

/** `Nat.sub`.
 *  @param {bigint} a `bigint_nat`
 *  @param {bigint} b `bigint_nat`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_nat_sub = (a, b) => a > b ? a - b : 0n;

/** `String.Internal.length`, `String.length`.
 *  @param {string} a `string`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_string_length__String_Internal_length = (a) => BigInt([...a].length);

/** `String.utf8ByteSize`.
 *  @param {string} a `string`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_string_utf8_byte_size = (a) => BigInt($utf8(a).length);

/* ------------------------------------------------------------ nat_num */

/** `Int.natAbs`.
 *  @param {bigint} a `bigint_int`
 *  @returns {number} `uint53` */
export const bigint_int__uint53__lean_nat_abs = (a) => $toNum53(a < 0n ? -a : a);

/** `Int.natAbs`.
 *  @param {number} a `int53`
 *  @returns {bigint} `bigint_nat` */
export const int53__bigint_nat__lean_nat_abs = (a) => BigInt(Math.abs(a));

/** `Int.natAbs` (the absolute value of a safe integer is one).
 *  @param {number} a `int53`
 *  @returns {number} `uint53` */
export const int53__uint53__lean_nat_abs = (a) => Math.abs(a);

/** `UInt64.toNat`.
 *  @param {bigint} a `bigint_nat`
 *  @returns {number} `uint53` */
export const bigint_nat__uint53__lean_uint64_to_nat__UInt64_toNat = (a) => $toNum53(a);

/** `Nat.add`.
 *  @param {number} a `uint53`
 *  @param {number} b `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_nat_add = (a, b) => $chk53(a + b);

/** `Nat.div`.
 *  @param {number} a `uint53`
 *  @param {number} b `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_nat_div = (a, b) => b === 0 ? 0 : Math.floor(a / b);

/** `Nat.divExact`.
 *  @param {number} a `uint53`
 *  @param {number} b `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_nat_div_exact = (a, b) => b === 0 ? 0 : Math.floor(a / b);

/** `Nat.land`.
 *  @param {number} a `uint53`
 *  @param {number} b `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_nat_land = (a, b) => $land53(a, b);

/** `Nat.log2`.
 *  @param {number} a `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_nat_log2 = (a) => a === 0 ? 0 : a.toString(2).length - 1;

/** `Nat.lor`.
 *  @param {number} a `uint53`
 *  @param {number} b `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_nat_lor = (a, b) => $lor53(a, b);

/** `Nat.xor`.
 *  @param {number} a `uint53`
 *  @param {number} b `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_nat_lxor = (a, b) => $xor53(a, b);

/** `Nat.modCore`, `Nat.mod`.
 *  @param {number} a `uint53`
 *  @param {number} b `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_nat_mod__Nat_mod = (a, b) => b === 0 ? a : a % b;

/** `Nat.mul`.
 *  @param {number} a `uint53`
 *  @param {number} b `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_nat_mul = (a, b) => $chk53(a * b);

/** `Nat.pow`.
 *  @param {number} a `uint53`
 *  @param {number} b `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_nat_pow = (a, b) => $pow53(a, b);

/** `Nat.pred`.
 *  @param {number} a `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_nat_pred = (a) => a > 0 ? a - 1 : 0;

/** `Nat.shiftLeft`.
 *  @param {number} a `uint53`
 *  @param {number} b `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_nat_shiftl = (a, b) => $chk53(a * Math.pow(2, b));

/** `Nat.shiftRight`.
 *  @param {number} a `uint53`
 *  @param {number} b `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_nat_shiftr = (a, b) => Math.floor(a / Math.pow(2, b));

/** `Nat.sub`.
 *  @param {number} a `uint53`
 *  @param {number} b `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_nat_sub = (a, b) => a > b ? a - b : 0;

/** `String.Internal.length`, `String.length`.
 *  @param {string} a `string`
 *  @returns {number} `uint53` */
export const uint53__lean_string_length__String_Internal_length = (a) => [...a].length;

/** `String.utf8ByteSize`.
 *  @param {string} a `string`
 *  @returns {number} `uint53` */
export const uint53__lean_string_utf8_byte_size = (a) => $utf8(a).length;

/* ------------------------------------------------------------ int_bigint */

/** `Int.tdiv`.
 *  @param {bigint} a `bigint_int`
 *  @param {bigint} b `bigint_int`
 *  @returns {bigint} `bigint_int` */
export const bigint_int__lean_int_div = (a, b) => b === 0n ? 0n : a / b;

/** `Int.divExact`.
 *  @param {bigint} a `bigint_int`
 *  @param {bigint} b `bigint_int`
 *  @returns {bigint} `bigint_int` */
export const bigint_int__lean_int_div_exact = (a, b) =>
  b === 0n
  ? 0n
  : a % b < 0n
    ? b > 0n
      ? a / b - 1n
      : a / b + 1n
    : a / b;

/** `Int.ediv`.
 *  @param {bigint} a `bigint_int`
 *  @param {bigint} b `bigint_int`
 *  @returns {bigint} `bigint_int` */
export const bigint_int__lean_int_ediv = (a, b) =>
  b === 0n
  ? 0n
  : a % b < 0n
    ? b > 0n
      ? a / b - 1n
      : a / b + 1n
    : a / b;

/** `Int.emod`.
 *  @param {bigint} a `bigint_int`
 *  @param {bigint} b `bigint_int`
 *  @returns {bigint} `bigint_int` */
export const bigint_int__lean_int_emod = (a, b) => b === 0n ? a : ((a % b) + (b < 0n ? -b : b)) % (b < 0n ? -b : b);

/** `Int.tmod`.
 *  @param {bigint} a `bigint_int`
 *  @param {bigint} b `bigint_int`
 *  @returns {bigint} `bigint_int` */
export const bigint_int__lean_int_mod = (a, b) => b === 0n ? a : a % b;

/** `Int.negSucc`.
 *  @param {bigint} a `bigint_nat`
 *  @returns {bigint} `bigint_int` */
export const bigint_nat__bigint_int__lean_int_neg_succ_of_nat = (a) => -a - 1n;

/** `Int.negSucc`.
 *  @param {number} a `uint53`
 *  @returns {bigint} `bigint_int` */
export const uint53__bigint_int__lean_int_neg_succ_of_nat = (a) => -BigInt(a) - 1n;

/* ------------------------------------------------------------ int_num */

/** `Int64.toInt`.
 *  @param {bigint} a `bigint_int`
 *  @returns {number} `int53` */
export const bigint_int__int53__lean_int64_to_int_sint = (a) => $toNum53(a);

/** `Int.negSucc`.
 *  @param {bigint} a `bigint_nat`
 *  @returns {number} `int53` */
export const bigint_nat__int53__lean_int_neg_succ_of_nat = (a) => $toNum53(-a - 1n);

/** `Int.negSucc`.
 *  @param {number} a `uint53`
 *  @returns {number} `int53` */
export const uint53__int53__lean_int_neg_succ_of_nat = (a) => -a - 1;

/** `Int.ofNat`.
 *  @param {bigint} a `bigint_nat`
 *  @returns {number} `int53` */
export const bigint_nat__int53__lean_nat_to_int = (a) => $toNum53(a);

/** `Int.add`.
 *  @param {number} a `int53`
 *  @param {number} b `int53`
 *  @returns {number} `int53` */
export const int53__lean_int_add = (a, b) => $chk53(a + b);

/** `Int.tdiv`.
 *  @param {number} a `int53`
 *  @param {number} b `int53`
 *  @returns {number} `int53` */
export const int53__lean_int_div = (a, b) => b === 0 ? 0 : Math.trunc(a / b);

/** `Int.divExact`.
 *  @param {number} a `int53`
 *  @param {number} b `int53`
 *  @returns {number} `int53` */
export const int53__lean_int_div_exact = (a, b) =>
  b === 0
  ? 0
  : a % b < 0
    ? b > 0
      ? Math.trunc(a / b) - 1
      : Math.trunc(a / b) + 1
    : Math.trunc(a / b);

/** `Int.ediv`.
 *  @param {number} a `int53`
 *  @param {number} b `int53`
 *  @returns {number} `int53` */
export const int53__lean_int_ediv = (a, b) =>
  b === 0
  ? 0
  : a % b < 0
    ? b > 0
      ? Math.trunc(a / b) - 1
      : Math.trunc(a / b) + 1
    : Math.trunc(a / b);

/** `Int.emod`.
 *  @param {number} a `int53`
 *  @param {number} b `int53`
 *  @returns {number} `int53` */
export const int53__lean_int_emod = (a, b) => b === 0 ? a : ((a % b) + Math.abs(b)) % Math.abs(b);

/** `Int.tmod`.
 *  @param {number} a `int53`
 *  @param {number} b `int53`
 *  @returns {number} `int53` */
export const int53__lean_int_mod = (a, b) => b === 0 ? a : a % b;

/** `Int.mul`.
 *  @param {number} a `int53`
 *  @param {number} b `int53`
 *  @returns {number} `int53` */
export const int53__lean_int_mul = (a, b) => $chk53(a * b);

/** `Int.pow`.
 *  @param {number} a `int53`
 *  @param {number} b `uint53`
 *  @returns {number} `int53` */
export const int53__uint53__lean_int_pow = (a, b) => $pow53(a, b);

/** `Int.pow`, of a `BigInt` exponent (only `-1`, `0` and `1` have a safe power of an exponent
 *  of more than 53 bits).
 *  @param {number} a `int53`
 *  @param {bigint} b `bigint_nat`
 *  @returns {number} `int53` */
export const int53__bigint_nat__lean_int_pow = (a, b) =>
  a === 0 || a === 1 || a === -1 || b <= 64n
    ? $pow53(a, Number(b > 64n ? (b % 2n) + 2n : b))
    : $overflow();

/** `Int.neg`.
 *  @param {number} a `int53`
 *  @returns {number} `int53` */
export const int53__lean_int_neg = (a) => 0 - a;

/** `Int.sub`.
 *  @param {number} a `int53`
 *  @param {number} b `int53`
 *  @returns {number} `int53` */
export const int53__lean_int_sub = (a, b) => $chk53(a - b);

/* ------------------------------------------------------------ uint64_bigint */

/** `Bool.toUInt64`.
 *  @param {boolean} a `bool`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_bool_to_uint64 = (a) => a ? 1n : 0n;

/** `String.hash`: Lean's hash of the UTF-8 bytes (MurmurHash64A, seed 11).
 *  @param {string} s `string`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_string_hash = (s) => $hashBytes(encoder.encode(s));

/** `UInt64.add`.
 *  @param {bigint} a `bigint_nat`
 *  @param {bigint} b `bigint_nat`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_uint64_add = (a, b) => BigInt.asUintN(64, a + b);

/** `UInt64.complement`.
 *  @param {bigint} a `bigint_nat`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_uint64_complement = (a) => BigInt.asUintN(64, ~a);

/** `UInt64.div`.
 *  @param {bigint} a `bigint_nat`
 *  @param {bigint} b `bigint_nat`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_uint64_div = (a, b) => b === 0n ? 0n : BigInt.asUintN(64, a / b);

/** `UInt64.land`.
 *  @param {bigint} a `bigint_nat`
 *  @param {bigint} b `bigint_nat`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_uint64_land = (a, b) => BigInt.asUintN(64, a & b);

/** `UInt64.log2`.
 *  @param {bigint} a `bigint_nat`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_uint64_log2 = (a) => a === 0n ? 0n : BigInt(a.toString(2).length - 1);

/** `UInt64.lor`.
 *  @param {bigint} a `bigint_nat`
 *  @param {bigint} b `bigint_nat`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_uint64_lor = (a, b) => BigInt.asUintN(64, a | b);

/** `UInt64.mod`.
 *  @param {bigint} a `bigint_nat`
 *  @param {bigint} b `bigint_nat`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_uint64_mod = (a, b) => b === 0n ? a : a % b;

/** `UInt64.mul`.
 *  @param {bigint} a `bigint_nat`
 *  @param {bigint} b `bigint_nat`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_uint64_mul = (a, b) => BigInt.asUintN(64, a * b);

/** `UInt64.neg`.
 *  @param {bigint} a `bigint_nat`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_uint64_neg = (a) => BigInt.asUintN(64, -a);

/** `UInt64.ofNat`, `UInt64.ofNatLT`.
 *  @param {bigint} a `bigint_nat`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_uint64_of_nat__UInt64_ofNat = (a) => BigInt.asUintN(64, a);

/** `UInt64.ofNat`, `UInt64.ofNatLT` (a safe integer is below `2^64`).
 *  @param {number} a `uint53`
 *  @returns {bigint} `bigint_nat` */
export const uint53__bigint_nat__lean_uint64_of_nat__UInt64_ofNat = (a) => BigInt(a);

/** `UInt64.shiftLeft`.
 *  @param {bigint} a `bigint_nat`
 *  @param {bigint} b `bigint_nat`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_uint64_shift_left = (a, b) => BigInt.asUintN(64, a << (((b % 64n) + 64n) % 64n));

/** `UInt64.shiftRight`.
 *  @param {bigint} a `bigint_nat`
 *  @param {bigint} b `bigint_nat`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_uint64_shift_right = (a, b) => a >> (((b % 64n) + 64n) % 64n);

/** `UInt64.sub`.
 *  @param {bigint} a `bigint_nat`
 *  @param {bigint} b `bigint_nat`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_uint64_sub = (a, b) => BigInt.asUintN(64, a - b);

/** `UInt64.xor`.
 *  @param {bigint} a `bigint_nat`
 *  @param {bigint} b `bigint_nat`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_uint64_xor = (a, b) => BigInt.asUintN(64, a ^ b);

/* ------------------------------------------------------------ uint64_num */
// A `UInt64` below `2^53`: a result that is not throws.

/** `UInt64.ofBitVec`.
 *  @param {bigint} a `bigint_bitvec64`
 *  @returns {number} `uint53` */
export const bigint_bitvec64__uint53__lean_uint64_of_nat_mk = (a) => $toNum53(a);

/** `UInt64.ofNatLT`, `UInt64.ofNat`.
 *  @param {bigint} a `bigint_nat`
 *  @returns {number} `uint53` */
export const bigint_nat__uint53__lean_uint64_of_nat__UInt64_ofNat = (a) => $toNum53(BigInt.asUintN(64, a));

/** `UInt64.ofNat`, `UInt64.ofNatLT`: a safe integer is below `2^64`.
 *  @param {number} a `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_uint64_of_nat__UInt64_ofNat = (a) => a;

/** `Bool.toUInt64`.
 *  @param {boolean} a `bool`
 *  @returns {number} `uint53` */
export const uint53__lean_bool_to_uint64 = (a) => a ? 1 : 0;

/** `String.hash`: Lean's hash of the UTF-8 bytes (MurmurHash64A, seed 11).
 *  @param {string} s `string`
 *  @returns {number} `uint53` */
export const uint53__lean_string_hash = (s) => $toNum53($hashBytes(encoder.encode(s)));

/** `UInt64.add` (the sum of two safe integers is below `2^64`).
 *  @param {number} a `uint53`
 *  @param {number} b `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_uint64_add = (a, b) => $chk53(a + b);

/** `UInt64.complement` (it is at least `2^64 - 2^53`: it always throws).
 *  @param {number} a `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_uint64_complement = (a) => $toNum53(BigInt.asUintN(64, ~BigInt(a)));

/** `UInt64.div`.
 *  @param {number} a `uint53`
 *  @param {number} b `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_uint64_div = (a, b) => b === 0 ? 0 : Math.floor(a / b);

/** `UInt64.land`.
 *  @param {number} a `uint53`
 *  @param {number} b `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_uint64_land = (a, b) => $land53(a, b);

/** `UInt64.log2`.
 *  @param {number} a `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_uint64_log2 = (a) => $log2_53(a);

/** `UInt64.lor`.
 *  @param {number} a `uint53`
 *  @param {number} b `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_uint64_lor = (a, b) => $lor53(a, b);

/** `UInt64.mod`.
 *  @param {number} a `uint53`
 *  @param {number} b `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_uint64_mod = (a, b) => b === 0 ? a : a % b;

/** `UInt64.mul` (modulo `2^64`, which may bring it back below `2^53`).
 *  @param {number} a `uint53`
 *  @param {number} b `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_uint64_mul = (a, b) => $toNum53(BigInt.asUintN(64, BigInt(a) * BigInt(b)));

/** `UInt64.neg` (only `0` has a negation below `2^53`).
 *  @param {number} a `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_uint64_neg = (a) => (a === 0 ? 0 : $toNum53(18446744073709551616n - BigInt(a)));

/** `UInt64.shiftLeft` (modulo `2^64`).
 *  @param {number} a `uint53`
 *  @param {number} b `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_uint64_shift_left = (a, b) => $toNum53(BigInt.asUintN(64, BigInt(a) << BigInt(b % 64)));

/** `UInt64.shiftRight`.
 *  @param {number} a `uint53`
 *  @param {number} b `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_uint64_shift_right = (a, b) => Math.floor(a / 2 ** (b % 64));

/** `UInt64.sub` (a negative difference wraps to `2^64 - 2^53` or more).
 *  @param {number} a `uint53`
 *  @param {number} b `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_uint64_sub = (a, b) => (a >= b ? a - b : $toNum53(BigInt.asUintN(64, BigInt(a - b))));

/** `UInt64.xor`.
 *  @param {number} a `uint53`
 *  @param {number} b `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_uint64_xor = (a, b) => $xor53(a, b);

/* ------------------------------------------------------------ int64_bigint */

/** `Bool.toInt64`.
 *  @param {boolean} a `bool`
 *  @returns {bigint} `bigint_int` */
export const bigint_int__lean_bool_to_int64 = (a) => a ? 1n : 0n;

/** `Int64.abs`.
 *  @param {bigint} a `bigint_int`
 *  @returns {bigint} `bigint_int` */
export const bigint_int__lean_int64_abs = (a) => BigInt.asIntN(64, a < 0n ? -a : a);

/** `Int64.add`.
 *  @param {bigint} a `bigint_int`
 *  @param {bigint} b `bigint_int`
 *  @returns {bigint} `bigint_int` */
export const bigint_int__lean_int64_add = (a, b) => BigInt.asIntN(64, a + b);

/** `Int64.complement`.
 *  @param {bigint} a `bigint_int`
 *  @returns {bigint} `bigint_int` */
export const bigint_int__lean_int64_complement = (a) => BigInt.asIntN(64, ~a);

/** `Int64.div`.
 *  @param {bigint} a `bigint_int`
 *  @param {bigint} b `bigint_int`
 *  @returns {bigint} `bigint_int` */
export const bigint_int__lean_int64_div = (a, b) => b === 0n ? 0n : BigInt.asIntN(64, a / b);

/** `Int64.land`.
 *  @param {bigint} a `bigint_int`
 *  @param {bigint} b `bigint_int`
 *  @returns {bigint} `bigint_int` */
export const bigint_int__lean_int64_land = (a, b) => BigInt.asIntN(64, a & b);

/** `Int64.lor`.
 *  @param {bigint} a `bigint_int`
 *  @param {bigint} b `bigint_int`
 *  @returns {bigint} `bigint_int` */
export const bigint_int__lean_int64_lor = (a, b) => BigInt.asIntN(64, a | b);

/** `Int64.mod`.
 *  @param {bigint} a `bigint_int`
 *  @param {bigint} b `bigint_int`
 *  @returns {bigint} `bigint_int` */
export const bigint_int__lean_int64_mod = (a, b) => b === 0n ? a : a % b;

/** `Int64.mul`.
 *  @param {bigint} a `bigint_int`
 *  @param {bigint} b `bigint_int`
 *  @returns {bigint} `bigint_int` */
export const bigint_int__lean_int64_mul = (a, b) => BigInt.asIntN(64, a * b);

/** `Int64.neg`.
 *  @param {bigint} a `bigint_int`
 *  @returns {bigint} `bigint_int` */
export const bigint_int__lean_int64_neg = (a) => BigInt.asIntN(64, -a);

/** `Int64.ofInt`.
 *  @param {bigint} a `bigint_int`
 *  @returns {bigint} `bigint_int` */
export const bigint_int__lean_int64_of_int = (a) => BigInt.asIntN(64, a);

/** `Int64.ofInt` (a safe integer is an `Int64`).
 *  @param {number} a `int53`
 *  @returns {bigint} `bigint_int` */
export const int53__bigint_int__lean_int64_of_int = (a) => BigInt(a);

/** `Int64.shiftLeft`.
 *  @param {bigint} a `bigint_int`
 *  @param {bigint} b `bigint_int`
 *  @returns {bigint} `bigint_int` */
export const bigint_int__lean_int64_shift_left = (a, b) => BigInt.asIntN(64, a << (((b % 64n) + 64n) % 64n));

/** `Int64.shiftRight`.
 *  @param {bigint} a `bigint_int`
 *  @param {bigint} b `bigint_int`
 *  @returns {bigint} `bigint_int` */
export const bigint_int__lean_int64_shift_right = (a, b) => a >> (((b % 64n) + 64n) % 64n);

/** `Int64.sub`.
 *  @param {bigint} a `bigint_int`
 *  @param {bigint} b `bigint_int`
 *  @returns {bigint} `bigint_int` */
export const bigint_int__lean_int64_sub = (a, b) => BigInt.asIntN(64, a - b);

/** `Int64.xor`.
 *  @param {bigint} a `bigint_int`
 *  @param {bigint} b `bigint_int`
 *  @returns {bigint} `bigint_int` */
export const bigint_int__lean_int64_xor = (a, b) => BigInt.asIntN(64, a ^ b);

/** `Int64.ofNat`.
 *  @param {bigint} a `bigint_nat`
 *  @returns {bigint} `bigint_int` */
export const bigint_nat__bigint_int__lean_int64_of_nat = bigint_int__lean_int64_of_int;

/** `Int64.ofNat`.
 *  @param {number} a `uint53`
 *  @returns {bigint} `bigint_int` */
export const uint53__bigint_int__lean_int64_of_nat = int53__bigint_int__lean_int64_of_int;

/* ------------------------------------------------------------ int64_num */
// An `Int64` of absolute value below `2^53`: a result that is not throws.

/** `Int64.ofInt`.
 *  @param {bigint} a `bigint_int`
 *  @returns {number} `int53` */
export const bigint_int__int53__lean_int64_of_int = (a) => $toNum53(BigInt.asIntN(64, a));

/** `Int64.ofNat`.
 *  @param {bigint} a `bigint_nat`
 *  @returns {number} `int53` */
export const bigint_nat__int53__lean_int64_of_nat = bigint_int__int53__lean_int64_of_int;

/** `Int64.ofInt` (a safe integer is an `Int64`).
 *  @param {number} a `int53`
 *  @returns {number} `int53` */
export const int53__lean_int64_of_int = (a) => a;

/** `Int64.ofNat`.
 *  @param {number} a `uint53`
 *  @returns {number} `int53` */
export const uint53__int53__lean_int64_of_nat = int53__lean_int64_of_int;

/** `Bool.toInt64`.
 *  @param {boolean} a `bool`
 *  @returns {number} `int53` */
export const int53__lean_bool_to_int64 = (a) => a ? 1 : 0;

/** `Int64.abs`.
 *  @param {number} a `int53`
 *  @returns {number} `int53` */
export const int53__lean_int64_abs = (a) => Math.abs(a);

/** `Int64.add` (the sum of two safe integers is an `Int64`).
 *  @param {number} a `int53`
 *  @param {number} b `int53`
 *  @returns {number} `int53` */
export const int53__lean_int64_add = (a, b) => $chk53(a + b);

/** `Int64.complement`.
 *  @param {number} a `int53`
 *  @returns {number} `int53` */
export const int53__lean_int64_complement = (a) => $chk53(-a - 1);

/** `Int64.div` (truncated).
 *  @param {number} a `int53`
 *  @param {number} b `int53`
 *  @returns {number} `int53` */
export const int53__lean_int64_div = (a, b) => b === 0 ? 0 : Math.trunc(a / b);

/** `Int64.land`.
 *  @param {number} a `int53`
 *  @param {number} b `int53`
 *  @returns {number} `int53` */
export const int53__lean_int64_land = (a, b) => $toNum53(BigInt(a) & BigInt(b));

/** `Int64.lor`.
 *  @param {number} a `int53`
 *  @param {number} b `int53`
 *  @returns {number} `int53` */
export const int53__lean_int64_lor = (a, b) => $toNum53(BigInt(a) | BigInt(b));

/** `Int64.mod` (the sign of `a`).
 *  @param {number} a `int53`
 *  @param {number} b `int53`
 *  @returns {number} `int53` */
export const int53__lean_int64_mod = (a, b) => b === 0 ? a : a % b;

/** `Int64.mul` (modulo `2^64`, which may bring it back to a safe integer).
 *  @param {number} a `int53`
 *  @param {number} b `int53`
 *  @returns {number} `int53` */
export const int53__lean_int64_mul = (a, b) => $toNum53(BigInt.asIntN(64, BigInt(a) * BigInt(b)));

/** `Int64.neg`.
 *  @param {number} a `int53`
 *  @returns {number} `int53` */
export const int53__lean_int64_neg = (a) => 0 - a;

/** `Int64.shiftLeft` (modulo `2^64`).
 *  @param {number} a `int53`
 *  @param {number} b `int53`
 *  @returns {number} `int53` */
export const int53__lean_int64_shift_left = (a, b) =>
  $toNum53(BigInt.asIntN(64, BigInt(a) << BigInt(((b % 64) + 64) % 64)));

/** `Int64.shiftRight` (arithmetic).
 *  @param {number} a `int53`
 *  @param {number} b `int53`
 *  @returns {number} `int53` */
export const int53__lean_int64_shift_right = (a, b) => Math.floor(a / 2 ** (((b % 64) + 64) % 64));

/** `Int64.sub`.
 *  @param {number} a `int53`
 *  @param {number} b `int53`
 *  @returns {number} `int53` */
export const int53__lean_int64_sub = (a, b) => $chk53(a - b);

/** `Int64.xor`.
 *  @param {number} a `int53`
 *  @param {number} b `int53`
 *  @returns {number} `int53` */
export const int53__lean_int64_xor = (a, b) => $toNum53(BigInt(a) ^ BigInt(b));

/* ------------------------------------------------------------ bitvec_bigint */

/* ------------------------------------------------------------ bitvec_num */

/** `UInt64.toBitVec`.
 *  @param {bigint} a `bigint_nat`
 *  @returns {number} `int53_bitvec64` */
export const bigint_nat__int53_bitvec64__lean_uint64_to_nat__UInt64_toBitVec = (a) => $toNum53(a);


/* ------------------------------------------------------------ floats */

/** `Float.round`.
 *  @param {number} a `float`
 *  @returns {number} `float` */
export const float__round = (a) => $round(a);

/** `Float32.round`.
 *  @param {number} a `float32`
 *  @returns {number} `float32` */
export const float32__roundf = (a) => $round(a);

/** `Float.toString`.
 *  @param {number} a `float`
 *  @returns {string} `string` */
export const float__lean_float_to_string = (a) => $fmtF6(a);

/** `Float32.toString`.
 *  @param {number} a `float32`
 *  @returns {string} `string` */
export const float32__lean_float32_to_string = (a) => $fmtF6(a);

/** `Float.toUInt8` (saturating; `NaN` is `0`).
 *  @param {number} a `float`
 *  @returns {number} `uint8` */
export const float__lean_float_to_uint8 = (a) => $satNum(a, 0, 255);

/** `Float.toUInt16` (saturating; `NaN` is `0`).
 *  @param {number} a `float`
 *  @returns {number} `uint16` */
export const float__lean_float_to_uint16 = (a) => $satNum(a, 0, 65535);

/** `Float.toUInt32` (saturating; `NaN` is `0`).
 *  @param {number} a `float`
 *  @returns {number} `uint32` */
export const float__lean_float_to_uint32 = (a) => $satNum(a, 0, 4294967295);

/** `Float.toUInt64` (saturating; `NaN` is `0`).
 *  @param {number} a `float`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_float_to_uint64 = (a) => $satBig(a, 0n, 18446744073709551615n);

/** `Float.toUInt64` (saturating; `NaN` is `0`), a result of `2^53` or more throws.
 *  @param {number} a `float`
 *  @returns {number} `uint53` */
export const uint53__lean_float_to_uint64 = (a) => $toNum53($satBig(a, 0n, 18446744073709551615n));

/** `Float.toInt8` (saturating; `NaN` is `0`).
 *  @param {number} a `float`
 *  @returns {number} `int8` */
export const float__lean_float_to_int8 = (a) => $satNum(a, -128, 127);

/** `Float.toInt16` (saturating; `NaN` is `0`).
 *  @param {number} a `float`
 *  @returns {number} `int16` */
export const float__lean_float_to_int16 = (a) => $satNum(a, -32768, 32767);

/** `Float.toInt32` (saturating; `NaN` is `0`).
 *  @param {number} a `float`
 *  @returns {number} `int32` */
export const float__lean_float_to_int32 = (a) => $satNum(a, -2147483648, 2147483647);

/** `Float.toInt64` (saturating; `NaN` is `0`).
 *  @param {number} a `float`
 *  @returns {bigint} `bigint_int` */
export const bigint_int__lean_float_to_int64 = (a) =>
  $satBig(a, -9223372036854775808n, 9223372036854775807n);

/** `Float.toInt64` (saturating; `NaN` is `0`), a result of absolute value `2^53` or more throws.
 *  @param {number} a `float`
 *  @returns {number} `int53` */
export const int53__lean_float_to_int64 = (a) =>
  $toNum53($satBig(a, -9223372036854775808n, 9223372036854775807n));

/** `Float32.toUInt8` (saturating; `NaN` is `0`).
 *  @param {number} a `float32`
 *  @returns {number} `uint8` */
export const float32__lean_float32_to_uint8 = (a) => $satNum(a, 0, 255);

/** `Float32.toUInt16` (saturating; `NaN` is `0`).
 *  @param {number} a `float32`
 *  @returns {number} `uint16` */
export const float32__lean_float32_to_uint16 = (a) => $satNum(a, 0, 65535);

/** `Float32.toUInt32` (saturating; `NaN` is `0`).
 *  @param {number} a `float32`
 *  @returns {number} `uint32` */
export const float32__lean_float32_to_uint32 = (a) => $satNum(a, 0, 4294967295);

/** `Float32.toUInt64` (saturating; `NaN` is `0`).
 *  @param {number} a `float32`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_float32_to_uint64 = (a) => $satBig(a, 0n, 18446744073709551615n);

/** `Float32.toUInt64` (saturating; `NaN` is `0`), a result of `2^53` or more throws.
 *  @param {number} a `float32`
 *  @returns {number} `uint53` */
export const uint53__lean_float32_to_uint64 = (a) => $toNum53($satBig(a, 0n, 18446744073709551615n));

/** `Float32.toInt8` (saturating; `NaN` is `0`).
 *  @param {number} a `float32`
 *  @returns {number} `int8` */
export const float32__lean_float32_to_int8 = (a) => $satNum(a, -128, 127);

/** `Float32.toInt16` (saturating; `NaN` is `0`).
 *  @param {number} a `float32`
 *  @returns {number} `int16` */
export const float32__lean_float32_to_int16 = (a) => $satNum(a, -32768, 32767);

/** `Float32.toInt32` (saturating; `NaN` is `0`).
 *  @param {number} a `float32`
 *  @returns {number} `int32` */
export const float32__lean_float32_to_int32 = (a) => $satNum(a, -2147483648, 2147483647);

/** `Float32.toInt64` (saturating; `NaN` is `0`).
 *  @param {number} a `float32`
 *  @returns {bigint} `bigint_int` */
export const bigint_int__lean_float32_to_int64 = (a) =>
  $satBig(a, -9223372036854775808n, 9223372036854775807n);

/** `Float32.toInt64` (saturating; `NaN` is `0`), a result of absolute value `2^53` or more throws.
 *  @param {number} a `float32`
 *  @returns {number} `int53` */
export const int53__lean_float32_to_int64 = (a) =>
  $toNum53($satBig(a, -9223372036854775808n, 9223372036854775807n));

/** `Float.toBits`.
 *  @param {number} a `float`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_float_to_bits__Float_toBits = (a) => $toBits(a);

/** `Float.toBits`; bits of `2^53` or more (every double of absolute value at least `2^-1021`,
 *  and every negative one) throw.
 *  @param {number} a `float`
 *  @returns {number} `uint53` */
export const uint53__lean_float_to_bits__Float_toBits = (a) => $toNum53($toBits(a));

/** `Float.ofBits`.
 *  @param {bigint} a `bigint_nat`
 *  @returns {number} `float` */
export const bigint_nat__lean_float_of_bits__Float_ofBits = (a) => $ofBits(a);

/** `Float.ofBits`.
 *  @param {number} a `uint53`
 *  @returns {number} `float` */
export const uint53__lean_float_of_bits__Float_ofBits = (a) => $ofBits(BigInt(a));

/** `Float32.toBits`.
 *  @param {number} a `float32`
 *  @returns {number} `uint32` */
export const float32__lean_float32_to_bits__Float32_toBits = (a) => {
  const dv = new DataView(new ArrayBuffer(4));
  dv.setFloat32(0, a);
  return dv.getUint32(0);
};

/** `Float32.ofBits`.
 *  @param {number} a `uint32`
 *  @returns {number} `float32` */
export const uint32__lean_float32_of_bits__Float32_ofBits = (a) => {
  const dv = new DataView(new ArrayBuffer(4));
  dv.setUint32(0, a);
  return dv.getFloat32(0);
};

/** `Float.frExp`.
 *  @param {number} a `float`
 *  @returns {{_1: number, _2: bigint}} `obj (record 2) [float, bigint_int]` */
export const bigint_int__lean_float_frexp = (a) => {
  const [m, e] = $frexp(a);
  return { _1: m, _2: BigInt(e) };
};

/** `Float.frExp`.
 *  @param {number} a `float`
 *  @returns {{_1: number, _2: number}} `obj (record 2) [float, int53]` */
export const int53__lean_float_frexp = (a) => {
  const [m, e] = $frexp(a);
  return { _1: m, _2: e };
};

/** `Float32.frExp`.
 *  @param {number} a `float32`
 *  @returns {{_1: number, _2: bigint}} `obj (record 2) [float32, bigint_int]` */
export const bigint_int__lean_float32_frexp = (a) => {
  const [m, e] = $frexp(a);
  return { _1: m, _2: BigInt(e) };
};

/** `Float32.frExp`.
 *  @param {number} a `float32`
 *  @returns {{_1: number, _2: number}} `obj (record 2) [float32, int53]` */
export const int53__lean_float32_frexp = (a) => {
  const [m, e] = $frexp(a);
  return { _1: m, _2: e };
};

/** `Float.scaleB`.
 *  @param {number} a `float`
 *  @param {bigint} n `bigint_int`
 *  @returns {number} `float` */
export const bigint_int__lean_float_scaleb = (a, n) => $scalbn(a, $clampExp(n));

/** `Float.scaleB` (`$scalbn` clamps the exponent itself).
 *  @param {number} a `float`
 *  @param {number} n `int53`
 *  @returns {number} `float` */
export const int53__lean_float_scaleb = (a, n) => $scalbn(a, n);

/** `Float32.scaleB`.
 *  @param {number} a `float32`
 *  @param {bigint} n `bigint_int`
 *  @returns {number} `float32` */
export const bigint_int__lean_float32_scaleb = (a, n) => $scalbnf(a, $clampExp(n));

/** `Float32.scaleB` (`$scalbnf` clamps the exponent itself).
 *  @param {number} a `float32`
 *  @param {number} n `int53`
 *  @returns {number} `float32` */
export const int53__lean_float32_scaleb = (a, n) => $scalbnf(a, n);

/* ------------------------------------------------------------ strings */

/** `String.Internal.drop`: without its first `n` characters.
 *  @param {string} s `string`
 *  @param {number} n `uint53`
 *  @returns {string} `string` */
export const uint53__lean_string_drop = (s, n) => [...s].slice(n).join("");

/** `String.Internal.drop` (`Number` keeps a count too large for a string too large).
 *  @param {string} s `string`
 *  @param {bigint} n `bigint_nat`
 *  @returns {string} `string` */
export const bigint_nat__lean_string_drop = (s, n) => uint53__lean_string_drop(s, Number(n));

/** `String.Internal.dropRight`: without its last `n` characters.
 *  @param {string} s `string`
 *  @param {number} n `uint53`
 *  @returns {string} `string` */
export const uint53__lean_string_dropright = (s, n) => {
  const cs = [...s];
  return cs.slice(0, Math.max(cs.length - n, 0)).join("");
};

/** `String.Internal.dropRight`.
 *  @param {string} s `string`
 *  @param {bigint} n `bigint_nat`
 *  @returns {string} `string` */
export const bigint_nat__lean_string_dropright = (s, n) => uint53__lean_string_dropright(s, Number(n));

/** `String.Internal.trim`: without the whitespace (`Char.isWhitespace`) at both ends.
 *  @param {string} s `string`
 *  @returns {string} `string` */
export const string__lean_string_trim = (s) => {
  const cs = [...s];
  let b = 0;
  let e = cs.length;
  while (b < e && $isWs(cs[b])) b++;
  while (e > b && $isWs(cs[e - 1])) e--;
  return cs.slice(b, e).join("");
};

/** `String.Internal.foldl`.
 *  @param {function(string, string): string} f `fn [string, string] string`
 *  @param {string} init `string`
 *  @param {string} s `string`
 *  @returns {string} `string` */
export const string__lean_string_foldl = (f, init, s) => {
  let acc = init;
  for (const c of s) acc = f(acc, c);
  return acc;
};

/** `String.Internal.isPrefixOf`.
 *  @param {string} p `string`
 *  @param {string} s `string`
 *  @returns {boolean} `bool` */
export const string__lean_string_isprefixof = (p, s) => s.startsWith(p);

/** `String.Internal.contains`.
 *  @param {string} s `string`
 *  @param {string} c `string`
 *  @returns {boolean} `bool` */
export const string__lean_string_contains = (s, c) => s.includes(c);

/** `String.Internal.front`: the first character (`'A'` for the empty string).
 *  @param {string} s `string`
 *  @returns {string} `string` */
export const string__lean_string_front = (s) => (s.length === 0 ? "A" : String.fromCodePoint(s.codePointAt(0)));

/** `String.Internal.posOf`: the position of the first `c`, or the end position.
 *  @param {string} s `string`
 *  @param {string} c `string`
 *  @returns {number} `uint53` */
export const string__lean_string_posof = (s, c) => {
  const i = s.indexOf(c);
  return encoder.encode(i < 0 ? s : s.slice(0, i)).length;
};

/** `String.Internal.intercalate`.
 *  @param {string} sep `string`
 *  @param {Array<string>} xs `list string`
 *  @returns {string} `string` */
export const string__lean_string_intercalate = (sep, xs) => xs.join(sep);

/** `String.Internal.nextWhile`: from `i`, the position of the first character that fails `p`
 *  (or the end).
 *  @param {string} s `string`
 *  @param {function(string): boolean} p `fn [string] bool`
 *  @param {number} i `uint53`
 *  @returns {number} `uint53` */
export const string__lean_string_nextwhile = (s, p, i) => {
  const end = $utf8(s).length;
  while (i < end && p($get(s, i))) i = $next(s, i);
  return i;
};

/** `String.Internal.any`.
 *  @param {string} s `string`
 *  @param {function(string): boolean} p `fn [string] bool`
 *  @returns {boolean} `bool` */
export const string__lean_string_any = (s, p) => {
  for (const c of s) if (p(c)) return true;
  return false;
};

/** `String.Internal.capitalize`: the first character in upper case (ASCII only).
 *  @param {string} s `string`
 *  @returns {string} `string` */
export const string__lean_string_capitalize = (s) => {
  const c = s.charCodeAt(0);
  return c >= 97 && c <= 122 ? String.fromCharCode(c - 32) + s.slice(1) : s;
};

/** `String.Internal.offsetOfPos`: the number of characters that start before `p`.
 *  @param {string} s `string`
 *  @param {number} p `uint53`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_string_offsetofpos = (s, p) => BigInt(uint53__lean_string_offsetofpos(s, p));

/** `String.Internal.offsetOfPos`: the number of characters that start before `p`.
 *  @param {string} s `string`
 *  @param {number} p `uint53`
 *  @returns {number} `uint53` */
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

/** `String.Internal.getUTF8Byte`: byte `n` of the UTF-8 encoding.
 *  @param {string} s `string`
 *  @param {bigint} n `bigint_nat`
 *  @returns {number} `uint8` */
export const bigint_nat__lean_string_get_byte_fast__String_Internal_getUTF8Byte = (s, n) =>
  encoder.encode(s)[Number(n)];

/** `String.Internal.getUTF8Byte`: byte `n` of the UTF-8 encoding.
 *  @param {string} s `string`
 *  @param {number} n `uint53`
 *  @returns {number} `uint8` */
export const uint53__lean_string_get_byte_fast__String_Internal_getUTF8Byte = (s, n) => encoder.encode(s)[n];

/** `String.getUTF8Byte`: the byte at position `p`.
 *  @param {string} s `string`
 *  @param {number} p `uint53`
 *  @returns {number} `uint8` */
export const string__lean_string_get_byte_fast__String_getUTF8Byte = (s, p) => encoder.encode(s)[p];

/** `String.getUtf8Byte`.
 *  @param {string} s `string`
 *  @param {number} p `uint53`
 *  @returns {number} `uint8` */
export const string__lean_string_get_byte_fast__String_getUtf8Byte = string__lean_string_get_byte_fast__String_getUTF8Byte;

/** `String.Pos.Raw.get?`, `String.get?`: the character that starts at `p`, if one does.
 *  @param {string} s `string`
 *  @param {number} p `uint53`
 *  @returns {({tag: 0}|{tag: 1, _1: string})} `obj (union [0, 1] cells) [string]` */
export const string__lean_string_utf8_get_opt__String_Pos_Raw_get$3F = (s, p) => {
  const r = $utf8At(s, p);
  return r === undefined ? { tag: 0 } : { tag: 1, _1: r[0] };
};

/** `String.Pos.Raw.get!`, `String.get!`, `String.Pos.Raw.get'`, `String.get'`: the character at `p`
 *  (`'A'` if none starts there).
 *  @param {string} s `string`
 *  @param {number} p `uint53`
 *  @returns {string} `string` */
export const string__lean_string_utf8_get_bang__String_Pos_Raw_get$21 = (s, p) => $get(s, p);

/** `String.Pos.Raw.prev`, `String.prev`.
 *  @param {string} s `string`
 *  @param {number} p `uint53`
 *  @returns {number} `uint53` */
export const string__lean_string_utf8_prev__String_Pos_Raw_prev = (s, p) => $prev(s, p);

/** `String.get?`.
 *  @param {string} s `string`
 *  @param {number} p `uint53`
 *  @returns {({tag: 0}|{tag: 1, _1: string})} `obj (union [0, 1] cells) [string]` */
export const string__lean_string_utf8_get_opt__String_get$3F = string__lean_string_utf8_get_opt__String_Pos_Raw_get$3F;

/** `String.get!`.
 *  @param {string} s `string`
 *  @param {number} p `uint53`
 *  @returns {string} `string` */
export const string__lean_string_utf8_get_bang__String_get$21 = string__lean_string_utf8_get_bang__String_Pos_Raw_get$21;

/** `String.get'`.
 *  @param {string} s `string`
 *  @param {number} p `uint53`
 *  @returns {string} `string` */
export const string__lean_string_utf8_get_fast__String_get$27 = string__lean_string_utf8_get_bang__String_Pos_Raw_get$21;

/** `String.Pos.Raw.get'`.
 *  @param {string} s `string`
 *  @param {number} p `uint53`
 *  @returns {string} `string` */
export const string__lean_string_utf8_get_fast__String_Pos_Raw_get$27 = string__lean_string_utf8_get_bang__String_Pos_Raw_get$21;

/** `String.prev`.
 *  @param {string} s `string`
 *  @param {number} p `uint53`
 *  @returns {number} `uint53` */
export const string__lean_string_utf8_prev__String_prev = string__lean_string_utf8_prev__String_Pos_Raw_prev;

/** `dbgTraceIfShared msg a`: `a` (JavaScript does not tell whether a value is shared).
 *  @template α the delayed type
 *  @param {string} msg `string`
 *  @param {α} a `α`
 *  @returns {α} `α` */
export const string__lean_dbg_trace_if_shared = (msg, a) => a;

/** `String.next'`.
 *  @param {string} s `string`
 *  @param {number} p `uint53`
 *  @returns {number} `uint53` */
export const string__lean_string_utf8_next_fast__String_next$27 = (s, p) => $next(s, p);

/** `String.Pos.next` (on a position of the string `s` given first).
 *  @param {string} s `string`
 *  @param {number} p `uint53`
 *  @returns {number} `uint53` */
export const string__lean_string_utf8_next_fast__String_Pos_next = (s, p) => $next(s, p);

/** `String.extract` (on positions of the string `s` given first).
 *  @param {string} s `string`
 *  @param {number} b `uint53`
 *  @param {number} e `uint53`
 *  @returns {string} `string` */
export const string__lean_string_utf8_extract_fast = (s, b, e) => $utf8Extract(s, b, e);

/** `String.Pos.Raw.isValid`.
 *  @param {string} s `string`
 *  @param {number} p `uint53`
 *  @returns {boolean} `bool` */
export const string__lean_string_is_valid_pos = (s, p) => $isValid(s, p);

/** `String.Pos.Raw.Internal.min`.
 *  @param {number} a `uint53`
 *  @param {number} b `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_string_pos_min = (a, b) => Math.min(a, b);

/** `String.Pos.Raw.Internal.sub`.
 *  @param {number} a `uint53`
 *  @param {number} b `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_string_pos_sub = (a, b) => Math.max(a - b, 0);

/** `Substring.Raw.Internal.toString`.
 *  @param {[string, number, number]} ss `substring`
 *  @returns {string} `string` */
export const substring__lean_substring_tostring = (ss) => $utf8Extract(ss[0], ss[1], ss[2]);

/** `Substring.Raw.Internal.get`.
 *  @param {[string, number, number]} ss `substring`
 *  @param {number} p `uint53`
 *  @returns {string} `string` */
export const substring__lean_substring_get = (ss, p) => $get(ss[0], ss[1] + p);

/** `Substring.Raw.Internal.front`.
 *  @param {[string, number, number]} ss `substring`
 *  @returns {string} `string` */
export const substring__lean_substring_front = (ss) => $get(ss[0], ss[1]);

/** `Substring.Raw.Internal.isEmpty`.
 *  @param {[string, number, number]} ss `substring`
 *  @returns {boolean} `bool` */
export const substring__lean_substring_isempty = (ss) => ss[2] <= ss[1];

/** `Substring.Raw.Internal.prev`.
 *  @param {[string, number, number]} ss `substring`
 *  @param {number} p `uint53`
 *  @returns {number} `uint53` */
export const substring__lean_substring_prev = (ss, p) => {
  const absP = ss[1] + p;
  return absP === ss[1] ? p : Math.max($prev(ss[0], absP) - ss[1], 0);
};

/** `Substring.Raw.Internal.drop`: without its first `n` characters.
 *  @param {[string, number, number]} ss `substring`
 *  @param {number} n `uint53`
 *  @returns {[string, number, number]} `substring` */
export const uint53__lean_substring_drop = (ss, n) => {
  let k = n;
  let p = 0;
  while (k > 0) {
    const q = $subNext(ss, p);
    if (q === p) break;
    p = q;
    k--;
  }
  return [ss[0], ss[1] + p, ss[2]];
};

/** `Substring.Raw.Internal.drop`.
 *  @param {[string, number, number]} ss `substring`
 *  @param {bigint} n `bigint_nat`
 *  @returns {[string, number, number]} `substring` */
export const bigint_nat__lean_substring_drop = (ss, n) => uint53__lean_substring_drop(ss, Number(n));

/** `Substring.Raw.Internal.extract`.
 *  @param {[string, number, number]} ss `substring`
 *  @param {number} b `uint53`
 *  @param {number} e `uint53`
 *  @returns {[string, number, number]} `substring` */
export const substring__lean_substring_extract = (ss, b, e) =>
  b >= e ? ["", 0, 0] : [ss[0], Math.min(ss[2], ss[1] + b), Math.min(ss[2], ss[1] + e)];

/** `Substring.Raw.Internal.takeWhile`.
 *  @param {[string, number, number]} ss `substring`
 *  @param {function(string): boolean} p `fn [string] bool`
 *  @returns {[string, number, number]} `substring` */
export const substring__lean_substring_takewhile = (ss, p) => {
  let i = ss[1];
  while (i < ss[2] && p($get(ss[0], i))) i = $next(ss[0], i);
  return [ss[0], ss[1], i];
};

/** `Substring.Raw.Internal.all` (`true` for a substring whose bounds are not valid).
 *  @param {[string, number, number]} ss `substring`
 *  @param {function(string): boolean} p `fn [string] bool`
 *  @returns {boolean} `bool` */
export const substring__lean_substring_all = (ss, p) => {
  const [s, b, e] = ss;
  if (!($isValid(s, b) && $isValid(s, e) && b <= e)) return true;
  for (let i = b; i < e; i = $next(s, i)) if (!p($get(s, i))) return false;
  return true;
};

/** `Substring.Raw.Internal.beq`: the same bytes (after moving an invalid bound to the end).
 *  @param {[string, number, number]} x `substring`
 *  @param {[string, number, number]} y `substring`
 *  @returns {boolean} `bool` */
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

/** `String.Slice` `<`: the order of the strings of the slices.
 *  @param {[string, number, number]} a `stringSlice`
 *  @param {[string, number, number]} b `stringSlice`
 *  @returns {boolean} `bool` */
export const stringSlice__lean_slice_dec_lt = (a, b) =>
  $cmpStr($utf8Extract(a[0], a[1], a[2]), $utf8Extract(b[0], b[1], b[2])) < 0;

/** `String.Slice.hash`: the hash of the string of the slice.
 *  @param {[string, number, number]} a `stringSlice`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_slice_hash = (a) => $hashBytes($sliceBytes(a));

/** `String.Slice.hash`: the hash of the string of the slice (`2^53` or more throws).
 *  @param {[string, number, number]} a `stringSlice`
 *  @returns {number} `uint53` */
export const uint53__lean_slice_hash = (a) => $toNum53($hashBytes($sliceBytes(a)));

/* ------------------------------------------------------------ hashes */

/** `mixHash`.
 *  @param {bigint} h `bigint_nat`
 *  @param {bigint} k `bigint_nat`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_uint64_mix_hash = (h, k) => $mixHash(h, k);

/** `mixHash` (a result of `2^53` or more throws).
 *  @param {number} h `uint53`
 *  @param {number} k `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_uint64_mix_hash = (h, k) => $toNum53($mixHash(BigInt(h), BigInt(k)));

/* ------------------------------------------------------------ version and platform */
// The values of the Lean toolchain the snapshots are checked against (4.34.0 on
// x86_64-unknown-linux-gnu); `Tests/Main.lean` checks them against the Lean that runs it.

/** `Lean.version.getMajor`.
 *  @returns {function(): bigint} `fn [] bigint_nat` */
export const bigint_nat__lean_version_get_major = () => () => 4n;

/** `Lean.version.getMajor`.
 *  @returns {function(): number} `fn [] uint53` */
export const uint53__lean_version_get_major = () => () => 4;

/** `Lean.version.getMinor`.
 *  @returns {function(): bigint} `fn [] bigint_nat` */
export const bigint_nat__lean_version_get_minor = () => () => 34n;

/** `Lean.version.getMinor`.
 *  @returns {function(): number} `fn [] uint53` */
export const uint53__lean_version_get_minor = () => () => 34;

/** `Lean.version.getPatch`.
 *  @returns {function(): bigint} `fn [] bigint_nat` */
export const bigint_nat__lean_version_get_patch = () => () => 0n;

/** `Lean.version.getPatch`.
 *  @returns {function(): number} `fn [] uint53` */
export const uint53__lean_version_get_patch = () => () => 0;

/** `Lean.version.getIsRelease`.
 *  @returns {function(): boolean} `fn [] bool` */
export const bool__lean_version_get_is_release = () => () => true;

/** `Lean.version.getSpecialDesc`.
 *  @returns {function(): string} `fn [] string` */
export const string__lean_version_get_special_desc = () => () => "";

/** `Lean.getGithash`.
 *  @returns {function(): string} `fn [] string` */
export const string__lean_get_githash = () => () => "293d5d0c0c3f3dded4688b3ccd6a33939ac5102b";

/** `System.Platform.getTarget`.
 *  @returns {function(): string} `fn [] string` */
export const string__lean_system_platform_target = () => () => "x86_64-unknown-linux-gnu";

/** `System.Platform.getIsEmscripten`.
 *  @returns {function(): boolean} `fn [] bool` */
export const bool__lean_system_platform_emscripten = () => () => false;

/** `Lean.Internal.isStage0`.
 *  @returns {function(): boolean} `fn [] bool` */
export const bool__lean_internal_is_stage0 = () => () => false;

/** `Lean.Internal.hasLLVMBackend`.
 *  @returns {function(): boolean} `fn [] bool` */
export const bool__lean_internal_has_llvm_backend = () => () => false;

/* ------------------------------------------------------------ operations that share a function */

/** `Array.get!InternalBorrowed`: the same as `Array.get!Internal`.
 *  @template A, E the array layout `l : JsArrayLayout A E`: `A` is `array E`, or `typedArray t` with `E` = `terminal t.leaf`
 *  @param {E} d `E`
 *  @param {Array<E>|TypedArray} a `A`
 *  @param {bigint} i `bigint_nat`
 *  @returns {E} `E` */
export const bigint_nat__lean_array_get_borrowed = bigint_nat__lean_array_get;
/**
 *  @param {bigint} a `bigint_nat`
 *  @returns {number} `uint16` */
export const bigint_nat__lean_uint16_of_nat__UInt16_ofNatLT = bigint_nat__lean_uint16_of_nat__UInt16_ofNat;
/**
 *  @param {bigint} a `bigint_nat`
 *  @returns {number} `uint32` */
export const bigint_nat__lean_uint32_of_nat__UInt32_ofNatLT = bigint_nat__lean_uint32_of_nat__UInt32_ofNat;
/**
 *  @param {bigint} a `bigint_nat`
 *  @returns {number} `uint8` */
export const bigint_nat__lean_uint8_of_nat__UInt8_ofNatLT = bigint_nat__lean_uint8_of_nat__UInt8_ofNat;
/**
 *  @param {string} a `string`
 *  @returns {Array<string>} `list string` */
export const string__lean_string_data__String_toList = string__lean_string_data__String_data;
/**
 *  @param {Array<string>} a `list string`
 *  @returns {string} `string` */
export const string__lean_string_mk__String_ofList = string__lean_string_mk__String_mk;
/**
 *  @param {string} a `string`
 *  @param {number} b `uint53`
 *  @returns {boolean} `bool` */
export const string__lean_string_utf8_at_end__String_Pos_Raw_atEnd = string__lean_string_utf8_at_end__String_Internal_atEnd;
/**
 *  @param {string} a `string`
 *  @param {number} b `uint53`
 *  @returns {boolean} `bool` */
export const string__lean_string_utf8_at_end__String_atEnd = string__lean_string_utf8_at_end__String_Internal_atEnd;
/**
 *  @param {string} a `string`
 *  @param {number} b `uint53`
 *  @param {number} c `uint53`
 *  @returns {string} `string` */
export const string__lean_string_utf8_extract__String_Pos_Raw_extract = string__lean_string_utf8_extract__String_Internal_extract;
/**
 *  @param {string} a `string`
 *  @param {number} b `uint53`
 *  @returns {string} `string` */
export const string__lean_string_utf8_get__String_Pos_Raw_get = string__lean_string_utf8_get__String_Internal_get;
/**
 *  @param {string} a `string`
 *  @param {number} b `uint53`
 *  @returns {string} `string` */
export const string__lean_string_utf8_get__String_get = string__lean_string_utf8_get__String_Internal_get;
/**
 *  @param {string} a `string`
 *  @param {number} b `uint53`
 *  @returns {number} `uint53` */
export const string__lean_string_utf8_next__String_Pos_Raw_next = string__lean_string_utf8_next__String_Internal_next;
/**
 *  @param {string} a `string`
 *  @param {number} b `uint53`
 *  @returns {number} `uint53` */
export const string__lean_string_utf8_next__String_next = string__lean_string_utf8_next__String_Internal_next;
/**
 *  @param {string} a `string`
 *  @param {number} b `uint53`
 *  @param {string} c `string`
 *  @returns {string} `string` */
export const string__lean_string_utf8_set__String_set = string__lean_string_utf8_set__String_Pos_Raw_set;
/** `Array.get!InternalBorrowed`: the same as `Array.get!Internal`.
 *  @template A, E the array layout `l : JsArrayLayout A E`: `A` is `array E`, or `typedArray t` with `E` = `terminal t.leaf`
 *  @param {E} d `E`
 *  @param {Array<E>|TypedArray} a `A`
 *  @param {number} i `uint53`
 *  @returns {E} `E` */
export const uint53__lean_array_get_borrowed = uint53__lean_array_get;
/**
 *  @param {number} a `uint53`
 *  @returns {number} `uint16` */
export const uint53__lean_uint16_of_nat__UInt16_ofNatLT = uint53__lean_uint16_of_nat__UInt16_ofNat;
/**
 *  @param {number} a `uint53`
 *  @returns {number} `uint32` */
export const uint53__lean_uint32_of_nat__UInt32_ofNatLT = uint53__lean_uint32_of_nat__UInt32_ofNat;
/**
 *  @param {number} a `uint53`
 *  @returns {number} `uint8` */
export const uint53__lean_uint8_of_nat__UInt8_ofNatLT = uint53__lean_uint8_of_nat__UInt8_ofNat;
/**
 *  @param {bigint} a `bigint_nat`
 *  @param {bigint} b `bigint_nat`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_nat_mod__Nat_modCore = bigint_nat__lean_nat_mod__Nat_mod;
/**
 *  @param {string} a `string`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_string_length__String_length = bigint_nat__lean_string_length__String_Internal_length;
/**
 *  @param {number} a `uint53`
 *  @param {number} b `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_nat_mod__Nat_modCore = uint53__lean_nat_mod__Nat_mod;
/**
 *  @param {string} a `string`
 *  @returns {number} `uint53` */
export const uint53__lean_string_length__String_length = uint53__lean_string_length__String_Internal_length;
/**
 *  @param {bigint} a `bigint_nat`
 *  @returns {bigint} `bigint_nat` */
export const bigint_nat__lean_uint64_of_nat__UInt64_ofNatLT = bigint_nat__lean_uint64_of_nat__UInt64_ofNat;
/**
 *  @param {bigint} a `bigint_nat`
 *  @returns {number} `uint53` */
export const bigint_nat__uint53__lean_uint64_of_nat__UInt64_ofNatLT = bigint_nat__uint53__lean_uint64_of_nat__UInt64_ofNat;
/**
 *  @param {number} a `uint53`
 *  @returns {bigint} `bigint_nat` */
export const uint53__bigint_nat__lean_uint64_of_nat__UInt64_ofNatLT = (a) => BigInt(a);
/**
 *  @param {number} a `uint53`
 *  @returns {number} `uint53` */
export const uint53__lean_uint64_of_nat__UInt64_ofNatLT = (a) => a;

/* ------------------------------------------------------------ array functions written in Lean */

// The operations of the externs of `ArrayStdExtern`
// (`LeanScript/LeanInitPureExterns/ArrayStdFunctionsNonExternButBigEnoughToLoseInformation.lean`):
// the array functions of `Init` that are written in Lean (`Array.append`, `Array.map`,
// `Array.filter`, …), each written here as JavaScript does it.  They take a generic or a typed
// array (the operations are layout-polymorphic, `JsArrayLayout`), which they only read, and
// always answer a *new* array (the ownership analysis counts on it, `Own.freshExterns`), except
// `array__lean_array_append_mutable`, which pushes onto its first argument.  An operation whose
// result is a typed array while its argument may be of another layout (`Array.map`,
// `Array.flatMap`, `Array.flatten`, `Array.zipWith`) takes the constructor of the typed array
// first (`typedArray__…`).  The `bigint_nat__…` versions read their indices as numbers (an index
// past `2^53` is past the end of any array: `Infinity`) and answer `BigInt`s.

/** An index given as a `BigInt`, as a number (`Infinity` past `2^53`, past the end of any array). */
const $bigIdx = (x) => (x > 9007199254740991n ? Infinity : Number(x));

/** `Array.append` (`a ++ b`): a new array, the elements of `a` then those of `b`. */
export const array__lean_array_append_immutable = (a, b) => {
  if (Array.isArray(a)) return a.concat(b);
  const r = new a.constructor(a.length + b.length);
  r.set(a);
  r.set(b, a.length);
  return r;
};

/** `Array.append`, pushing the elements of `b` onto `a` (a generic array nothing else refers
 *  to; a typed array cannot grow, so it gets a new one).  `b` may be `a` itself. */
export const array__lean_array_append_mutable = (a, b) => {
  if (!Array.isArray(a)) return array__lean_array_append_immutable(a, b);
  const n = b.length;
  for (let i = 0; i < n; i++) a.push(b[i]);
  return a;
};

/** `Array.map f a`, as a generic array. */
export const array__lean_array_map = (f, a) => {
  const n = a.length;
  const r = new Array(n);
  for (let i = 0; i < n; i++) r[i] = f(a[i]);
  return r;
};

/** `Array.map f a`, as a typed array of constructor `C`. */
export const typedArray__lean_array_map = (C, f, a) => {
  const n = a.length;
  const r = new C(n);
  for (let i = 0; i < n; i++) r[i] = f(a[i]);
  return r;
};

/** `Array.filter p a start stop`: the elements of `a[start, min(stop, a.length))` that satisfy `p`. */
export const uint53__lean_array_filter = (p, a, start, stop) => {
  const r = [];
  const e = Math.min(stop, a.length);
  for (let i = start; i < e; i++) if (p(a[i])) r.push(a[i]);
  return Array.isArray(a) ? r : a.constructor.from(r);
};

/** `Array.filter`, on `BigInt` bounds. */
export const bigint_nat__lean_array_filter = (p, a, start, stop) =>
  uint53__lean_array_filter(p, a, $bigIdx(start), $bigIdx(stop));

/** `Array.flatMap f a`, as a generic array. */
export const array__lean_array_flat_map = (f, a) => {
  const r = [];
  for (let i = 0; i < a.length; i++) {
    const b = f(a[i]);
    for (let j = 0; j < b.length; j++) r.push(b[j]);
  }
  return r;
};

/** The arrays `bs` one after the other, as a typed array of constructor `C`. */
const $concatTyped = (C, bs) => {
  let n = 0;
  for (const b of bs) n += b.length;
  const r = new C(n);
  let o = 0;
  for (const b of bs) {
    r.set(b, o);
    o += b.length;
  }
  return r;
};

/** `Array.flatMap f a`, as a typed array of constructor `C`. */
export const typedArray__lean_array_flat_map = (C, f, a) => {
  const bs = [];
  for (let i = 0; i < a.length; i++) bs.push(f(a[i]));
  return $concatTyped(C, bs);
};

/** `Array.flatten a`, as a generic array. */
export const array__lean_array_flatten = (a) => {
  const r = [];
  for (let i = 0; i < a.length; i++) {
    const b = a[i];
    for (let j = 0; j < b.length; j++) r.push(b[j]);
  }
  return r;
};

/** `Array.flatten a`, as a typed array of constructor `C`. */
export const typedArray__lean_array_flatten = (C, a) => $concatTyped(C, a);

/** `Array.reverse a`: a new array. */
export const array__lean_array_reverse = (a) => a.slice().reverse();

/** `Array.extract a start stop` (`a.take n`, `a.drop n`): `a[start, min(stop, a.length))`. */
export const uint53__lean_array_extract = (a, start, stop) => a.slice(start, stop);

/** `Array.extract`, on `BigInt` bounds. */
export const bigint_nat__lean_array_extract = (a, start, stop) =>
  a.slice($bigIdx(start), $bigIdx(stop));

/** `Array.any a p start stop`: does an element of `a[start, min(stop, a.length))` satisfy `p`? */
export const uint53__lean_array_any = (a, p, start, stop) => {
  const e = Math.min(stop, a.length);
  for (let i = start; i < e; i++) if (p(a[i])) return true;
  return false;
};

/** `Array.any`, on `BigInt` bounds. */
export const bigint_nat__lean_array_any = (a, p, start, stop) =>
  uint53__lean_array_any(a, p, $bigIdx(start), $bigIdx(stop));

/** `Array.all a p start stop`: do all the elements of `a[start, min(stop, a.length))` satisfy `p`? */
export const uint53__lean_array_all = (a, p, start, stop) => {
  const e = Math.min(stop, a.length);
  for (let i = start; i < e; i++) if (!p(a[i])) return false;
  return true;
};

/** `Array.all`, on `BigInt` bounds. */
export const bigint_nat__lean_array_all = (a, p, start, stop) =>
  uint53__lean_array_all(a, p, $bigIdx(start), $bigIdx(stop));

/** `Array.contains a x` (`x ∈ a`), `beq` the function of the `BEq` instance: `beq(x, a[i])`
 *  for some `i`. */
export const array__lean_array_contains = (beq, a, x) => {
  for (let i = 0; i < a.length; i++) if (beq(x, a[i])) return true;
  return false;
};

/** `Array.find? p a`: the first element that satisfies `p`, if one does. */
export const array__lean_array_find_opt = (p, a) => {
  for (let i = 0; i < a.length; i++) if (p(a[i])) return { tag: 1, _1: a[i] };
  return { tag: 0 };
};

/** `Array.findIdx? p a`: the index of the first element that satisfies `p`, if one does. */
export const uint53__lean_array_find_idx_opt = (p, a) => {
  for (let i = 0; i < a.length; i++) if (p(a[i])) return { tag: 1, _1: i };
  return { tag: 0 };
};

/** `Array.findIdx?`, answering a `BigInt`. */
export const bigint_nat__lean_array_find_idx_opt = (p, a) => {
  for (let i = 0; i < a.length; i++) if (p(a[i])) return { tag: 1, _1: BigInt(i) };
  return { tag: 0 };
};

/** `Array.idxOf? a x`, `beq` the function of the `BEq` instance: the first `i` with
 *  `beq(a[i], x)`, if there is one. */
export const uint53__lean_array_idx_of_opt = (beq, a, x) => {
  for (let i = 0; i < a.length; i++) if (beq(a[i], x)) return { tag: 1, _1: i };
  return { tag: 0 };
};

/** `Array.idxOf?`, answering a `BigInt`. */
export const bigint_nat__lean_array_idx_of_opt = (beq, a, x) => {
  for (let i = 0; i < a.length; i++) if (beq(a[i], x)) return { tag: 1, _1: BigInt(i) };
  return { tag: 0 };
};

/** `Array.eraseIdx! a i`: a new array without the element `i`; out of bounds Lean panics, and
 *  the value of the panic is the empty array. */
export const uint53__lean_array_erase_idx = (a, i) => {
  if (!(i < a.length)) return a.slice(0, 0);
  const r = new a.constructor(a.length - 1);
  for (let j = 0; j < i; j++) r[j] = a[j];
  for (let j = i + 1; j < a.length; j++) r[j - 1] = a[j];
  return r;
};

/** `Array.eraseIdx!`, on a `BigInt` index. */
export const bigint_nat__lean_array_erase_idx = (a, i) => uint53__lean_array_erase_idx(a, $bigIdx(i));

/** `Array.insertIdx! a i x`: a new array with `x` at `i` (`i ≤ a.length`); out of bounds Lean
 *  panics, and the value of the panic is the empty array. */
export const uint53__lean_array_insert_idx = (a, i, x) => {
  if (!(i <= a.length)) return a.slice(0, 0);
  const r = new a.constructor(a.length + 1);
  for (let j = 0; j < i; j++) r[j] = a[j];
  r[i] = x;
  for (let j = i; j < a.length; j++) r[j + 1] = a[j];
  return r;
};

/** `Array.insertIdx!`, on a `BigInt` index. */
export const bigint_nat__lean_array_insert_idx = (a, i, x) =>
  uint53__lean_array_insert_idx(a, $bigIdx(i), x);

/** `Array.eraseIdxIfInBounds a i`: a new array without the element `i`; out of bounds a copy of
 *  `a` (Lean answers `a` itself; the copy keeps the answer a new array). */
export const uint53__lean_array_erase_idx_if_in_bounds = (a, i) =>
  i < a.length ? uint53__lean_array_erase_idx(a, i) : a.slice();

/** `Array.eraseIdxIfInBounds`, on a `BigInt` index. */
export const bigint_nat__lean_array_erase_idx_if_in_bounds = (a, i) =>
  uint53__lean_array_erase_idx_if_in_bounds(a, $bigIdx(i));

/** `Array.insertIdxIfInBounds a i x`: a new array with `x` at `i` (`i ≤ a.length`); out of
 *  bounds a copy of `a`. */
export const uint53__lean_array_insert_idx_if_in_bounds = (a, i, x) =>
  i <= a.length ? uint53__lean_array_insert_idx(a, i, x) : a.slice();

/** `Array.insertIdxIfInBounds`, on a `BigInt` index. */
export const bigint_nat__lean_array_insert_idx_if_in_bounds = (a, i, x) =>
  uint53__lean_array_insert_idx_if_in_bounds(a, $bigIdx(i), x);

/** `Array.qpartition` (`Init/Data/Array/QSort/Basic.lean`), in place on `as[lo..hi]`
 *  (`lo < hi`): the pivot is the median of `as[lo]`, `as[mid]`, `as[hi]`, moved to `hi`; the
 *  answer is the final position of the pivot. */
const $qpartition = (as, lt, lo, hi) => {
  const swap = (i, j) => {
    const t = as[i];
    as[i] = as[j];
    as[j] = t;
  };
  const mid = Math.floor((lo + hi) / 2);
  if (lt(as[mid], as[lo])) swap(lo, mid);
  if (lt(as[hi], as[lo])) swap(lo, hi);
  if (lt(as[mid], as[hi])) swap(mid, hi);
  const pivot = as[hi];
  let i = lo;
  for (let k = lo; k < hi; k++) {
    if (lt(as[k], pivot)) {
      swap(i, k);
      i++;
    }
  }
  swap(i, hi);
  return i;
};

/** `Array.qsort.sort`, in place on `as[lo..hi]`: Lean's quicksort step for step (it is not
 *  stable, so a different algorithm could order equivalent elements differently); the second
 *  recursive call is a loop. */
const $qsortRange = (as, lt, lo, hi) => {
  while (lo < hi) {
    const mid = $qpartition(as, lt, lo, hi);
    if (mid >= hi) return;
    $qsortRange(as, lt, lo, mid);
    lo = mid + 1;
  }
};

/** `Array.qsort a lt lo hi`: a sorted copy of `a` (the part `a[lo..hi]`). */
export const uint53__lean_array_qsort = (a, lt, lo, hi) => {
  const r = a.slice();
  const n = r.length;
  if (n === 0) return r;
  const lo1 = Math.min(lo, n - 1);
  const hi1 = Math.max(lo1, Math.min(hi, n - 1));
  $qsortRange(r, lt, lo1, hi1);
  return r;
};

/** `Array.qsort`, on `BigInt` bounds. */
export const bigint_nat__lean_array_qsort = (a, lt, lo, hi) =>
  uint53__lean_array_qsort(a, lt, $bigIdx(lo), $bigIdx(hi));

/** `Array.foldr f z a start stop`: `f(a[stop], … f(a[s - 1], z))` with `s = min(start, a.length)`. */
export const uint53__lean_array_foldr = (f, z, a, start, stop) => {
  let acc = z;
  for (let i = Math.min(start, a.length) - 1; i >= stop; i--) acc = f(a[i], acc);
  return acc;
};

/** `Array.foldr`, on `BigInt` bounds. */
export const bigint_nat__lean_array_foldr = (f, z, a, start, stop) =>
  uint53__lean_array_foldr(f, z, a, $bigIdx(start), $bigIdx(stop));

/** `Array.zipWith f a b`, as a generic array (as long as the shorter array). */
export const array__lean_array_zip_with = (f, a, b) => {
  const n = Math.min(a.length, b.length);
  const r = new Array(n);
  for (let i = 0; i < n; i++) r[i] = f(a[i], b[i]);
  return r;
};

/** `Array.zipWith f a b`, as a typed array of constructor `C`. */
export const typedArray__lean_array_zip_with = (C, f, a, b) => {
  const n = Math.min(a.length, b.length);
  const r = new C(n);
  for (let i = 0; i < n; i++) r[i] = f(a[i], b[i]);
  return r;
};

/** `Array.zip a b`: the pairs `{ _1: a[i], _2: b[i] }` (as long as the shorter array). */
export const array__lean_array_zip = (a, b) => {
  const n = Math.min(a.length, b.length);
  const r = new Array(n);
  for (let i = 0; i < n; i++) r[i] = { _1: a[i], _2: b[i] };
  return r;
};

/** `Array.back? a`: the last element, if there is one. */
export const array__lean_array_back_opt = (a) =>
  a.length === 0 ? { tag: 0 } : { tag: 1, _1: a[a.length - 1] };

/** `Array.countP p a`: the number of elements that satisfy `p`. */
export const uint53__lean_array_count_p = (p, a) => {
  let n = 0;
  for (let i = 0; i < a.length; i++) if (p(a[i])) n++;
  return n;
};

/** `Array.countP`, answering a `BigInt`. */
export const bigint_nat__lean_array_count_p = (p, a) => BigInt(uint53__lean_array_count_p(p, a));

/** `List.append` (`l ++ l'`) on the array layout of lists: a new array. */
export const list__lean_list_append = (a, b) => a.concat(b);

/** `List.append` (`l ++ l'`) on cons cells (`ListRepr.taggedUnion`): copies of the cells of
 *  `xs` in front of the cells of `ys`, which are shared, not copied (`xs` itself when `ys` is
 *  empty, `ys` itself when `xs` is). */
export const consList__lean_list_append = (xs, ys) => {
  if (xs.tag === 0) return ys;
  if (ys.tag === 0) return xs;
  const head = { tag: 1, _1: xs._1, _2: ys };
  let cur = head;
  for (let it = xs._2; it.tag === 1; it = it._2) {
    const c = { tag: 1, _1: it._1, _2: ys };
    cur._2 = c;
    cur = c;
  }
  return head;
};
