# `InlineReferencePrimOpNumber`: ours vs purescript-backend-optimizer

Files: `InlineReferencePrimOpNumber.lean` (the PureScript original is `InlineReferencePrimOpNumber.purs`),
the legacy output `legacy-backend/InlineReferencePrimOpNumber.js`, ours `InlineReferencePrimOpNumber-pbo.js` /
`-faithful.js`, the `Term` dumps `-Term-unoptimized.txt` / `-Term-optimized.txt`, and the checks
`-pbo.check.mjs` / `-faithful.check.mjs` (13 checks per preset, all passing).

The file tests that `Float` arithmetic (`+ - * /`) on the fields of a known record
(`{ a := { b := { c := 99.0 } }, d := fn (), e := 11.0 }`) is computed at compile time, both when the
record is built locally (`localTest`, inlined) and when it is a constant (`extern`, `externTest`).

## A difference between the Lean file and the PureScript original

`InlineReferencePrimOpNumber.lean` leaves out the test against `bottom` (`bottom :: Number` is
`-Infinity`) of the PureScript original:

```purescript
localTest f = do
  let rec = { a: { b: { c: 99.0 }}, d: fn {}, e: 11.0 }
  let res = f rec
  if res /= bottom then res else fn rec
externTest f = do
  let res = f extern
  if res /= bottom then res else bottom
```

The Lean `localTest` is just `f r`, and `externTest` is `f extern`.  So, to compare like with
like, the faithful translation with the test is in `Tests/SnapshotsMy/PrimOpNumberBottom.lean`
(as `InlineReferencePrimOpInt.lean` already has it for `Int`), together with more variants.

## Legacy (purescript-backend-optimizer)

```js
const fn = (v) => 0.0;
const localTest = (f) => {
  const rec = { a: { b: { c: 99.0 } }, d: fn({}), e: 11.0 };
  const res = f(rec);
  if (res !== -Infinity) { return res; }
  return fn(rec);
};
const test1 = 110.0; const test2 = 88.0; const test3 = 1089.0; const test4 = 9.0;
const extern = { a: { b: { c: 99.0 } }, d: /* #__PURE__ */ fn({}), e: 11.0 };
const externTest = (f) => {
  const res = f(extern);
  if (res !== -Infinity) { return res; }
  return -Infinity;
};
const test5 = 110.0; const test6 = 88.0; const test7 = 1089.0; const test8 = 9.0;
```

## Ours, `InlineReferencePrimOpNumber.lean` (preset `pbo`; `faithful` is the same; JSDoc left out)

```js
export const fn = (x) => 0;
export const localTest = (f) => f({ _1: 99, _2: 0, _3: 11 });
export const test1 = 110; export const test2 = 88; export const test3 = 1089; export const test4 = 9;
export const extern = { _1: 99, _2: 0, _3: 11 };
export const externTest = (f) => f(extern);
export const test5 = 110; export const test6 = 88; export const test7 = 1089; export const test8 = 9;
```

This was already the output at the start of this work (`externTest` reading `extern` came from
`shareConstValues`, see `InlineReferencePrimOpInt.md`).

## Ours, the faithful `PrimOpNumberBottom.lean`

Before this change:

```js
export const localTest = (f) => {
  const x$1 = f({ _1: 99, _2: 0, _3: 11 });
  return x$1 === -Infinity ? 0 : x$1;
};
export const externTest = (f) => {
  const x$1 = f(extern);
  return x$1 === -Infinity ? -Infinity : x$1;
};
```

Now:

```js
export const localTest = (f) => {
  const x$1 = f({ _1: 99, _2: 0, _3: 11 });
  return x$1 === -Infinity ? 0 : x$1;
};
export const externTest = (f) => f(extern);
```

(`test1`–`test8` are the constants `110`, `88`, `1089`, `9` in both.)

## Comparison

| | legacy | ours |
|---|---|---|
| `test1`–`test8` | constants `110.0`, `88.0`, `1089.0`, `9.0` | the same |
| `extern` | nested records, `fn({})` called at load time | a flat record, `fn ()` computed at compile time (`0`); one-field structures are unboxed |
| `localTest`: the record | nested records, `fn({})` called | a flat record literal, `d` computed (`0`) |
| `localTest`: the fallback `fn rec` | `fn(rec)` called | `0` (computed; `fn` is pure) |
| `localTest`: the test | `if … { return res; } return …;` | one expression `x$1 === -Infinity ? 0 : x$1` |
| `externTest`: `if res != bottom then res else bottom` | kept (a test and two returns) | **now** gone: `res` (when the test fails, the arms are equal) |
| `externTest` overall | 5 statements | `(f) => f(extern)` |

So ours is better than legacy on every definition, for the Lean file as given and for the faithful
variant.

## What changed

1. **`Term -[optimize]-> Term`** (`LeanScript/Term/Optimize/KnownCond.lean`): `Neu.eqView?` now
   also recognises the equality of `Float` (`lean_float_beq`) and `Float32` (`lean_float32_beq`)
   when one operand is a literal that is **not a zero** (`PExpr.floatNonzeroLit`, e.g.
   `-Infinity`, `5.0`, `-0.5`).  Then `x == k ? k : x` and `if x != k then x else k` become `x`
   (`Neu.condIsElse`).
   * In the semantics of `Term`, floats are `HashableFloat` (never `NaN` or `-0.0`), on which `==`
     is equality (`HashableFloat.beq_iff_eq`); so the proof that the value does not change
     (`Neu.condIsElse_eval`, `Neu.mkCondS_eval`, and so `Term.optimize_eval`) goes through
     without changes, using only the standard axioms.
   * The restriction to non-zero literals keeps the JavaScript exact on **every** number, `-0`
     and `NaN` included: for such a `k`, `x === k` holds only when `x` has the bits of `k`
     (`LeanScript.Gen.float_eq_iff_beq_of_finite`, and `±Infinity` has one bit pattern too).
     Against `0.0` it would not be (`-0 === 0`), so `if x == 0.0 then 0.0 else x` stays.
2. **`PExpr.same`** (`LeanScript/Term/Optimize/ShareTest.lean`): `Float` and `Float32` literals
   are now compared (`LeanPrimTy.litBEq`), so `-Infinity` in the test and in the arm are
   recognised as the same.  Equal `HashableFloat`s have the same bits, so this is exact as well.

Nothing was needed in `Term -[convert]-> JsTerm` or `JsTerm -[optimize]-> JsTerm`.  The file has no
loops or recursion, so labeled blocks/loops do not come into it.

## Variants (`Tests/SnapshotsMy/PrimOpNumberBottom.lean`, 92 checks per preset, all passing)

```js
export const selNegInf = (x) => x;      // if x == -∞ then -∞ else x
export const selPosInf = (x) => x;      // if x != ∞ then x else ∞
export const selFive = (x) => x;        // if x == 5.0 then 5.0 else x
export const selFiveFlip = (x) => 5;    // if 5.0 == x then x else 5.0
export const selNegHalf = (x) => x;     // if x != -0.5 then x else -0.5
export const selCall = (f, x) => f(x);  // let r := f x; if r != 2.5 then r else 2.5
export const keepZero = (x) => (x === 0 ? 0 : x);       // a zero: stays
export const keepOther = (x) => (x === 5 ? 6 : x);      // another value: stays
export const keepVars = (x, y) => (x === y ? y : x);    // no literal: stays
```
