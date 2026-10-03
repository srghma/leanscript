# `InlineReferencePrimOpInt`: ours vs purescript-backend-optimizer

Files: `InlineReferencePrimOpInt.lean` (and the PureScript original `InlineReferencePrimOpInt.purs`),
the legacy output `legacy-backend/InlineReferencePrimOpInt.js`, ours `InlineReferencePrimOpInt-pbo.js` /
`-faithful.js`, the `Term` dumps `-Term-unoptimized.txt` / `-Term-optimized.txt`, and the checks
`-pbo.check.mjs` / `-faithful.check.mjs` (14 checks per preset, all passing).

The file tests that integer arithmetic (`+ - * /`) on the fields of a record that is known
(`{ a := { b := { c := 99 } }, d := fn (), e := 11 }`) is computed at compile time, both when the
record is built locally (`localTest`, inlined) and when it is a constant (`extern`, `externTest`).

## Legacy (purescript-backend-optimizer)

```js
const fn = (v) => 0;
const localTest = (f) => {
  const rec = { a: { b: { c: 99 } }, d: fn({}), e: 11 };
  const res = f(rec);
  if (res !== -2147483648) { return res; }
  return fn(rec);
};
const test1 = 110; const test2 = 88; const test3 = 1089; const test4 = 9;
const extern = { a: { b: { c: 99 } }, d: /* #__PURE__ */ fn({}), e: 11 };
const externTest = (f) => {
  const res = f(extern);
  if (res !== -2147483648) { return res; }
  return -2147483648;
};
const test5 = 110; const test6 = 88; const test7 = 1089; const test8 = 9;
```

## Ours (preset `pbo`; `faithful` is the same with `n` literals; JSDoc left out)

Before this change:

```js
export const fn = (x) => 0;
export const localTest = (f) => {
  const x$1 = f({ _1: 99, _2: 0, _3: 11 });
  return x$1 === -2147483648 ? 0 : x$1;
};
export const test1 = 110; /* … */ export const test4 = 9;
export const extern = { _1: 99, _2: 0, _3: 11 };
export const externTest = (f) => {
  const x$1 = f({ _1: 99, _2: 0, _3: 11 });
  return x$1 === -2147483648 ? -2147483648 : x$1;
};
export const test5 = 110; /* … */ export const test8 = 9;
```

Now:

```js
export const fn = (x) => 0;
export const localTest = (f) => {
  const x$1 = f({ _1: 99, _2: 0, _3: 11 });
  return x$1 === -2147483648 ? 0 : x$1;
};
export const test1 = 110; /* … */ export const test4 = 9;
export const extern = { _1: 99, _2: 0, _3: 11 };
export const externTest = (f) => f(extern);
export const test5 = 110; /* … */ export const test8 = 9;
```

## Comparison

| | legacy | ours |
|---|---|---|
| `test1`–`test8` | constants `110`, `88`, `1089`, `9` | the same |
| `extern` | nested records, `fn({})` called at load time (`inline never`) | a flat record, `fn ()` computed at compile time (`0`); one-field structures are unboxed |
| `localTest`: the record | nested records, `fn({})` called | a flat record literal, `d` computed (`0`) |
| `localTest`: the fallback `fn rec` | `fn(rec)` called | `0` (computed; `fn` is pure) |
| `localTest`: the test | `if … { return res; } return …;` | one expression `x$1 === -2147483648 ? 0 : x$1` |
| `externTest`: the record | reads `extern` | **before**: built again (`f({ _1: 99, … })`); **now**: reads `extern` |
| `externTest`: `if res != bottom then res else bottom` | kept (a test and two returns) | **now**: gone, `res` (both arms are equal when the test fails) |
| `externTest` overall | 5 statements | `(f) => f(extern)` |

So ours is better than legacy on every definition: the same constants, no call of `fn` at load
time or in `localTest`, and `externTest` is a single call.

## What changed, and in which phase

1. **`Term -[optimize]-> Term`: `x == k ? k : x` is `x`** (`LeanScript/Term/Optimize/KnownCond.lean`).
   The `Term` optimiser had turned `if res != k then res else k` into the conditional
   `cond(lean_int_dec_eq(res, k), k, res)`.  When the test holds, `res` equals `k`, so both arms
   have the same value and the conditional is its second arm.  `Neu.eqView?` recognises a call of
   an equality whose result is exactly the equality of its operands (`Int`, `Nat` both
   `Nat.decEq` and `Nat.beq`, `String`, `UInt8`–`UInt64`, `Int8`–`Int64`; not `Float`, whose `==`
   is not the equality of the values), with the proof `Neu.EqSplit.eval`.
   `Neu.condIsElse` checks that the arms are the two operands (in either order, compared with
   `PExpr.same`), and `Neu.mkCondS` (used by `Neu.condSimp`, which the optimiser and the
   `Term -[convert]-> JsTerm` fallback both call) returns that arm.  The value is unchanged:
   `Neu.condIsElse_eval` and the updated `Neu.mkCondS_eval` are proved, sorry-free, against
   `Term.eval`.  After that rewrite the result is used once (`x3 [1]`) and is inlined, so the
   function is `(f) => f(…)`.

2. **`Term -[convert]-> JsTerm`, module level: functions read the record constants before them**
   (`JsTerm/Lower/ShareConsts.lean`, `shareConstValues`).  `Term` has no global names, so
   `extern`'s value is inlined into `externTest`.  The module pass that already shared constant
   values between constants now also replaces, in the body of a function, a record/constructor
   value that is written exactly as the value of a constant defined *before* that function, by
   the constant's name.  It only does this for frozen values (`JsExpr.isFrozen`: literals, enums,
   records and constructors of those, no arrays and no lists), because a function may update
   in place an array it owns (`LeanScript.Term.Ownership`), but records and constructors are
   never updated in place.  Only earlier constants are used: a later constant may not be
   initialised yet when a constant between the two calls the function.  `localTest` comes before
   `extern` in the module, so it keeps building its record, which is correct.

No labeled blocks or loops are involved: the file has no loops or recursion.

## Variants: `Tests/SnapshotsMy/PrimOpIntEqSelect.lean` (99 checks per preset, all passing)

```js
export const selInt = (x) => x;                  // if x != -2147483648 then x else -2147483648
export const selIntEq = (x) => x;                // if x == 5 then 5 else x
export const selIntFlip = (x) => 5;              // if 5 == x then x else 5
export const selIntVars = (x, y) => x;           // if x == y then y else x
export const selNat = (n) => n;                  // if n = 3 then 3 else n
export const selString = (s) => s;
export const selUInt8 = (x) => x;
export const selInt32 = (x) => x;
export const selCall = (f, x) => f(x);           // let r := f x; if r != 0 then r else 0
export const keepOther = (x) => (x === 5 ? 6 : x);   // different value: kept
export const keepFloat = (x) => (x === 0 ? 0 : x);   // Float: kept
export const origin = { _1: 3, _2: 4 };
export const applyOrigin = (f) => f(origin);     // the record constant is read
export const arr = [1, 2, 3];
export const applyArr = (f) => f([1, 2, 3]);     // an array is never shared
```

`Tests/Main.lean` has a new spec, `InlineReferencePrimOpInt`. It checks these fragments at both
presets and runs the generated checks under node.
