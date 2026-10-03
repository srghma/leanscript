# `InlineReferencePrimOpBoolean`: ours vs purescript-backend-optimizer

Files: `InlineReferencePrimOpBoolean.lean`, the legacy output
`legacy-backend/InlineReferencePrimOpBoolean.js`, ours `InlineReferencePrimOpBoolean-pbo.js` /
`-faithful.js`, the `Term` dumps `-Term-unoptimized.txt` / `-Term-optimized.txt`, and the checks
`-pbo.check.mjs` / `-faithful.check.mjs`.

The file tests that `&&`, `||` and `!` on boolean fields whose values are known (of a local
record `r`, through nested records `r.a.b.c`, and of a constant `extern1`) are decided at compile
time.

## Legacy (purescript-backend-optimizer)

```js
const fn = (v) => 0;
const test1 = 42;
const test2 = 42;
const test3 = 42;
const extern1 = { a: { b: { c: true } }, d: /* #__PURE__ */ fn({}), e: true, f: false };
const test4 = 42;
const test5 = 42;
const test6 = 42;
```

## Ours (preset `pbo`; `faithful` is the same with `0n`, `42n`)

```js
export const fn = (x) => 0;
export const test1 = 42;
export const test2 = 42;
export const test3 = 42;
export const extern1 = { _1: true, _2: 0, _3: true, _4: false };
export const test4 = 42;
export const test5 = 42;
export const test6 = 42;
```

(JSDoc comments left out. The structures `SubRec1`/`SubRec2` have one field each, so `r.a.b.c`
is represented by the boolean itself: `extern1` is a flat object.)

## Comparison

| | legacy | ours |
|---|---|---|
| `test1`–`test6` | `42` | `42` |
| `extern1.d` | `fn({})` called when the module loads | `0`, computed at compile time |
| nested single-field records | three nested objects | one flat object |
| conditionals left | none | none |

So on this file the output already was on par (and slightly better for `extern1`). The
conditions are decided while the Lean code is turned into `Term`, before the optimiser runs.

## Variants with unknown inputs: `Tests/SnapshotsMy/PrimOpBooleanKnownField.lean`

To exercise the optimiser itself, `PrimOpBooleanKnownField.lean` (`test7`–`test22`) uses the same
shapes, but with the record, or the operands of `&&`/`||`/`!`, as parameters. Output (preset `pbo`):

```js
export const test7  = (x, g) => x;                          // known fields of a record built from parameters
export const test8  = (x, g) => (g ? 42 : 0);               // false || g  ==>  g
export const test9  = (r) => (r._1 && r._3 ? 42 : 0);       // one conditional on `&&`
export const test10 = (r) => (r._4 || r._1 ? 42 : r._2);
export const test11 = (r) => (r._1 ? 42 : 0);               // !c  ==>  arms swapped
export const test12 = (c, d, x) => (c && d ? x : 2);        // inside `c && d`, c is true
export const test13 = (c, d, x) => (c || d ? 1 : 2);        // in the else of `c || d`, c is false
export const test14 = (c, x) => (c ? x : 1);                // in the else of `!c`, c is true
export const test15 = (c, x) => 7;                          // c && false  ==>  false
export const test16 = (c, x) => x;                          // c || true   ==>  true
export const test17 = (c) => c;                             // c && c      ==>  c
export const test18 = (c) => true;                          // !c || c     ==>  true
export const test19 = (c, x) => 7;                          // c ? 7 : 7   ==>  7
export const test20 = (r) => {                              // facts of both arms of `&&`
  const { _1: f$1 } = r;
  if (f$1 && r._3) {
    return r._2;
  }
  return f$1 ? 1 : 2;
};
export const test21 = (c, d) => c && d;                     // plain operators stay operators
export const test22 = (c, d) => c || !d;
```

All 12 checks of `InlineReferencePrimOpBoolean` and all 141 checks of `PrimOpBooleanKnownField`
pass in node at both presets (`lake exe tests`, spec `InlineReferencePrimOpBoolean`).

## Where the optimisations live

All of them are in the `Term -[optimize]-> Term` phase, in `Term.knownTests`
(`LeanScript/Term/Optimize/KnownTest.lean`, with `LeanScript/Term/Optimize/KnownCond.lean`), and
each comes with a proof that it does not change `Term.eval`:

* `Neu.factsOf`: what is known in each arm of a test of `p && q` (both true in the `then` arm),
  `p || q` (both false in the `else` arm) and `!p` (the negated facts); `Neu.factsOf_holds`.
* `Neu.condSimp` / `PExpr.condSimp`: simplification of conditions and of pure boolean
  expressions under the known facts (`c && false`, `c || true`, `c && c`, `!c || c`,
  `c ? a : a`); `Neu.condSimp_eval`.
* `Term.mergeJumps?`, `Term.mkIteJ`, `Term.joinOrLet`, `Term.letEOrSubst`: a join point whose body
  is `if c then jump j a else jump j b` at type `Bool` becomes a value `c ? a : b` (substituted when
  it is used once), so `&&`/`||` that Lean compiles into join points become JS operators instead
  of `let x; if (...) { x = ...; } else { x = ...; }` blocks. Restricted to `Bool` so that
  constructor jumps stay for the other optimisations.

One fallback is in `Term -[convert]-> JsTerm` (`JsTerm/Lower/FromTerm.lean`): `Neu.condSimp []` is
applied to every conditional expression, for cases in open function bodies that the `Term` pass
leaves (e.g. `c ? 7 : 7`, `c && false`). No change was needed in `JsTerm -[optimize]-> JsTerm`, and
no loops or labeled blocks arise in this file (it has no recursion).

## Side effects on other snapshots

* `KnownConstructors`: `test5 = (x) => 42 < x && false` became `(x) => false`.
* `PrimOpNumber02` (`testEq`, `testNe`): `if (noInline(a, b)) { x$2 = true; } else { x$2 = false; }`
  became `x$2 = noInline(a, b);` (and `x$2 = !noInline(a, b);` for the swapped arms).
