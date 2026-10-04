# `PrimOpBoolean02`: ours vs purescript-backend-optimizer

Files: `PrimOpBoolean02.lean`, the legacy output `legacy-backend/PrimOpBoolean02.js`, ours
`PrimOpBoolean02-pbo.js` / `-faithful.js`, the `Term` dumps `-Term-unoptimized.txt` /
`-Term-optimized.txt`, and the checks `-pbo.check.mjs` / `-faithful.check.mjs`.

`boolValues op` is `#[op true true, op true false, op false true, op false false]`, marked
`@[inline]`. `test1` … `test8` are `boolValues` applied to `&&`, `||`, `==`, `!=`, `<`, `>`, `≤`,
`≥`, and `test9` is `#[!true, !false]`.

## The tests

The `Term` optimiser inlines `boolValues` and the operator into every test and folds each one
to an array literal (`-Term-optimized.txt`: `ret #[true, false, false, false]`, …). So these
were already the legacy output, line for line (with `export` in front), at both presets:

```js
export const test1 = [true, false, false, false];
…
export const test9 = [false, true];
```

## `boolValues`

| | |
|---|---|
| legacy | `const boolValues = (op) => [op(true)(true), op(true)(false), op(false)(true), op(false)(false)];` |
| ours (before) | `const x$1 = op(true, true); const x$2 = op(true, false); return [x$1, x$2, op(false, true), op(false, false)];` |
| ours (now) | `export const boolValues = (op) => [op(true, true), op(true, false), op(false, true), op(false, false)];` |

(`legacy` and `now` are printed over several lines.) We now write the legacy shape, with one call
of two arguments instead of two calls of one (an `(a, b) => …` operator is a function of two
parameters in our output), at both presets.

### Why the first two calls were named

The `Term` (`-Term-optimized.txt`) is already as good as `Term` can make it: eight `let`s, each
used once, in the order they are used (`let x3 := x2 true; let x4 := x3 true; …;
ret #[x4, x6, x8, x10]`). The conversion makes one call of two arguments out of each pair. The
JavaScript was worse for two reasons that had nothing to do with `Term`:

1. **The conversion bound each literal argument to a constant.** The `JsTerm` was
   `const a = true; const b = true; const x = op(a, b); …`: twelve constants instead of four.
   The printer writes the literal constants at their uses, so they did not show in the output.
2. **The printer's decision whether to write a call at its use had a limit.** It may write a call
   read once at its use only when no other call comes in between (calls may have effects, so
   their order is kept). Calls in between that are themselves written at their uses are allowed,
   but finding out which ones they are was a search, cut off after 3 constants
   (`fuel`). The literal constants counted against that limit, so only the last two calls were
   written at their uses. Without the literal constants, the limit still stopped longer runs:
   `#[op 1 2, …, op 11 12]` (six calls) kept `x$1` and `x$2`.

### What changed

In your order of preference:

* **`Term → Term`:** nothing could be done here. The `Term` is already minimal, and both problems
  come after it.
* **`Term → JsTerm` (conversion):** a literal argument of a call is passed as it is
  (`op(true, false)`), not first bound to a constant. It is a new kind of conversion reference,
  `Ref.lit` (`JsTerm/Lower/Basic.lean`), produced by `cBindArg` (`JsTerm/Lower/FromTerm.lean`).
* **The decision to write a constant at its use** (used by the printer; defined in
  `JsTerm/Syntax/Vars/Occs.lean`): for a run of constants, the decisions are now made once, from
  the last constant up (`JsBlock.constPlan`). Each constant's decision uses the decisions already
  made for the constants after it (the new `ahead` argument of `JsBlock.useFirst` /
  `constInline`) instead of searching for them again. This removes the limit for the constants of
  a run, and takes time quadratic in the length of the run. The search used before was
  exponential, which is why it had a limit. The printer (`JsTerm/Print/Mini/Block.lean`) computes
  the plan at the first constant of a run and passes the rest of it on in `Scope.plan`. The rule
  itself has not changed: a call is written at its use only if nothing that is not also written
  at its use is computed before it. So calls are still made in the order the program makes them.
  This step is not a `JsTerm → JsTerm` rewrite. The printer is where a constant is written at
  its use, and only the analysis behind that choice changed.

This file has no loops or recursion, so labelled blocks and loops didn't come into it.

## Checks

* `PrimOpBoolean02`: 9/9 checks against Lean pass at both presets (one per test; `boolValues` takes a function, so it has none).
* New snapshot `Tests/SnapshotsMy/CallChain.lean`:
  * runs of six and eight calls on literals and variables, all written at their uses
    (`chain6`, `chainVars`);
  * calls whose arguments are themselves calls (`chainStr`:
    `[f("a"), f(g(1)), f("b"), f(g(2)), f("c")]`);
  * calls made in one order and read in the opposite one (`swapped`): the first two stay named,
    `const x$1 = op(1, 2); const x$2 = op(3, 4); return [op(5, 6), x$2, x$1];`, so the calls
    are still made in the program's order.

  21/21 checks pass at both presets.
* `primOpBoolean02Spec` in `Tests/Main.lean`:
  * checks that every legacy `const testN = …;` line appears in our output, after `export `;
  * checks the `boolValues` array and the `CallChain` fragments;
  * checks that no literal is bound to a constant;
  * runs both files' checks with node.
