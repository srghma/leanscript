# `PrimOpBoolean01`: ours vs purescript-backend-optimizer

Files: `PrimOpBoolean01.lean`, the legacy output `legacy-backend/PrimOpBoolean01.js`, ours
`PrimOpBoolean01-pbo.js` / `-faithful.js`, the `Term` dumps `-Term-unoptimized.txt` /
`-Term-optimized.txt`, and the checks `-pbo.check.mjs` / `-faithful.check.mjs`.

The file tests `&&`, `||`, `==`, `!=`, `<`, `>`, `≤`, `≥` and `!` on two `Bool` parameters.

## Before

| fn | Lean | `Term` (optimised) | ours (before) | legacy |
|---|---|---|---|---|
| `test1` | `a && b` | `cond(a, b, false)` | `a && b` | `a && b` |
| `test2` | `a \|\| b` | `cond(a, true, b)` | `a \|\| b` | `a \|\| b` |
| `test3` | `a == b` | `cond(a, b, cond(b, false, true))` | `(a ? b : !b)` | `a === b` |
| `test4` | `a != b` | `cond(cond(a, b, cond(b, false, true)), false, true)` | `!(a ? b : !b)` | `a !== b` |
| `test5` | `a < b` | `cond(a, false, b)` | `(a ? false : b)` | `a < b` |
| `test6` | `a > b` | `cond(b, false, a)` | `(b ? false : a)` | `a > b` |
| `test7` | `a <= b` | `cond(a, b, true)` | `(a ? b : true)` | `a <= b` |
| `test8` | `a >= b` | `cond(b, a, true)` | `(b ? a : true)` | `a >= b` |
| `test9` | `!a` | `cond(a, false, true)` | `!a` | `!a` |

## Now (both presets; JSDoc comments left out)

```js
export const test1 = (a, b) => a && b;
export const test2 = (a, b) => a || b;
export const test3 = (a, b) => a === b;
export const test4 = (a, b) => a !== b;
export const test5 = (a, b) => a < b;
export const test6 = (a, b) => a > b;
export const test7 = (a, b) => a <= b;
export const test8 = (a, b) => a >= b;
export const test9 = (a) => !a;
```

This is the legacy output exactly, line for line (with `export` in front). The checks against
Lean pass: 34/34 at both presets.

## Where the change is

`Term` has no operation that compares two booleans. Lean's `==`, `!=`, `<` and `≤` on `Bool`
are case analyses (`Bool.decEq`, `Bool.decLt`, …), not externs, so they reach `Term` as
conditionals of booleans, and the `Term` optimiser already leaves them as small as they get there.
So the change could not go into `Term → Term`: there is nothing to rewrite them to.

It is in `Term → JsTerm` (`JsTerm/Lower/BoolCmp.lean`, called by the conversion of `Neu.cond`
in `JsTerm/Lower/FromTerm.lean`), with a new `JsTerm` node `JsExpr.boolCmp op a b` for
`===`, `!==`, `<`, `<=`, `>`, `>=` on booleans. Every pass over `JsTerm` handles it. The rules:

* `c ? y : !y` is `c === y`, and `c ? !y : y` is `c !== y`, when both copies of `y` are the same
  variable. Both forms compute `c` and then `y`, so this holds for any condition `c`
  (`(x < y) == b` is `x < y === b`).
* `c ? false : y` is `c < y`, and `c ? y : true` is `c <= y`, only when `c` and `y` are both
  variables. The conditional reads `y` for only one value of `c`, and the comparison always
  reads it, which is only the same thing when reading `y` has no effect. A computed condition
  keeps its conditional (`decide (x < 5) < b` stays `x < 5 ? false : b`), which also avoids
  hard-to-read output such as `x < 5 < b`.
* Between two variables, the one bound first (the parameter to the left) is written on the left:
  `b ? false : a` is `a > b`, not `b < a`. Reading a variable has no effect, so the order doesn't
  matter.
* `!(x op y)` is the opposite comparison with the same operands: `!(a == b)` is `a !== b`,
  `!(a < b)` is `a >= b`, …

JavaScript compares booleans as the numbers `0` and `1`. The identity each rule relies on is
proved in `JsTerm/Lower/BoolCmp.lean` (`JsBoolCmp.eval_eq`, `eval_ne`, `eval_lt`, `eval_le`,
`cond_neg`) and `JsTerm/Syntax/Basic.lean` (`JsBoolCmp.eval_neg`). The model is `JsBoolCmp.eval`,
for example `a < b` is `!a && b`. The rewrite code itself is not formally verified; the
differential checks back it up.

The `JsTerm` optimiser was not changed. The file has no loops or recursion, so labelled blocks
and loops don't come into it.

## Tests

* New snapshot `Tests/SnapshotsMy/BoolCmp.lean`: computed operands, the negations, a comparison
  used as a condition, `decide (a = b)`, and two parameters that are not next to each other.
  110 / 110 checks pass at both presets.
* New spec `primOpBoolean01Spec` in `Tests/Main.lean`. It checks that every legacy line of
  `PrimOpBoolean01.js` appears in our output, checks the expected lines of `BoolCmp`, and runs
  both files' checks.

## Other snapshots

All snapshots were regenerated, and every check against Lean passes. The only other output that
changed is `PrimOpNumber02`: in `testEq` it is `return x$1 === expected;` (was
`x$1 ? expected : !expected`), and in `testNe` it is `return x$1 !== expected;`.
