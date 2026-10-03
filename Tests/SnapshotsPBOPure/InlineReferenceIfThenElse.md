# `InlineReferenceIfThenElse.lean` compared with `InlineReferenceIfThenElse.js` (purescript-backend-optimizer)

## The output (`InlineReferenceIfThenElse-pbo.js`; `-faithful.js` differs only in the header and the `n` suffixes)

```js
export const fn = (_r) => 0;
export const test1 = 42;
export const extern1 = { _1: true, _2: 0 };
export const test2 = 42;
```

purescript-backend-optimizer writes:

```js
const fn = (_ignored) => 0;
const test1 = 42;
const extern1 = { a: { b: { c: true } }, d: /* #__PURE__ */ fn() };
const test2 = 42;
export { extern1, fn, test1, test2 };
```

## Comparison

| | purescript-backend-optimizer | ours |
| :-- | :-- | :-- |
| `fn` | `(_ignored) => 0` | `(_r) => 0` (same) |
| `test1` | `42` | `42` (same) |
| `test2` | `42` | `42` (same) |
| `extern1` | `{ a: { b: { c: true } }, d: fn() }`: three objects, and a call of `fn` when the module loads | `{ _1: true, _2: 0 }`: one object, no call |

`test1` and `test2` are the constant `42`, as in purescript-backend-optimizer. `extern1` is smaller
and needs no call when the module loads:

* `RecB` and `RecC` have a single field, so they are represented by that field: `extern1.a.b.c`
  is `extern1._1`, so `RecA` is one object.
* `fn ()` is computed when the code is translated (`0`). purescript-backend-optimizer keeps the
  call and marks it `/* #__PURE__ */`.

The fields are numbered (`_1`, `_2`) rather than named. This is the encoding of structures used
everywhere in the project.

Here all the work is done while Lean is turned into `Term`. The unoptimised `Term` of `test1` and
`test2` is already `ret 42`, and that of `extern1` is `ret ⟨true, 0⟩`
(`InlineReferenceIfThenElse-Term-unoptimized.txt`): every `if` in the file is on a value known
when the code is translated, so it is decided right away. None of the three phases has anything
left to do for this file. It has no loops and no recursion, so labeled blocks and loops don't come
into it.

## Added in this run: tests whose answer is known from an enclosing `if`

To test the phases themselves, `Tests/SnapshotsMy/IfThenElseKnownField.lean` has variants where
the record is built from parameters. There, the condition can't be decided while Lean is turned
into `Term`. Most of them already came out well (`test3 = (x) => 42`, `test5 = (x) => x`,
`test6 = (r) => (r._1 ? r._2 : 0)`). One gap showed up: a condition tested again inside an arm of
an `if` on the same condition was tested again in the JavaScript as well:

```lean
def test7 (c : Bool) (x : Int) : Int :=
  let rec1 : RecA := { a := { b := { c := c } }, d := x }
  if rec1.a.b.c then (if rec1.a.b.c then x else 0) else (if rec1.a.b.c then 1 else x + 2)
```

```js
// before
export const test7 = (c, x) => {
  if (c) {
    return c ? x : 1;
  }
  return c ? 0 : int53__lean_int_add(x, 2);
};
// now
export const test7 = (c, x) => (c ? x : int53__lean_int_add(x, 2));
```

The fix is a new rewrite in the `Term -[optimize]-> Term` phase: `Term.knownTests`
(`LeanScript/Term/Optimize/KnownTest.lean`), which runs right after the known fields
(`Term.reuseFields`).

* **What it does:** it walks the statement knowing the value of some boolean unknowns. Inside
  `if x then … else …`, where `x` is an unknown or its negation `!x`, the arms know the value of
  `x`.
  * An `if` on a known condition is replaced by the arm it takes.
  * A conditional answer `ret (x ? a : b)` on a known `x` becomes `ret a` (or `ret b`).
* **Where the facts go:** they are carried under `let`s, case analyses and join points, and into
  open closure bodies. Closed bodies start with none.
* **Levels:** dropping an arm can change the level of the statement. So the walk returns the
  statement together with its level, and only a body (whose level is recorded in its type) has
  to keep its own.
* **Proved:**
  * `Term.knownTests_eval`: the value does not change. `Term.optimize_eval`,
    `Term.optimizeN_eval` and `Term.optimize_run` are extended accordingly.
  * `Term.numCalls_knownTests`: no call is added. `Term.numCalls_optimize` is extended
    accordingly.

Other cases in the variant file that now come out as a single conditional:
* `test8`, the same field of a record parameter tested twice: `(r) => (r._1 ? r._2 : 1)`.
* `test9`, a negated condition: `(c, x) => (c ? x + 1 : x)`.
* `test10`, the inner test under a `let`: the inner test is gone.

## Formally (`Tests/TermTests/Optimize/KnownTestTest.lean`)

The snapshot's definitions and the variants are translated to `Term` in Lean (`#leanscript_to_term`):

* `test1_translation_pretty`, `test2_translation_pretty`: the translations are `ret 42`;
  `test1_optimized_run`, `test2_optimized_run`: the optimised statements compute `42`.
* `test7_translation_pretty` (three tests of `c`), `test7_knownTests_pretty` (after
  `Term.knownTests` alone: one test), `test7_optimized_pretty` (after the optimiser: one
  conditional `cond(x2, x4, lean_int_add(x4, 2))`), and `test8_optimized_pretty` … `test10_optimized_pretty`.
* `test7_knownTests_run`, `test7_optimized_run` … `test10_optimized_run`: for every input, the
  rewritten statements compute the Lean functions `test7` … `test10`.

The `…_run` theorems are kernel-checked (`rfl` after the general `Term.optimizeN_run` /
`Term.knownTests_run`); the `…_pretty` ones use `native_decide`, like the other snapshot tests.

## Testing

* `inlineReferenceIfThenElseSpec` in `Tests/Main.lean` runs both files on both presets. It checks
  the lines above, checks that no repeated test is left (`return c ?`, `c ? 0`, …), and runs their
  checks under node: 3 for `InlineReferenceIfThenElse` and 83 for `IfThenElseKnownField`, per
  preset.
* Every snapshot was regenerated: all checks pass, and no other generated file changed.
