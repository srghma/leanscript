# `InlineReferenceOpIsTag`: ours vs purescript-backend-optimizer

Files: `InlineReferenceOpIsTag.lean` (and the PureScript original `InlineReferenceOpIsTag.purs`),
the legacy output `legacy-backend/InlineReferenceOpIsTag.js`, ours `InlineReferenceOpIsTag-pbo.js` /
`-faithful.js`, the `Term` dumps `-Term-unoptimized.txt` / `-Term-optimized.txt`, and the checks
`-pbo.check.mjs` / `-faithful.check.mjs`.

The file tests that a `match` on a value whose constructor is known (`Cons 1 (fn ())`, directly,
through nested records `rec1.a.b.c`, and through constants `extern1`, `extern2.a.b.c`,
`extern3.d.a.b.c`) is decided at compile time.

## Legacy (purescript-backend-optimizer)

```js
const $List = (tag, _1, _2) => ({ tag, _1, _2 });
const Cons = (value0, value1) => $List("Cons", value0, value1);
const Nil = /* #__PURE__ */ $List("Nil");
const test1 = (fn) => $List("Cons", 0, $List("Cons", 1, fn({})));
const test2 = (fn) => $List("Cons", 0, $List("Cons", 1, fn({})));
const test3 = (fn) => $List("Cons", 0, $List("Cons", 1, fn({})));
const fn$p = (v) => Nil;
const extern2 = { a: { b: { c: /* #__PURE__ */ $List("Cons", 1, /* #__PURE__ */ fn$p({})) } } };
const extern3 = { d: extern2, e: /* #__PURE__ */ fn$p({}) };
const test4 = /* #__PURE__ */ $List("Cons", 0, extern1);
const test5 = /* #__PURE__ */ (() => $List("Cons", 0, extern2.a.b.c))();
const extern1 = /* #__PURE__ */ $List("Cons", 1, /* #__PURE__ */ fn$p({}));
const test6 = /* #__PURE__ */ (() => $List("Cons", 0, extern2.a.b.c))();
```

## Ours (preset `pbo`; `faithful` is the same with `0n`, `1n`)

```js
export const test1 = (fn) => ({ tag: 0, _1: 0, _2: { tag: 0, _1: 1, _2: fn() } });
export const test2 = (fn) => ({ tag: 0, _1: 0, _2: { tag: 0, _1: 1, _2: fn() } });
export const test3 = (fn) => ({ tag: 0, _1: 0, _2: { tag: 0, _1: 1, _2: fn() } });
export const fn_prime = { tag: 1 };
export const extern1 = { tag: 0, _1: 1, _2: { tag: 1 } };
export const extern2 = extern1;
export const extern3 = { _1: extern1, _2: { tag: 1 } };
export const test4 = { tag: 0, _1: 0, _2: extern1 };
export const test5 = test4;
export const test6 = test4;
```

(`test1`–`test3` are printed over several lines in the file; the JSDoc comments are left out here.)

## Comparison

| | legacy | ours |
|---|---|---|
| `test1`–`test3`: `match` on a constructor built in place (directly, through `rec.a.b.c`, through `rec2.d.a.b.c`) | decided | decided (already in the `Term` produced from Lean: `-Term-unoptimized.txt` has no case analysis left) |
| `test1`–`test3`: the records `rec1`, `rec2` | gone | gone (a structure of one field is its field; the unused `rec2.e` is dropped) |
| `test3`: the unused `rec2.e = fn ()` | dropped | dropped (Lean is pure, the call is dead) |
| `fn'` / `fn_prime` | a function `(v) => Nil` | the constant `{ tag: 1 }` (a `Unit → τ` definition is a lazy value, read without a call: the project's convention) |
| `extern1`, `extern2`, `extern3`: calls of `fn'` | kept, marked `#__PURE__`, run at load time (`inline never`) | computed at compile time (`{ tag: 1 }`) |
| `extern2` | a nested record `{ a: { b: { c: … } } }` | `extern1` (the records of one field are unboxed, and the value is the same as `extern1`'s: `shareConstValues`) |
| `extern3` | `{ d: extern2, e: fn$p({}) }` | `{ _1: extern1, _2: { tag: 1 } }` |
| `test4` | `$List("Cons", 0, extern1)` | `{ tag: 0, _1: 0, _2: extern1 }` |
| `test5`, `test6` | an IIFE each, `(() => $List("Cons", 0, extern2.a.b.c))()`, built at load time | `test4` (the same value: no new object, no IIFE) |
| constructors | a helper `$List(tag, …)` and string tags | object literals with numeric tags (no helper call) |

So ours is on par on `test1`–`test4`, and better on `extern1`–`extern3` (no calls at load time),
on `extern2` (no nested records) and on `test5`/`test6` (no IIFE, no new object: they read
`test4`).

**Nothing in the JavaScript needed to change** for this file: every decision above is already
made in the `Term -[optimize]-> Term` phase (the known-constructor case analyses fold while Lean is
turned into `Term`, and `Term.optimize` inlines and drops the dead `fn ()` of `rec2.e`), and the
sharing of `extern1`/`test4` in the `Term -[convert]-> JsTerm` phase (`shareConstValues`, as `Term`
has no global names).  The file has no loops or recursion, so labeled blocks and loops are not
involved; its generated JavaScript is unchanged by this work.

## What was missing: the results were not compared with Lean

Before this change the check modules of this file had **0 checks**: every result is a
`MyList Int`, a recursive datatype of the source, and the checks (`LeanScriptCli/Check.lean`)
only compared unions that are not recursive (`Option Int`).  The parameter type `Unit → MyList Int`
had no samples either, and a structure of one field holding a union (`RecA`) was refused.  Now:

* **Recursive unions are printed and compared** (`resultPrintable` accepts every sample type).
  In Lean, `showExpr` builds the printer as a chain of `let`-bound functions `f₀ … f_D`, each
  doing a `casesOn` and printing the recursive fields with the one before it (`treeCases`), so the
  expression stays linear in the depth and is compiled by `evalExpr` (a recursor would not be).
  In JavaScript, `showTree(v, rec, d)` (in the prelude of every check module) prints the same
  `i(…, …)`, told by `rec` which fields of each constructor are recursive.  Both cut the value at
  the depth `treeShowDepth` (32) with `…`, the same way, so a deeper value is still compared on
  its first 32 levels.
* **Lazy parameters answering a union** (`Unit → MyList Int`) get two samples, written
  `() => ({ tag: 0, … })` (in parentheses, as `() => { … }` would be a block).
* **A structure of one field holding a union** is unboxed like any other (`SType.wrap`), as the
  translation does (`extern2 = extern1`).

This file now has **13 checks per preset** (`test1`–`test3` on two lazy lists each, `fn_prime`,
`extern1`–`extern3`, `test4`–`test6`), all passing under node.  A deliberately broken
`test4` (`_1: 5`) makes `test4`, `test5` and `test6` fail, as expected.

## Testing

* `Tests/SnapshotsMy/RecursiveUnionChecks.lean` (new): `MyList.app`, `countdown`, a list of 40
  elements (`long`, deeper than the printing depth), `Tree.mirror`, `Tree.insert`, a structure of
  one field holding a tree (`wrapMirror`), a structure of two holding a list and a tree (`both`),
  and a lazy list parameter (`consForced`): 242 checks per preset, all pass under node.
* `inlineReferenceOpIsTagSpec` in `Tests/Main.lean`, on both presets: the expected lines of
  `InlineReferenceOpIsTag`, the absent ones (`if (`, ` ? `, `.tag`, `switch`, `fn_prime(`), the
  number of checks (13, and 242 for `RecursiveUnionChecks`) and the checks under node.
* All snapshots regenerated with the new checker (`scripts/leanscript-snapshots.sh`): no
  generated JavaScript changed; the check modules changed (the `showTree` function in their
  prelude, and new checks wherever a result is of a recursive datatype, e.g. `RecData`), and
  every check passes under node.
* `lake exe tests`: 130/130 pass.

## Notes

* `fn_prime` is a value, while a parameter of the same type `Unit → MyList Int` is a thunk:
  `test1(fn_prime)` would fail in JavaScript.  This is the project's convention for
  `Unit → τ` definitions (`cApplyTerm` in `JsTerm/Lower/FromTerm.lean`), not specific to this
  file; it is unchanged.
* Seen while writing `RecursiveUnionChecks`: structural recursion on a datatype of the source
  (`MyList.app`) is translated through Lean's `brecOn`: a helper building the table of the
  recursive results, which returns closures.  It is correct (the checks pass), but not a loop or
  labeled block; this file does not exercise it.
