# `InlineReferenceOpArrayLength`: ours vs purescript-backend-optimizer

Files: `InlineReferenceOpArrayLength.lean`, the legacy output
`legacy-backend/InlineReferenceOpArrayLength.js`, ours `InlineReferenceOpArrayLength-pbo.js` /
`-faithful.js` (and the `Term` dumps `-Term-unoptimized.txt` / `-Term-optimized.txt`).

## Legacy (purescript-backend-optimizer)

```js
const test1 = (fn) => [1, 2, fn(undefined)];
const test2 = (fn) => [[1, 2, fn(undefined)], [3, 4], [fn(undefined)]];
const fn$p = (v) => 0;
const extern1 = [1, 2, /* #__PURE__ */ fn$p(undefined)];
const extern2 = [extern1, [3], [/* #__PURE__ */ fn$p(undefined)]];
const test3 = extern1;
const test4 = extern2;
```

## Ours (preset `pbo`; `faithful` is the same with `1n`, `2n`, …)

```js
export const test1 = (fn) => [1, 2, fn()];
export const test2 = (fn) => {
  const x$1 = fn();
  return [[1, 2, x$1], [3, 4], [x$1]];
};
export const fn_x27 = 0;
export const extern1 = [1, 2, 0];
export const extern2 = [extern1, [3], [0]];
export const test3 = extern1;
export const test4 = extern2;
```

## Comparison

| | legacy | ours |
|---|---|---|
| `test1`, `test2`: test of the size of a known array | decided | decided (`Term -[optimize]-> Term`: `lean_array_get_size` of a literal, then the `if`) |
| `test2`: `array2[0]?.map size == some 3` | decided | decided (the `Option` case, the join points and the comparison all fold) |
| `test2`: calls of `fn` | two calls of `fn(undefined)` | one call, shared (`x$1`): Lean is pure, `fn ()` twice is the same value |
| `fn'` | a function `(v) => 0` | the constant `0` (a `Unit → Int` definition is a lazy value, read without a call) |
| `extern1`, `extern2`: calls of `fn'` | kept, marked `#__PURE__` (`inline never`) | computed (`0`) |
| `extern2` | `[extern1, [3], […]]` | `[extern1, [3], [0]]` |
| `test3`, `test4` | `extern1`, `extern2` | `extern1`, `extern2` |

So ours is on par on every definition and better on `test2` (one call instead of two) and on
`extern1`/`extern2` (no call at load time).

## What changed

Before this change, `extern2`, `test3` and `test4` repeated the values of the constants before
them (`extern2 = [[1, 2, 0], [3], [0]]`, `test3 = [1, 2, 0]`, `test4 = [[1, 2, 0], [3], [0]]`).

* **`shareConstValues`** (`JsTerm/Lower/ShareConsts.lean`, the `Term -[convert]-> JsTerm` phase,
  run on the functions of a module next to `aliasFuns`): in the value of each constant, each
  part built of arrays, lists, records and constructors that is written exactly as the whole value of
  an earlier constant is read as that constant, by its name, outermost first.  Empty arrays and
  constructors without fields are not shared (they are as short as a name).  Only the values
  of constants are rewritten: a function's body returns a fresh array, which a caller owning
  it may update in place, so `fresh n = #[1, 2, 3].push n` keeps its literal.
  *Why not `Term`:* `Term` has no global names (a definition reading another one has it inlined),
  so it cannot say "the value of `extern1`".
  *Why it is safe:* a constant's value is shared by every reader and never updated in place
  (`JsFun.isConst`), and the constant read comes before, so it has been computed already.
* **Checks of arrays of arrays** (`LeanScriptCli/Check.lean`): `Array (Array Nat/Int/Bool/String)` is
  now a sample type, so `test2`, `extern2` and `test4` are compared with Lean too (9 checks per
  preset instead of 5, all pass under node).

* **The tests of the size are decided in `Term`** by the pass `Term.knownSizes`
  (`LeanScript/Term/Optimize/KnownSize.lean`, part of `Term.optimize`, proved not to change
  `eval` nor to add calls): the size of an array literal is known, so
  `lean_array_get_size(#[1, 2, x3]) == 3` is `true`, and `array2[0]?` of a literal is the
  `some` of its first element, whose size is known too.
* **Speed fix found on the way** (`LeanScript/Term/FinMemo.lean`, `Fin.optAllMemo` in
  `LeanScript/Term/Rename/Basic.lean`).  Regenerating all snapshots, the optimiser did not
  finish on `BranchSpecialization01.lean` (a derived `BEq` on an enum of four constructors:
  nested case analyses of enums).  The renamings and substitutions that every pass uses
  (`Term.rename`, `Term.relvl`, `Term.subst`, through `Fin.optAll`) computed each branch of an
  enum's case analysis once to check that all succeed, then again each time the branch was read
  — exponential in the nesting.  `Fin.optAllMemo` computes each branch once into an array; it is
  equal to `Fin.optAll` (`Fin.optAll_eq_optAllMemo`, `@[csimp]`), so only the compiled code
  changes and no proof does.  The file now takes about 2 s (before: over 10 minutes);
  `nestedEnumCasesSpec` in `Tests/Main.lean` checks it.  Three examples of
  `Tests/TermTests/Optimize/OptimizeTest.lean` that check `t.optimize = t'` by `rfl` hit the
  elaborator's heartbeat limit since `Term.knownSizes` was added; they use `kernel_rfl` now, as
  `copy.optimize = copyOpt` already did.

The file has no loops or recursion, so labeled blocks and loops are not involved.

## Testing

* `Tests/SnapshotsMy/ShareConstValues.lean`: whole values, parts in arrays, records and
  `Option`, a constant equal to an earlier one that itself reads another (`nested2 = nested`),
  empty arrays (not shared), `Array UInt8` (shared at `pbo`, where it is written `[1, 2, 3]`, not
  at `faithful`, where it is `Uint8Array.of(1, 2, 3)`), and functions (not rewritten).  17
  checks per preset, all pass under node.
* `inlineReferenceOpArrayLengthSpec` in `Tests/Main.lean`, on both presets: the expected lines,
  the absent ones, the number of checks, and the checks under node.
* All snapshots regenerated: every check passes under node.  Other outputs that changed:
  constants equal to an earlier constant now read it (`TestUInt16$test3 = TestUInt8$test3` in
  `PrimOpInt02NonConfigurable`), and a few outputs of earlier optimiser changes that had not been
  regenerated (`KnownConstructors` `test2`–`test5`, now translated; calls written in place in
  `PrimOpBoolean02`, `UnpackArray01`, …).
* `lake exe tests`: 129/129 pass.
