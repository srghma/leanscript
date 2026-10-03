# `InlineReferenceRecordUpdate`: ours vs purescript-backend-optimizer

Files: `InlineReferenceRecordUpdate.lean` (and the PureScript original `.purs`), the legacy output
`legacy-backend/InlineReferenceRecordUpdate.js`, ours `InlineReferenceRecordUpdate-pbo.js` /
`-faithful.js`, the `Term` dumps `-Term-unoptimized.txt` / `-Term-optimized.txt`.  Variants that
update an *unknown* record: `../SnapshotsMy/RecordUpdateKnownField.lean`.

## Legacy (purescript-backend-optimizer)

```js
const test1 = (fn) => fn({}).c;
const fn$p = (v) => ({ a: 1, b: 2, c: 3 });
const extern = { .../* #__PURE__ */ fn$p({}), a: 42 };
const test2 = /* #__PURE__ */ (() => extern.c)();
```

## Ours (preset `pbo`; `faithful` is the same with `1n`, `2n`, …)

```js
export const test1 = (fn) => fn()._3;
export const fn_prime = { _1: 1, _2: 2, _3: 3 };
export const extern1 = { _1: 42, _2: 2, _3: 3 };
export const test2 = 3;
```

## Comparison

| | legacy | ours |
|---|---|---|
| `test1`: `rec2.a == 42` after `rec2 := { rec1 with a := 42, … }` | decided, `fn({}).c` | decided, `fn()._3` |
| `test1`: the second call `fn ()` (for `b`) | dropped | dropped (dead) |
| `fn'` | a function `(v) => ({…})` (`inline never`) | the constant record (a `Unit → Rec` definition is a lazy value, read without a call) |
| `extern`: `{ fn' {} with a = 42 }` | spread of a call at load time | the record, computed |
| `test2` | an IIFE reading `extern.c` at load time | the constant `3` |

So ours was already on par for `test1` and better for `extern1`/`test2` before this change; this
file's output did not change.  (`test1` takes a function returning a record, which the check
generator does not sample, so its 3 node checks cover `fn_prime`, `extern1` and `test2`.)

## The variants (`RecordUpdateKnownField.lean`) and what changed

The original only updates records that are known at compile time.  The variants update an
unknown record `r`.  Final output (preset `pbo`):

```js
export const updKnown = (r) => r._3;                         // { r with a := 42 }.a == 42 decided
export const updOther = (r) => r._2;
export const updRet = (r) => ({ _1: 42, _2: r._2, _3: r._3 });
export const updChain = (r, x) => ({ _1: x, _2: int53__lean_int_add(x, 1), _3: r._3 });
export const updLazy = (fn, v) => {
  if (v === 42) {
    return int53__lean_int_add(v, 1);
  }
  return fn()._3;                                            // was: const x$1 = fn(); before the if
};
export const updAll = (r, x) => ({ _1: x, _2: x, _3: x });
export const updLoop = (r, a) => {
  let p$1 = r._1; let p$2 = r._2; let p$3 = r._3; let j$4 = a;
  while (true) {
    if (j$4 === 0) { return { _1: p$1, _2: p$2, _3: p$3 }; }
    j$4--;
    p$1 = int53__lean_int_add(p$1, 1);
    p$3 = int53__lean_int_mul(p$3, 2);                       // was also: p$2 = p$2;
  }
};
export const updCond = (r, b) => {
  const { _2: f$1 } = r;
  return b ? int53__lean_int_add(f$1, 1) : int53__lean_int_add(f$1, 2);
};                                                           // was: a record per arm, then x$1._1 + x$1._2
export const updSameBranches = (r, x) => ({ _1: 0, _2: r._2, _3: r._3 });
                                                             // was: x < 0 ? {…} : {…} (the same record)
```

The changes, by phase:

1. **`Term -[optimize]-> Term`, a computation moved into the arm that reads it**
   (`Term.sinkArm`, `LeanScript/Term/Optimize/SinkLet.lean`, run by `Term.sinkWalk`):
   `let x := c; if p then t else e`, where `p` and `e` do not read `x`, is
   `if p then (let x := c; t) else e` (and symmetrically), again inside the arm.  Proved:
   `Term.sinkArm_eval` (same value) and `Term.numCalls_sinkArm` (same number of calls written).
   This gives `updLazy`, and `RecordUpdate.lean`'s `test1` (the same shape).
2. **`Term -[optimize]-> Term`, record literals compared** (`PExpr.same`,
   `LeanScript/Term/Optimize/ShareTest.lean`): two record, union, array, list or `data` literals
   written the same way are now the same expression (before, only unknowns, literals of leaves,
   enum constructors and calls of externs were).  So `c ? ⟨0, f6, f7⟩ : ⟨0, f6, f7⟩` is
   `⟨0, f6, f7⟩` (`Neu.mkCondS`), and the other users of `PExpr.same` (shared and merged tests)
   see more.  Proved: `PExpr.same_eval`, `Elems.same_eval`.  This gives `updSameBranches`.
3. **`Term -[optimize]-> Term`, a join point taking a record apart, written at its jumps**
   (`Term.joinCtor`, `LeanScript/Term/Optimize/JoinCtor.lean`): `CaseJoin` now also covers
   `join j (x : σ) := let ⟨fs⟩ := x; b`, and a jump passing a record literal is `b` with the
   fields bound to the literal's (`Term.subst`), kept only when the join point disappears and no
   call is added (as for unions).  Proved: `Term.joinCtor_eval` (record case of
   `JPos.jump?_eval`, `Term.caseJoin?_eval`).  This gives `updCond`.
4. **`JsTerm -[optimize]-> JsTerm`, a test whose two arms are the same is dropped**
   (`JsBlock.mkIte` and `JsExpr.mergeIte`, `JsTerm/Lower/MergeIte.lean`): `if (c) { T } else { T }`
   is `T` and `c ? a : a` is `a`, when `c` has no effect (`JsExpr.noEffect`).  *Why not `Term`:*
   in the derived `Repr` instances each arm also takes the record parameter apart for nothing
   (`let ⟨_, _, _⟩ := x`); dropping that case analysis lowers the level index of the arm, which
   the `Term` syntax records in its type, so the arms are not the same `Term`.  The lowering
   writes nothing for it, so the arms are the same JavaScript.  This turns the
   `if (f$1 < 0) { x$4 = A; } else { x$4 = A; }` of every derived `Repr` of a structure with an
   `Int` field into `const x$1 = A;` (`RecordUpdate`, `CaseGuarded`, `KnownConstructor07`,
   `ProfunctorLenses01`).
5. **`MiniJs` printer, `x = x;` dropped** (`JsTerm/Print/Mini/Block.lean`): a loop that keeps a
   record accumulator in one variable per field, passing a field on unchanged, assigned the
   variable a constant holding its own value; written at its use, that was `p$2 = p$2;`.

No change was needed in the `Term -[convert]-> JsTerm` phase.  The only loop here (`updLoop`) is
already a labeled `while (true)` loop with a counter (`countdown`), with no recursion.

## Tests

* `inlineReferenceRecordUpdateSpec` in `Tests/Main.lean` (`lake exe tests`): the fragments above at
  both presets, the absence of the old shapes, and the node checks (3 for the original, 93 for the
  variants, per preset).
* All snapshots regenerated; every node check passes.  Outputs that changed: `RecordUpdate`,
  `CaseGuarded`, `KnownConstructor07`, `ProfunctorLenses01` (all smaller, see 1 and 4).
