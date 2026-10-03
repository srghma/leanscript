# `KnownConstructors01`: our output compared with purescript-backend-optimizer

Files: `KnownConstructors01.lean` (the Lean port), `KnownConstructors01.purs` (the original),
`KnownConstructors01.js` (purescript-backend-optimizer), and our outputs
`KnownConstructors01-pbo.js` / `KnownConstructors01-faithful.js` (and `-Term-optimized.txt`).
The variants are in `Tests/SnapshotsMy/KnownCtorOption.lean`.

## `test1`

```lean
def test1 : String :=
  (some "c").map (fun _ => "b") |>.getD "a"
```

purescript-backend-optimizer:

```js
const test1 = "b";
```

Ours, at both presets:

```js
export const test1 = "b";
```

This was already on par before this change. Lean's own compiler folds the known constructor before
leanscript reads the code, so even the unoptimised `Term` is `ret "b"`. No `Option` is built and no
function is called.

## Variants: a known constructor whose payload or function is unknown

These were already at the best possible output, at both presets:

| Lean | JavaScript |
|------|------------|
| `(some x).map (fun _ => "b") \|>.getD "a"` | `(x) => "b"` |
| `(some "c").map f \|>.getD "a"` | `(f) => f("c")` |
| `(some x).map f \|>.getD "a"` | `(f, x) => f(x)` |
| `(none).map f \|>.getD "a"` | `(f) => "a"` |
| `((some x).map f \|>.map g).getD "a"` | `(f, g, x) => g(f(x))` |
| `match (Except.ok x).map f with …` | `(f, x) => f(x)` |
| `(if b then some x else none).map f \|>.getD "a"` | `if (b) { return f(x); } return "a";` |
| `((wrap x).map (· * 2)).getD 7` (private `wrap` inlined) | `(10 < x ? uint53__lean_nat_mul(x, 2) : 7)` (preset `pbo`) |

`bindKnown` (`((some x).bind f).getD "a"`) keeps one test on `f(x)`, because the result of `f` is not
known.

## What changed: loop states that are always `yield`

In a `for` loop the state is a `ForInStep` (`yield s` / `done s`). When the body always ends in
`yield`, that constructor is a known constructor in exactly the sense of this test. It was still
built, tested, and taken apart on every iteration:

Before (`loopOpt`, and `ScalarRepl.test1`):

```js
let acc$1 = { tag: 1, _1: 0 };
for (let i$2 = 0; i$2 < n; i$2++) {
  if (acc$1.tag === 1) {
    const { _1: f$3 } = acc$1;
    acc$1 = { tag: 1, _1: uint53__lean_nat_add(f$3, i$2) };
  }
}
return acc$1._1;
```

Now:

```js
let acc$1 = 0;
for (let i$2 = 0; i$2 < n; i$2++) {
  acc$1 = uint53__lean_nat_add(acc$1, i$2);
}
return acc$1;
```

This is a plain JavaScript `for` loop, so it cannot overflow the stack. Nested loops (`loopNested`)
lose both boxes. Two mutable variables (`loopPair`) keep only their record, and the final
`let ⟨a, b⟩ := acc; ret ⟨a, b⟩` is reduced to `return acc$1;`. A loop with `break` (`loopBreak`)
does take the `done` branch, so its box is kept, and the test is merged into the loop's condition:
`if (acc$1.tag === 1 && k < i$2)`.

### Where it is done

The rewrite is in the `Term → Term` optimiser, in the new pass `Term.loopYield`
(`LeanScript/Term/Optimize/LoopYield.lean`). For

```
let x := nat_rec n (C a) step; rest
```

where every return of `step` is the constructor `C` (after its `case` on the state is resolved),
it produces

```
let y := nat_rec n a step'; rest[x := C y]
```

where `step'` takes and returns the payload. The pass also contains `Term.recordEta`, which turns
`let ⟨a, b⟩ := x; ret ⟨a, b⟩` into `ret x`. The rewrite is kept only when it does not increase the
number of calls.

Proofs, with no `sorry`:

* `Term.loopYield_eval` (`LoopYieldEval.lean`): `Term.eval` of the result is the same as `Term.eval`
  of the input. It is part of `Term.optimize_eval`, so the whole optimiser still provably preserves
  `eval`.
* `Term.numCalls_loopYield` (`CountLoopYield.lean`): the pass does not increase the number of calls.
  It is part of `Term.numCalls_optimize`.

The full snapshot run changed about 10 files in `Tests/SnapshotsMy` (`ScalarRepl`, `ArrayInPlace`,
`CaseGuardedSweep`, `StringWalk`, `LoopClosure`, …). Every change made the output smaller, and all
their `--check` tests still pass.

### Not done

`LoopState.minMaxSum` is not improved. Its body's join points are compiled to closures
(`k$11 = () => (x) => …`), so its returns are not visibly `yield`, and the nested record there is not
reduced by `recordEta`. This pattern only occurs in that one file.

## Test

`knownConstructors01Spec` in `Tests/Main.lean` runs leanscript on both files, checks the fragments
above at both presets, checks that no tag or closure is left in `test1`, and runs the generated
checks with `node` (1 for `KnownConstructors01`, 113 for `KnownCtorOption`).
