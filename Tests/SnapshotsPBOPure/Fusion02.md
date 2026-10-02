# Fusion02: LeanScript output compared with purescript-backend-optimizer

`Fusion02.lean` builds a pipeline from an *unfold* stream. `Unfold α` is a structure with an
existential state type `State`, a `seed`, a `step : State → Option (State × α)` and a
termination measure. The file defines:

* the transformers `mapU`, `filterMapU` and `filterU`;
* `filterMapStep`, by well-founded recursion, which skips the elements that `f` drops;
* the conversions `fromArray`, and `toArray`, which goes through `toArrayLoop` (also by
  well-founded recursion);
* `test`, which runs the pipeline on an array.

## Before

Only `dropPrefix1` was translated. `test` failed with "the parameter `α` of `overArray` is a
type". Once the helpers are inlined, the body is `toArrayLoop U U.seed #[]`, and that cannot be
translated: `toArrayLoop` is defined by well-founded recursion, and the language has no
unbounded fixpoint. Its argument `U` is also an `Unfold`, a structure with a field that is a
type.

## The legacy backend (`legacy-backend/Fusion02.js`)

The legacy backend translates every definition, because JavaScript is untyped. `test` then
keeps the whole structure at run time:

* it builds a chain of `{ tag: 0, _1: seed, _2: step, _3: measure }` records, each `step` a
  closure that calls the step of the inner record;
* `filterMapStep` is called through these closures, and it runs a `while (true)` loop of its
  own;
* `toArrayLoop` runs the outer `while (true)` loop. Each element allocates an
  `Option`/`Prod` record at every stage, and each push copies the array (`[...v5, v7._2]`), so
  building the result takes quadratic time;
* `startsWith`/`drop` expand to `memcmp` and `String.Slice` records, and `Int` → `String`
  goes through `Nat_reprFast`.

## LeanScript's output now (`Fusion02-pbo.js`)

```js
export const test = (arr) => {
  let acc$1 = [];
  for (const e$2 of arr) {
    const x$3 = String(int53__lean_int_add(e$2, 1));
    if (string__lean_string_isprefixof("1", x$3)) {
      const x$4 = "2" + uint53__lean_string_drop(x$3, 1);
      if (x$4 !== "wat") {
        acc$1 = array__lean_array_push_mutable(acc$1, x$4 + "1");
      }
    }
  }
  return acc$1;
};
```

This is one `for … of` loop that pushes onto the result in place. It allocates no stream
records, `Option` or `Prod` values, or closures, and it does not recurse, so the stack cannot
overflow. It is the same code as `Fusion01`'s `test`, which goes through the Church-encoded
fold instead. Node checks: 8/8 pass on both presets.

## Where each step happens

| step | phase |
| --- | --- |
| inlining `overArray`, `toArray`, `mapU`, `filterMapU`, `filterU`, `fromArray` and `flip` (`headNorm`) | elaboration to `Term` (existing, `LeanScript/TermElab/ToTerm/Fusion.lean`) |
| **new:** `toArrayLoop U s acc` becomes `Array.foldl K acc arr s`. The rewrite reads the unfolding equations (`g.eq_def`) of the definitions by well-founded recursion and recognises their *shape*, not their names: a drain (`none ↦ acc`, `some (s', a) ↦ self s' (G a acc)`), transformers (`none ↦ none`, `some (s', a) ↦` a tree of `if`/`match` whose leaves emit `some (s', b)` or skip to the self call at `s'`), and an array source (`if h : s < arr.size then some (s + 1, arr[s]) else none`). The consumer `K` is composed from the drain down to the source. | elaboration to `Term` (`LeanScript/TermElab/ToTerm/StreamFusion.lean`, called from `trApp` in `Expr.lean`) |
| `startsWith`/`drop` become the `String.Internal` primitives | elaboration to `Term` (existing `stringRewrite?`) |
| a `case` on an `if` whose arms are constructors (the `Option` from `dropPrefix1` and from `filterU`'s `if … then some a else none`) becomes an `if`; `lean_int_add(e, 1)` is hoisted; dead bindings are dropped | `Term` optimiser (existing, with proofs that it preserves the value) |
| `Array.foldl` with an owned accumulator becomes a `for … of` loop with an in-place push | conversion `Term` → `JsTerm` (existing) |

All of the new work is in the earliest phase, elaboration to `Term`. The `Term` optimiser and
the later phases needed no changes.

## Not translated

These are reported in the header of the `.js` files:

* `fromArray`, `toArray`, `mapU`, `filterMapU`, `filterU` and `overArray` take or return an
  `Unfold`. Its `State` field is a type, which the typed `Term` language cannot represent.
* `toArrayLoop` and `filterMapStep` are polymorphic and defined by well-founded recursion over
  an `Unfold`.

Inside a first-order definition such as `test`, all of them are inlined and fused away.
