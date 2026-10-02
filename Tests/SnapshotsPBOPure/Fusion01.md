# Fusion01: LeanScript output compared with purescript-backend-optimizer

`Fusion01.lean` builds a pipeline out of a Church-encoded fold (`Fold`, a structure with a rank-2
field), `mapF`/`filterMapF`/`filterF`, and the conversions `fromArray`/`toArray`, and applies it
to an array in `test`.

## `test`

The legacy backend's output (`legacy-backend/Fusion01.js`) keeps a lot of the structure:

* a specialised `Array.foldrMUnsafe.fold` loop that builds a cons **list**, which is then turned
  into an array with `$lean_array_mk`;
* the step function, re-created on every iteration as a closure (`const v8 = (v8, v9) => …`);
* `String.startsWith` expanded into `utf8_byte_size` and `memcmp`, and `drop` building two
  `String.Slice` records before calling `String_Slice_toString`;
* `Int` → `String` through `Nat_reprFast`, with a sign test.

LeanScript's output (`Fusion01-pbo.js`):

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

That is one `for … of` loop that pushes to the result array. There is no intermediate list, no
closures, no slice records and no recursion.

## Where each step happens

| step | phase |
| --- | --- |
| inlining the non-recursive helpers (`overArray`, `mapF`, …), `flip`/`∘`/`id`, and projections of `Fold.run` out of structure literals | elaboration to `Term` (`LeanScript/TermElab/ToTerm/Fusion.lean`) |
| `List.toArray (Array.foldr f [] xs)` with a step that only conses becomes `Array.foldl` pushing onto `#[]` | elaboration to `Term` (`fuseToArrayFoldr?`) |
| `String.startsWith` / `(s.drop n).toString` / `dropEnd` become `String.Internal.isPrefixOf` / `drop` / `dropRight` | elaboration to `Term` (`stringRewrite?`) |
| a `case` on an `if` whose arms are constructors becomes an `if` (`Option` from `dropPrefix1` and from `filterF`'s `if … then some a else none`) | `Term` optimiser (`Term.caseCondTop`, `Term.shareCase`); value preservation proved (`JoinCtorEval.lean`), never adds calls (`CountJoinCtor.lean`) |
| hoisting `lean_int_add(e, 1)` (calls with literal arguments count as calls on atoms) | `Term` optimiser (`HoistExpr.lean`) |
| dead bindings dropped before common-subexpression elimination and hoisting, so that dead code does not make a computation run on every path | `Term` optimiser (`Term.optimize`; `Term.optimize_eval` and `Term.numCalls_optimize` updated) |
| the loop body reads the accumulator variable directly, and an iteration that leaves the accumulator unchanged is just the end of the iteration (no `const a = acc; … acc = a;`) | conversion `Term` → `JsTerm` (`JsTerm/Lower/LoopAcc.lean`, `JsBlock.retToNext`) |

## Not translated

`mapF`, `filterMapF`, `filterF`, `fromArray`, `toArray` and `overArray` take or return a `Fold`.
`Fold` is a structure in `Type 1` with a field that is polymorphic in a type (`{r : Type} → …`),
and the `Term` language has no polymorphism over types, so these definitions are reported as
"not translated". They still work when they are used inside a first-order definition such as
`test`: there they are inlined and fused away.
