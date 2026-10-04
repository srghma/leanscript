# `KnownConstructors05`: our output compared with purescript-backend-optimizer

Files: `KnownConstructors05.lean` (the Lean port), `legacy-backend/KnownConstructors05.js`
(purescript-backend-optimizer), and our outputs `KnownConstructors05-pbo.js` /
`KnownConstructors05-faithful.js` (and `-Term-*.txt`). The variants are in
`Tests/SnapshotsMy/KnownCtorEnumParse.lean`. The checks are in `knownConstructors05Spec`
(`Tests/Main.lean`).

`fromString` turns a string into `Option Test` (`Test` is an enum with four constructors), and
`test` does a `match` on `fromString a`.

## The file itself: already on par

`fromString` is inlined into `test` and each case of the `match` is reduced at the constructor
that is known there. No record is built and no tag is tested:

```js
export const test = (a) => {
  if (a === "foo") {
    return 1;
  }
  if (a === "bar") {
    return 2;
  }
  if (a === "baz") {
    return 3;
  }
  return a === "qux" ? 4 : 0;
};
```

Legacy writes the same chain of `if`s; the only difference is that we write the last test as a
conditional expression. Enum constructors are numbers (`{ tag: 1, _1: 0 }`), where legacy
builds string-tagged constants (`$Test("Foo")`). With `faithful`, `int` is `bigint`, so the
literals are `1n`…. This snapshot did not change.

## What the variants found, and what was fixed

The variants (`Tests/SnapshotsMy/KnownCtorEnumParse.lean`: `wildcard`, `sharedArm`, `armsCall`,
`thenMore`, `mapGetD`, `getDEnum`, `isColor`, `two`, `describe`, `sumCodes`, `firstBad`,
`natSwitch`) found three problems:

1. **Elaboration failure (fixed, in `Term`).** A case analysis on an enum with at least three
   constructors, inside a body whose arms call outer variables (`| .Foo => f 1 | .Bar => f 2 …`),
   failed with "omega could not prove the goal" while solving a usage-level side condition. The
   `ls_lvl` tactic (`LeanScript/Term/Build.lean`) now has a last alternative that unfolds the
   level computation (`Lvl.meetFin`, `List.getD`, …) and uses `decide`.
2. **Elaboration failure (fixed, in `Term`).** The same kind of case analysis failed with
   "expected type must not contain metavariables" because the expected type did not reach the
   branches that contain closures. The new `Branch.enumListAt` fixes the level by an equation
   (`h : … = m`), and the elaborator (`LeanScript/TermElab/Anf.lean`) now produces it.
   These two fixes also let `TagChain.test1` and `PrimOpBooleanNotRegression.test` translate.
3. **A loop that keeps testing its state (improved, in `JsTerm`).** In a `for` over a range
   whose state becomes final at some iteration (`firstBad`; also `firstAbove`/`loopBreak` in
   `LoopState.lean`/`KnownCtorOption.lean`), every iteration tested the state's tag. It is now a
   labelled loop that is left with `break`:

   ```js
   // before
   for (let i$2 = 0; i$2 < n; i$2++) {
     if (acc$1.tag === 1 && k < uint53__lean_nat_mul(i$2, i$2)) {
       acc$1 = { tag: 0, _1: i$2 };
     }
   }
   // now
   j$1: for (let i$2 = 0; i$2 < n; i$2++) {
     if (k < uint53__lean_nat_mul(i$2, i$2)) {
       acc$1 = { tag: 0, _1: i$2 };
       break j$1;
     }
   }
   ```

## Where the loop change lives, and why

The pattern only shows up after loops are lowered to mutable JavaScript state (`for` with an
accumulator variable), and `Term` has no such loop form, so the change cannot be made in
`Term → Term` or in the conversion. It is a `JsTerm → JsTerm` pass: `JsTerm/Lower/LoopExit.lean`,
run from `JsTerm/Print/Share.lean`. It uses a new block form `JsBlock.forExit` (a loop with an
exit continuation, `JsTerm/Syntax/Basic.lean`). The printer writes it as a labelled loop
`L: for (…)`, or as `let x; L: { for (…) …; … }` (a labelled block) when code follows the loop,
so no recursion or extra stack is used. The pass:

* turns an assignment that makes the state final (a value on which the loop body does nothing)
  into the assignment followed by a jump to the exit;
* removes the test of the state at the top of the body, since every path that reaches a final
  state now leaves the loop;
* fills arms for states that cannot occur any more.

## Status

* Not proved: the `JsTerm` passes, including this one, have no correctness proofs. They are
  checked by the node checks generated from Lean evaluation: 5 per preset for this file, 87 for
  `KnownCtorEnumParse`, 41 for `LoopState`, 113 for `KnownCtorOption`, and 0 failures over the
  whole snapshot run.
* The `Term` proofs (including that the optimiser preserves `eval`) are not affected.
* Not done: at a `break`, the code after the loop could be specialised to the state just
  written. For example, `firstBad` could `return i$2` directly and never build
  `{ tag: 0, _1: i$2 }`. Legacy has no such loops (PureScript uses recursion), so this would go
  beyond legacy rather than catch up with it.
