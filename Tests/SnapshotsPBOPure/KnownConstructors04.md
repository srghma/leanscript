# `KnownConstructors04`: our output compared with purescript-backend-optimizer

Files: `KnownConstructors04.lean` (the Lean port), `legacy-backend/KnownConstructors04.js`
(purescript-backend-optimizer), and our outputs `KnownConstructors04-pbo.js` /
`KnownConstructors04-faithful.js` (and `-Term-*.txt`). The variants are in
`Tests/SnapshotsMy/KnownCtorShared.lean`. The checks are in `knownConstructors04Spec`
(`Tests/Main.lean`).

All three functions name an `Option` chosen by a test (`let a := if x > 42 then some … else none`)
and take it apart **twice** with `get!`.

**Semantics.** PureScript's `fromJust Nothing` is undefined behaviour, so the legacy backend
treats the `Nothing` branch as unreachable and throws. Lean's `none.get!` panics (a message on
stderr) and then *returns the default value* (`""`, `false`), and the program carries on. Our
output keeps Lean's result in that branch, so it does not throw. It is checked against Lean by
the generated node checks (14 per preset).

## Before and after

Before this work, each function built the option as a record `{ tag: 1, _1: "Hello" }` /
`{ tag: 0 }` and tested its tag once per `get!` (`let x$2; if (x$1.tag === 0) … else x$2 = x$1._1;`
twice). The `Term` optimiser could only take apart a conditional of constructors used **once**.

Now (`pbo`; `faithful` is the same with `42n`):

```js
export const test1 = (x) =>
  42 < x ? ["Hello, World", "Hello, Universe"] : [", World", ", Universe"];

export const test2 = (f, x) => {
  const x$1 = 42 < x;
  return f(
    x$1 ? "Hello, World" : ", World",
    x$1 ? "Hello, Universe" : ", Universe",
  );
};

export const test3 = (x) => false;
```

purescript-backend-optimizer:

```js
const test1 = (x) => {
  if (x > 42) {
    return ["Hello, World", "Hello, Universe"];
  }
  throw new Error("UNREACHABLE");
};
const test2 = (f, x) => {
  if (x > 42) {
    return f("Hello, World")("Hello, Universe");
  }
  throw new Error("UNREACHABLE");
};
const test3 = (x) => {
  if (x > 42) {
    return false;
  }
  throw new Error("UNREACHABLE");
};
```

* `test1`: the same work as the legacy output: one comparison, one constant array.
* `test2`: one comparison (shared in `x$1`), one call of `f` with both arguments, no record.
  Writing `x > 42 ? f(…, …) : f(…, …)` would copy the call of `f`; the optimiser is proved never
  to add calls (`Term.numCalls_optimize`), so the choice is made in the arguments.
* `test3`: `a.get! && !a.get!` is `false` on both paths (`true && !true`, and `false && …`), so the
  function is the constant `false`, with no test at all.

## What changed (all in the `Term → Term` optimiser)

1. **`Term.condJump`** (new, `LeanScript/Term/Optimize/CondJump.lean`), run before and after
   `Term.joinCtor`:
   * `Term.shareSubst`: `let x := share (c ? a : b); body`, where `x` is used once, or only as
     the operand of union case analyses (`Term.onlyScrut`), is `body[x := c ? a : b]`. Each
     `case x of …` becomes a case of a conditional of constructors, which `Branch.caseCond`
     (already there) turns into `if c then (arm of a) else (arm of b)`.
   * `Term.condJumps`: `if c then jump j a else jump j b` is `jump j (c ? a : b)`.
   * `Branch.joinJump`: `join j x := body; jump j a` is `body[x := a]` (or
     `let x := share a; body`), and a jump further out drops the join point.
2. **`LeanScript/Term/Optimize/CondFold.lean`** (new), applied by `Term.arithWalk`:
   * `Neu.condFold`: an extern call whose operands are constants and conditionals of constants
     on one condition is a conditional of two folded literals:
     `(c ? "Hello" : "") ++ ", World"` is `c ? "Hello, World" : ", World"`.
   * `PExpr.liftCond`: an array, list, record or union literal with **two or more** conditional
     operands on one condition, the rest constants, is one conditional of two literals (`test1`).
     It is not done with a single conditional operand, because that would only copy the literal
     (it made `KnownConstructors06` worse, so it was restricted).
3. **Hoisting** (`Term.hoistWalk`, `Hoist.lean`) now also looks into the operands of calls, so the
   comparison `42 < x` repeated in the two arguments of `f` in `test2` is computed once.

**Proofs.** `Term.condJump_eval`, `PExpr.liftCond_eval`, `Neu.condFold_eval` (the value does not
change) and `Term.numCalls_condJump` (no call is added) are proved, and are part of
`Term.optimize_eval` and `Term.numCalls_optimize`, which depend only on `propext`,
`Classical.choice` and `Quot.sound`. The hoisting proofs were extended to the new case.

Nothing was needed in `Term → JsTerm` or `JsTerm → JsTerm`. This file has no loops or recursion,
so labeled blocks and loops do not come into it; no join point is printed as a closure.

## Variants (`Tests/SnapshotsMy/KnownCtorShared.lean`, 85 checks per preset)

* `twoDefaults`: `const x$1 = 42 < x; return [(x$1 ? s : "none") + "!", x$1 ? s : "?"];`
* `threeUses`: `42 < x ? ["Hello1", "Hello2", "Hello3"] : ["1", "2", "3"]`
* `nestedChoice` (two tests choosing the constructor): no record, nested conditionals.
* `exceptTwice` (`Except`, taken apart twice):
  `return (x$1 ? String(x) : "neg") + int53__lean_int_add(x$1 ? x : 0, 1);`
* `boolTwice`: `a.get! || !(a.getD false)` is `true` on both paths, so `(x) => true`.
* `underTests`: each use under another test; no record.
* `alsoReturned`: the option is also part of the result, so it is still built (once), and the
  `getD` still tests its tag. This is the only `.tag` test left in the file.
* `twoMatchCalls`: no record, but the two `match`es remain two `if (x$1)` statements. Merging
  them would copy the code after the first `match` into both arms of the test.

## Other snapshots that changed

* `KnownCtorCaseOfIf.usedTwice` (the gap noted in `KnownConstructors03.md`): the option used by two
  `match`es is no longer built: `const x$1 = 0 < x; return int53__lean_int_add(x$1 ? x : 0, x$1 ?
  int53__lean_int_mul(x, 2) : 1);`.
* `KnownConstructors.test4`: `const x$1 = 42 < x ? "Hello" : "Default";` instead of a `let` with
  an `if`.
* `CaseGuardedSweep.sweep1`: the per-iteration temporary is gone; the conditional is written in
  the accumulator's update (still a `for` loop).
* `CaseLeafTco`, `OwnershipAliasing`, `ScalarRepl`: only the `Term` text changed (a shared
  conditional used once is written at its use); their JavaScript is the same.

Every node check in `scripts/leanscript-snapshots.sh` reports 0 failed. The script still exits 1
because of the existing `literal too big` errors for `UInt64` literals in the `pbo` preset of
`PrimOpInt02Configurable`/`PrimOpInt03Configurable`; their outputs did not change.
