# `KnownConstructors03`: our output compared with purescript-backend-optimizer

Files: `KnownConstructors03.lean` (the Lean port), `legacy-backend/KnownConstructors03.js`
(purescript-backend-optimizer), and our outputs `KnownConstructors03-pbo.js` /
`KnownConstructors03-faithful.js` (and `-Term-*.txt`). The variants are in
`Tests/SnapshotsMy/KnownCtorCaseOfIf.lean`. The checks are in `knownConstructors03Spec`
(`Tests/Main.lean`).

## `test`

```lean
def test (x : Int) : String :=
  let a := if x > 42 then some "Hello" else none
  match a with
  | some str => str ++ ", World!"
  | none => ""
```

purescript-backend-optimizer:

```js
const test = (x) => {
  if (x > 42) {
    return "Hello, World!";
  }
  return "";
};
```

Ours (`pbo`; `faithful` is the same with `42n`). This was already the output before this
work, and this work did not change it:

```js
export const test = (x) => (42 < x ? "Hello, World!" : "");
```

* The `Term` optimiser takes apart the `Option` chosen by the `if` (case of a conditional of
  constructor literals). Each arm is then a literal, so the string concatenation is folded.
* The two-arm `if` that returns from both arms is printed as one conditional expression. No
  record is built and no tag is tested.

## Variants (`Tests/SnapshotsMy/KnownCtorCaseOfIf.lean`)

Ideal outputs (`pbo`):

| Lean | JavaScript |
|------|------------|
| payload used twice (`twiceUse`) | `(x) => (42 < x ? "HelloHello" : "")` |
| payload a parameter (`payloadArg`) | `(x, s) => (42 < x ? s + ", World!" : "")` |
| `Except` chosen by a test (`exceptIf`) | `(x) => (0 < x ? int53__lean_int_mul(x, 2) : -1)` |
| `Bool` tested again (`boolTwice`) | `(x) => (42 < x ? "big" : "small")` |
| pair of options (`pairOpt`) | `(x) => (0 < x ? x : int53__lean_int_neg(x))` |
| `Bool × Int` pair (`pairBool`) | `(x) => (0 < x ? int53__lean_int_mul(x, 3) : -1)` |
| `isSome` (`isSomeIf`) | `(x) => 0 < x` |
| `if let` (`ifLet`) | `(x, s) => (0 < x ? s + "!" : "?")` |
| `Option` do-notation (`doChain`), `Except` do then `match` (`exceptChainGet`) | `if (0 < x && 0 < y) { return int53__lean_int_add(x, y); } return 0;` |
| private helpers (`viaSafeDiv`, `safeDivTwice`) | one `if (b === 0) return …;` per test, no record |
| three arms, two `some` (`threeArms`) | `if (42 < x) return s + …; return x < 0 ? t + … : "";` |

### What changed

**1. A large continuation shared by two `some` leaves** (`bigShared`):

```lean
def bigShared (x : Int) (s t : String) (f : String → String) : String :=
  let a := if x > 42 then some s else if x < 0 then some t else none
  match a with
  | some str => f (f (f (str ++ ", World!")))
  | none => ""
```

Before (an `Option` record was built and then tested):

```js
export const bigShared = (x, s, t, f) => {
  const s$1 =
    42 < x ? { tag: 1, _1: s } : x < 0 ? { tag: 1, _1: t } : { tag: 0 };
  if (s$1.tag === 0) {
    return "";
  }
  return f(f(f(s$1._1 + ", World!")));
};
```

Now (no record and no tag test, and the continuation is still written only once):

```js
export const bigShared = (x, s, t, f) => {
  let x$1;
  if (42 < x) {
    x$1 = s;
  } else if (x < 0) {
    x$1 = t;
  } else {
    return "";
  }
  return f(f(f(x$1 + ", World!")));
};
```

Copying the `some` arm into each leaf would add calls. In this case the optimiser instead makes
that arm a join point that takes the field. A leaf of the `some` constructor jumps to it with its
payload. Every other leaf is replaced by its own arm. A join point that is jumped to from several
places is printed as an assignment followed by the shared code, so there is no closure and no
recursion. The same rewrite improves `test4` of `KnownConstructors.lean`
(`let x$1; if (42 < x) x$1 = "Hello"; else x$1 = "Default"; return f(x$1 + …, x$1 + …);`).

**2. Earlier fixes from this work, all visible in the variants:**

* Elaboration of a nested conditional under a type ascription used to fail
  ("Expected type must not contain metavariables"). `threeArms` and `bigShared` did not
  translate before this fix (`LeanScript/TermElab/Anf/Render.lean`).
* Case of a *nested* conditional of constructor literals, `threeArms` (`Branches.caseOf?`).
* Case of a *record* built by a conditional of literals (`pairOpt`, `pairBool`), with the
  record never built (`Term.recordCaseOf?`, `Term.recordCaseCond`).
* A non-recursive `match` on a `Nat` is now an `n === 0` test and a predecessor. Before, it was a
  `nat_rec` loop that runs in O(n) (`fromMatch`; `TcoHyper` also improved).
* Jumps that pass a conditional of literals into the join point of a case. With these,
  `doChain` and `exceptChainGet` become one `&&` test (`JPos.jumpCond?`).
* An open closure that answers a literal, or that is called exactly once, is inlined at its
  call (`Term.letOpenCall`, `Term.openLetCall?`). `exceptChainGet`, `KnownConstructors05`,
  `Specialize01`, `AppArity`, `Html` and `ProfunctorLenses01` improved.
* Printer: a non-simple subject that is taken apart is bound once, so it is not recomputed for
  each field read (`JsTerm/Print/Mini/Block.lean`).

### Where it is done, and why there

Every optimisation above, except the printer fix, is in the `Term → Term` optimiser
(`LeanScript/Term/Optimize/…`). Each one comes with its proofs:

* `…_eval`: the result evaluates to the same value as the original.
* `numCalls_…`: the result makes no more calls than the original. The join-point rewrite is only
  applied when it adds no call.

The top-level theorems `LeanScript.Term.optimize_eval` and `LeanScript.Term.numCalls_optimize`
still build without `sorry`. They depend only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.

The printer fix has to be in the printer: whether a subject is "simple" (cheap to repeat)
can only be decided on the printed JavaScript expression.

### Not improved yet

* `usedTwice`: an option used by two different case analyses is still built as a record
  (rewriting it would copy code into both arms).
* `fromMatch` calls `uint53__lean_nat_pred(n)` where `n - 1` would do, since `n ≠ 0` is known at
  that point.
