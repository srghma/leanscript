# `PrimOpBooleanNotRegression`: ours vs purescript-backend-optimizer

Files: `PrimOpBooleanNotRegression.lean`, the legacy output
`legacy-backend/PrimOpBooleanNotRegression.js`, ours `PrimOpBooleanNotRegression-pbo.js` /
`-faithful.js`, the `Term` dumps `-Term-unoptimized.txt` / `-Term-optimized.txt`, and the checks
`-pbo.check.mjs` / `-faithful.check.mjs`.

```lean
def test {α : Type} (comp : α → α → Ordering) (a b : α) : Bool :=
  comp a b != Ordering.eq
```

## The function

| | |
|---|---|
| legacy | `const test = (comp) => (a) => (b) => { return comp(a)(b) !== "eq"; };` |
| ours (both presets) | `export const test = (comp, a, b) => comp(a, b) !== 0;` |

Ours already matched or beat the legacy output before this change, and the output is unchanged:

* one call with two arguments, not two curried calls (`comp(a)(b)`);
* one comparison with a number (`Ordering` numbers from `-1`: `lt = -1`, `eq = 0`, `gt = 1`),
  not with a string (`"eq"`);
* an arrow with an expression body, not a block with `return`.

### How it gets there

Lean compiles `!=` on `Ordering` (its derived `BEq`) as `!(Nat.decEq (toCtorIdx x) 1)`.
`toCtorIdx` becomes a join point fed by a case analysis over every constructor
(`-Term-optimized.txt`):

```
join j9 (x10 : Nat) := ret cond(lean_nat_dec_eq__Nat_decEq(x10, 1), false, true)
case x8 of | enum#0 => jump j9 0 | enum#1 => jump j9 1 | enum#2 => jump j9 2
```

`Term` has no operation that turns an enum into a `Nat`, so this `Term` is as small as `Term`
can make it. The conversion (`Term → JsTerm`) recognises the `toCtorIdx` shape
(`isCtorIdxCases`) and reads the position from the value itself (`JsExpr.enumIndex`). It then
turns `Nat.decEq` of that position and a literal into `===` on the enum (`enumIndexEq?`). The
`Term` optimiser had already applied `comp` once with both arguments (`x7 := x2 x4; x8 := x7 x6`).

The file has no loops or recursion, so labelled blocks and loops are not involved.

## Its neighbours (`Tests/SnapshotsMy/OrderingCmp.lean`)

Small variations of this file gave much worse JavaScript before this change. Each one below is
now handled, in the phase you prefer most where possible:

| Lean | before | now |
|---|---|---|
| `compare a b == .lt` (`Nat`, `Int`) | `(a < b ? -1 : a === b ? 0 : 1) === -1` | `a < b` |
| `compare a b != .eq` (`Nat`, `Int`) | `(a < b ? -1 : a === b ? 0 : 1) !== 0` | `a < b \|\| a !== b` |
| `(comp a b).isLE` | `const x$1 = comp(a, b); return x$1 !== 1;` | `comp(a, b) !== 1` |
| `a != b` on an enum (derived `BEq`) | `const x$1 = a === b; return !x$1;` | `a !== b` |

**`Term → Term` (optimiser, proved to preserve `Term.eval`):**

* `Branch.enumCaseCond` (`LeanScript/Term/Optimize/JoinCtor.lean`): a case analysis on an enum
  whose subject is a conditional of constructor literals (`compare` inlined:
  `cond(a < b, enum#0, cond(a == b, enum#1, enum#2))`) becomes `if`s on the conditions, each
  leading to the arm of its constructor. This is kept only when no call is added. It is the enum
  counterpart of the existing `Branch.caseCond` for unions. Proved by `Branch.enumCaseCond_eval`
  and `Branch.numCalls_enumCaseCond`.
* `Neu.condFoldDeep?` (`LeanScript/Term/Optimize/CondFold.lean`): an extern call whose
  arguments are constants and *nested* conditionals of constants, on several conditions, is a
  tree of conditionals with the calls folded at its leaves:
  `decEq(cond(lt, 0, cond(eq, 1, 2)), 1)` is `cond(lt, false, cond(eq, true, false))`.
  Before, only one level on one condition was folded. Proved by `Neu.condFoldDeep?_eval`.
* `Neu.condOfCond?` (`LeanScript/Term/Optimize/Cond.lean`): the negation of a conditional with
  a literal arm is pushed into its arms: `!(p ? false : q)` is `p ? true : !q`. It is not done
  when the condition and an arm are both variables, because the conversion writes those as a
  boolean comparison (`!(a < b)` on `Bool` stays `a >= b`). Proved by `Neu.condOfCond?_eval`.

**`Term → JsTerm` (conversion, `JsTerm/Lower/FromTerm.lean`):** these two can't be done in
`Term`, which has no comparison of enums.

* An enum case analysis whose arms all answer Boolean literals, one of them differently from
  all the others, is one comparison `e === k` (or `e !== k`), the subject computed once
  (`enumBoolArm?`).
* A join point whose block only jumps to it with a value is written as a constant
  (`JsBlock.joinOrConst`). The printer can then write the value at its only use.

Not done (yet): `compare a b != .eq` on `Nat` could be `a !== b`, and `(compare a b).isLE` could
be `a <= b`. Both need the fact that `a < b` implies `a !== b` about the externs, which no `Term`
rewrite knows. `compare` of a user enum with derived `Ord` (`compare a b != .eq`) still builds
the `Ordering`: the case analysis there goes through the `toCtorIdx` join points, which only the
conversion recognises.

## Checks

Checks of a function that returns or takes an `Ordering` used the constructor position (`0, 1,
2`) as the expected value. JavaScript holds `-1, 0, 1`, so every such check failed. They now use
the same numbering as the JavaScript (`enumCtorsShift`, `LeanScriptCli/Check.lean`).
`PrimOpBooleanNotRegression.test` takes a function, so it has no checks. `OrderingCmp` has 126 at
each preset, and all pass.
