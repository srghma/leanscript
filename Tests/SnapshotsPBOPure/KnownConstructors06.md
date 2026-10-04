# `KnownConstructors06`: our output compared with purescript-backend-optimizer

Files: `KnownConstructors06.lean` (the Lean port), `KnownConstructors06.purs` and
`legacy-backend/KnownConstructors06.js` (purescript-backend-optimizer), and our outputs
`KnownConstructors06-pbo.js` / `KnownConstructors06-faithful.js` (and `-Term-*.txt`). The
variants are in `Tests/SnapshotsMy/KnownCtorEnumFactor.lean`. The checks are in
`knownConstructors06Spec` (`Tests/Main.lean`).

The PureScript file derives `Show` for an enum of four constructors through `Generic`. The Lean
port derives `Repr`. `deriving Repr` writes, for each constructor,

```lean
| .Foo => Repr.addAppParen (Format.group (Format.nest (if prec ≥ 1024 then 1 else 2) "Test.Foo")) prec
```

and `Repr.addAppParen f prec` is `if prec ≥ 1024 then Format.paren f else f`. The result is a
`Std.Format`, a recursive union, so `--check` writes no checks for this file (`0 passed`). The
variants return strings, numbers and pairs, and are checked against Lean.

## Before

Each of the four arms built its own `Format` and tested `1024 <= prec` twice. The inner test
was not recognised as the outer one, so the inner `x ? 1 : 2` was kept:

```js
export const instReprTest$repr = (x, prec) => {
  if (x === 0) {
    return 1024 <= prec
      ? { tag: 6, _1: { tag: 4, _1: 1, _2: { tag: 5, _1: { tag: 5, _1: { tag: 3, _1: "(" },
          _2: { tag: 6, _1: { tag: 4, _1: 1024 <= prec ? 1 : 2, _2: { tag: 3, _1: "Test.Foo" } },
          _2: false } }, _2: { tag: 3, _1: ")" } } }, _2: false }
      : { tag: 6, _1: { tag: 4, _1: 1024 <= prec ? 1 : 2, _2: { tag: 3, _1: "Test.Foo" } }, _2: false };
  }
  if (x === 1) { … the same, with "Test.Bar" … }
  if (x === 2) { … "Test.Baz" … }
  return … "Test.Qux" …;
};
```

(157 lines after formatting.)

## After

```js
export const instReprTest$repr = (x, prec) => {
  let x$1;
  if (x === 0) {
    x$1 = "Test.Foo";
  } else if (x === 1) {
    x$1 = "Test.Bar";
  } else if (x === 2) {
    x$1 = "Test.Baz";
  } else {
    x$1 = "Test.Qux";
  }
  return 1024 <= prec
    ? {
        tag: 6,
        _1: {
          tag: 4,
          _1: 1,
          _2: {
            tag: 5,
            _1: {
              tag: 5,
              _1: { tag: 3, _1: "(" },
              _2: {
                tag: 6,
                _1: { tag: 4, _1: 1, _2: { tag: 3, _1: x$1 } },
                _2: false,
              },
            },
            _2: { tag: 3, _1: ")" },
          },
        },
        _2: false,
      }
    : { tag: 6, _1: { tag: 4, _1: 2, _2: { tag: 3, _1: x$1 } }, _2: false };
};
```

(44 lines.) The test `1024 <= prec` is made once on every path. Each constructor name is written
once, picked by one chain of `if`s, and the `Format` is built by a single expression. There is
no closure, no recursion and no `throw`.

Legacy's `showTest.show` is the same kind of chain of `if`s, each returning a string. Its
`Show` builds no document, so it has no counterpart to our `Format` expression. Legacy also keeps
`genericTest.to`/`from` (the `Generic` instance), which has no counterpart in the Lean port, and
ends each chain with `throw new Error("UNREACHABLE")`. We write the last arm as `else`, because
the case analysis is exhaustive.

## What changed (all in `Term → Term`)

1. **Hoisting of `Nat` comparisons** (`LeanScript/Term/Optimize/ExternEq.lean`). `Extern.beq`,
   which tells the optimiser that two calls call the same extern, did not recognise any entry of
   `PreludeExtern`. That family holds `lean_nat_dec_le`, `lean_nat_add`, `lean_nat_mul`,
   `lean_string_dec_eq`, …. So two calls `1024 <= prec` were never seen as the same and never
   computed once. `Extern.beq` now also compares the entries of `PreludeExtern` that take no
   type argument, by their constructor index (`Extern.preludeOfIdx`, moved there from
   `ShareTest.lean`; `Extern.eq_of_beq` is still proved). `Term.hoistWalk` then computes
   `1024 <= prec` once, above the `case`.
2. **Known conditions inside constructors** (`LeanScript/Term/Optimize/KnownCond.lean`).
   `PExpr.condSimp` simplifies the arms of `c ? a : b` knowing whether `c` holds. It used to stop
   at the first constructor, and now also goes into records, unions, arrays, lists, `data_in` and
   the arguments of extern calls. So `x ? ⟨…, x ? 1 : 2, …⟩ : ⟨…, x ? 1 : 2, …⟩` becomes
   `x ? ⟨…, 1, …⟩ : ⟨…, 2, …⟩` (`Neu.condSimp_eval` is extended to the new cases).
3. **Arms that differ only by a literal** (new pass `Term.factorWalk`,
   `LeanScript/Term/Optimize/FactorArms.lean`). A `case` on an enum whose arms all answer the
   same expression, except for one literal, becomes a join point that the arms jump to with
   their literal:

   ```
   join j (s : String) := ret E[s]
   case x of | 0 => jump j "Test.Foo" | 1 => jump j "Test.Bar" | …
   ```

   The JavaScript printer already writes such a join point as a variable assigned by the arms
   (`let x$1; if … x$1 = …`), with no closure. How it works:
   - The first position where the literals of two arms differ gives the literal `v₀` of the
     first arm. `E` is the first arm with every `v₀` replaced by the parameter.
   - Each arm `eᵢ` is accepted with its own literal `vᵢ` only when `eᵢ`, with its `vᵢ` replaced
     by the parameter, is written the same way as `E` (`PExpr.same`). So `E[vᵢ]` has the value
     of `eᵢ`.
   - The pass runs only when `E` is big enough to be worth sharing: `12 ≤ (n - 1) * size E` for
     `n` arms. A `case` that only picks a literal (`nameOf` in the variants) is kept as it is.
   - Proofs: `Branch.factorAt_eval` and `Term.factorWalk_eval` show the value is unchanged, and
     `Term.numCalls_factorWalk` shows no call is added. `Term.optimize_eval` and
     `Term.numCalls_optimize` still hold, with the new pass in the pipeline. They depend only on
     `propext`, `Classical.choice` and `Quot.sound`.

No change was needed in `Term → JsTerm` or `JsTerm → JsTerm`. There is no loop or recursion here,
so labelled blocks or loops do not come into it.

## The variants (`Tests/SnapshotsMy/KnownCtorEnumFactor.lean`)

These run 173 checks per preset, all passed. To check functions that take an enum,
`leanscript --check` now has samples for enumerations: an inductive type without parameters,
with three or more constructors and no fields, written in JavaScript as the index of its
constructor. Results of enum type are compared by that index. This also adds checks to
`KnownCtorEnumParse` (97 instead of 87), `TagChain` and `BranchSpecialization01`.

| function | result |
|---|---|
| `instReprColor.repr` | the same as `KnownConstructors06` |
| `wrap` | `let x$1; if … x$1 = "<red"; …; return x$1 + s + ">";` |
| `twice` (the name twice in each arm) | `return { _1: x$1, _2: x$1 + s };` |
| `codeOf` (a number differs) | `let x$2; if … x$2 = 10; …; return { _1: x$2, _2: { _1: x$1, _2: "color" } };` |
| `label`, `wildcard`, `isRed` | kept: the shared part is too small to be worth a join point |
| `nameOf` (only the literal) | kept: `if (c === 0) return "red"; …` |
| `twoLits` (two literals differ), `oneOther` (one arm has another shape) | kept |
| `paren` (as `Repr.addAppParen`, but on strings) | kept: Lean folds `"(" ++ "red" ++ ")"` into one literal `"(red)"`, so two literals differ in each arm. The inner test is gone: `x$1 ? { _1: "(red)", _2: 1 } : { _1: "red", _2: 2 }` |
| `reprString` (`Format.pretty`) | not translated: `Std.Format.be` is private and has no extern |

## Other snapshots that changed

- `ProfunctorLenses01` (`instReprRecFooBaz.repr`): one `const x$1 = String(x._2);` is now written
  at its only use, so the function body is a single expression.
- `CaseRedBlackTree` (Term only): inside an `if f15`, the constructor that rebuilds the node now
  holds `true` instead of `f15`. The JavaScript is unchanged.

Every other snapshot is unchanged, and every node check reports 0 failed.
