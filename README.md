This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# LeanScript

A typed object language embedded in Lean: a type language (`Ty`, with the proof `Ty.Wf`
that a tree is a type), a grammar of terms that terminates by construction (`Term`), an
evaluator into Lean values, and `#leanscript_to_term`, which translates a Lean definition
into a `Term`.

Build everything, tests included, with `lake build`.

## Layout

| path | what it holds |
| :-- | :-- |
| `LeanScript/Ty/` | the type language: `Ty`, `Ty.Wf`, the `ty_wf` tactic, the bundle `TyWf`, the class `LeanScriptTyWf`, its instances and `deriving LeanScriptTyWf` (see `LeanScript/Ty/README.md`) |
| `LeanScript/LeanPrimTy.lean`, `LeanScript/LeanPrimTyCovariant.lean` | the leaf types and leaf type formers |
| `LeanScript/LeanInitPureExterns.lean`, `LeanScript/LeanInitPureExterns/` | the catalogue of the pure externs of `Init`, one module per theme (`Core`, `FixedWidth`, `String`, `Float`) |
| `LeanScript/ExprCtx.lean`, `LeanScript/DeBruijn.lean` | contexts, variables and the signature of a module |
| `LeanScript/Expr/` | the grammar `Term` and what it is written with (`Expr/Design.lean` explains the design) |
| `LeanScript/Den.lean`, `LeanScript/Den/` | `Ty.Den`, what a type of the language denotes, including the recursive types (as W-types) |
| `LeanScript/Eval.lean`, `LeanScript/Eval/` | the evaluator, its environments, and the value of each extern (`Eval/Extern/`, one module per module of the catalogue) |
| `LeanScript/EvalFacts.lean`, `LeanScript/*Facts.lean` | what the evaluator and the folds do, proved |
| `LeanScript/ToTerm/` | `#leanscript_to_term` (start with `ToTerm/Overview.lean`); `ToTerm/ExternTable.lean` is generated |
| `LeanScript/CtorFn.lean`, `LeanScript/CtorFn/` | `#leanscript_ctor`, a constructor of any datatype as a function on terms |
| `LeanScript/Nominal/` | proposal N of `proposals/NominalTyProposal.md`, next to the old stack: closed types over declared blocks (`Ty.lean`, `Decl.lean`), their meaning (`Container.lean`, `Den.lean`, `DenFacts.lean`, `Two.lean`), terms with `data_in`/`data_out`/`data_rec` and their evaluator (`Term.lean`, `Eval.lean`), the command `leanscript_signature` (`Signature.lean`), and the cached term elaborators `#leanscript_get_ty`, `#leanscript_get_ctor` and `#leanscript_get_cases` (`GetCtor.lean`), all built on one generator in `Gen/` (`Read.lean`: reading Lean types; `Translate.lean`: SCCs, blocks and grounding order; `Print.lean`: syntax; `Cache.lean`: the environment extension of programs and generated definitions); tests in `TyTests/Nominal*.lean` and `TermTests/NominalTermTest.lean` |
| `NonEmpty/` | correct-by-construction non-empty lists, arrays and strings |
| `TyTests/`, `TermTests/` | the tests, checked by `lake build` (`#guard_msgs` snapshots) |
| `docs/` | notes on the design (`TermTypeSafety.md`, `WfUsage.md`, `RecSnapshots.md`, `MATHLIB_REUSE.md`) |
| `proposals/` | proposals, reviews and stand-alone sketches; nothing here is part of the build |
| `scripts/` | `gen_externs.py`, which regenerates `LeanScript/ToTerm/ExternTable.lean` from the catalogue, and benchmarking scripts |

There is no module that gathers the others: a file imports the modules it uses, one by
one.

## Regenerating the extern table

After editing the catalogue (`LeanScript/LeanInitPureExterns.lean` or a module of
`LeanScript/LeanInitPureExterns/`), run from the root of the project:

```
python3 scripts/gen_externs.py
```

---

This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
