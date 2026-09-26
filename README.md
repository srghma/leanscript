This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# LeanScript

A typed object language embedded in Lean, with one grammar of types and one grammar of
terms:

* **types** (`Ty ks`): closed types whose recursive datatypes are *declared once*, in a
  datatype signature (`DSig ks`), and named (`Ty.data r`).  Every type has at least two
  values (`Ty.den_exists_ne`); a type of no or one value (`Unit`, `Empty`, …) cannot be
  written, and a type of two values is always `Ty.bool` (a union needs a constructor with
  fields, `BitVec 1` is refused, …): every type other than `Ty.bool` has three different
  values (`Ty.den_exists_three`, `Ty.eq_bool_of_two_points`);
* **terms** (`Term Δ Γ τ`): a direct-style grammar that terminates by construction (every
  loop is a fold: `nat_rec`, `array_foldl`, `data_rec`, `data_brec`), with a total,
  structural evaluator `Term.eval` into Lean values;
* **generators**: `leanscript_signature` declares the datatypes of a program,
  `#leanscript_get_ty` / `#leanscript_get_ctor` / `#leanscript_get_cases` give the type,
  the constructors and the case analysis of a Lean type, and `#leanscript_to_term`
  translates a Lean definition into a `Term`.

Build everything, tests included, with `lake build`.  The project depends on Lean core
(and Batteries/Aesop in the manifest), not on Mathlib.

## Layout

| path | what it holds |
| :-- | :-- |
| `LeanScript/LeanPrimTy.lean`, `LeanScript/EnumSchema.lean` | the leaf types and the payload of an enum |
| `LeanScript/Ty.lean` | `Ref`, `BRef`, the mutual `Ty`/`Fields`/`Ctor`/`Ctors`, `UnionShape`, with `DecidableEq`, `BEq`, `LawfulBEq`, `Repr` |
| `LeanScript/Decl.lean` | declarations of blocks of datatypes (`Fld`, `Decl`, `Mems`, `DSig`) and `unfold` |
| `LeanScript/Container.lean`, `LeanScript/Den.lean` | what a type denotes: indexed W-types for the declared blocks, `Ty.den`, `Ty.Den`, `DSig.dataIn`/`dataOut`/`dataRec` |
| `LeanScript/DenFacts.lean`, `LeanScript/DenBrec.lean` | `dataIn`/`dataOut` are inverse; course-of-values recursion `DSig.dataBrec` and its computation rule |
| `LeanScript/Two.lean` | every type has two values that a Boolean test tells apart |
| `LeanScript/Three.lean` | every type other than `bool` has three values that a test tells apart: two points are only ever `bool` |
| `LeanScript/DeBruijn.lean`, `LeanScript/Term.lean`, `LeanScript/Eval.lean` | the grammar of terms and its evaluator |
| `LeanScript/Signature.lean`, `LeanScript/GetCtor.lean`, `LeanScript/Gen/` | `leanscript_signature`, `#leanscript_get_ty`/`_ctor`/`_cases`, and the generator they share (reading Lean types, SCCs and grounding order, printing, cache) |
| `LeanScript/ToTerm.lean` | `#leanscript_to_term` |
| `LeanScript/LeanInitPureExterns.lean`, `LeanScript/LeanInitPureExterns/`, `LeanScript/LeanInitPureExternShorthands.lean`, `LeanScript/CatalogueShorthands.lean`, `LeanScript/LeanPrimTyCovariant.lean` | the catalogue of the pure externs of `Init` (not used by the language) |
| `LeanScript/KernelRfl.lean` | `kernel_rfl`, an equation checked by the kernel only |
| `NonEmpty/` | correct-by-construction non-empty lists, arrays and strings |
| `TyTests/`, `TermTests/` | the tests, checked by `lake build` (`#guard_msgs` snapshots, `rfl` runs) |
| `proposals/` | proposals, reviews and stand-alone sketches; nothing here is part of the build (`NominalTyProposal.md` is the design that is implemented) |
| `scripts/` | benchmarking scripts |

There is no module that gathers the others: a file imports the modules it uses, one by
one.

---

This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
