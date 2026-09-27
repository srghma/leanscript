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
| `LeanScript/Ty/LeanPrimTy.lean`, `LeanScript/Ty/LeanPrimTyCovariant.lean`, `LeanScript/Ty/EnumSchema.lean` | the leaf types, the covariant leaf type formers (arrays, thunks, lazy values; used by the extern catalogue) and the payload of an enum |
| `LeanScript/Ty/Ty.lean` | `Ref`, `BRef`, the mutual `Ty`/`Fields`/`Ctor`/`Ctors`, `UnionShape`, with `DecidableEq`, `BEq`, `LawfulBEq`, `Repr`; renaming `Ty.map` and its laws `Ty.map_id`, `Ty.map_map` |
| `LeanScript/Ty/Decl.lean` | declarations of blocks of datatypes (`Fld`, `Decl`, `Mems`, `DSig`) and `unfold` |
| `LeanScript/Ty/Container.lean`, `LeanScript/Ty/Den.lean` | what a type denotes: indexed W-types for the declared blocks, `Ty.den`, `Ty.Den`, `DSig.dataIn`/`dataOut`/`dataRec` |
| `LeanScript/Ty/DenFacts.lean`, `LeanScript/Ty/DenBrec.lean` | `dataIn`/`dataOut` are inverse; course-of-values recursion `DSig.dataBrec` and its computation rule |
| `LeanScript/Ty/Two.lean` | every type has two values that a Boolean test tells apart |
| `LeanScript/Ty/Three.lean` | every type other than `bool` has three values that a test tells apart: two points are only ever `bool` |
| `LeanScript/Term/DeBruijn.lean`, `LeanScript/Term/Term.lean`, `LeanScript/Term/Eval.lean` | typed de Bruijn indices and renamings, the grammar of terms (`PExpr.lit p v`, `PExpr.bvar i`) and its evaluator; everything that takes a value apart takes a neutral expression (`Neu`), so no ι-redex can be written (`TermTests/NoIotaTest.lean`) |
| `LeanScript/Term/Elim.lean`, `LeanScript/Term/TermSubst.lean` | the eliminations that reduce an ι-redex (`PExpr.mkDataOut`, `PExpr.mkCond`, `Term.mkIte`, `Term.mkEnumCases`), and renaming and hereditary substitution, with the facts that they commute with evaluation |
| `LeanScript/Term/Tuple.lean` | `Tuple F [a, b] = F a × F b`: right-nested products with no trailing `PUnit`, for environments, extern arguments and join-point closures |
| `LeanScript/Term/BoundedLoop.lean` | a loop of a fixed number of steps whose iterations shrink a measure has stopped after `μ init + 1` steps, and more steps change nothing (`boundedLoop_done`, `boundedLoop_stable`): why a translated `while` loop needs no fuel |
| `LeanScript/Term/TermSubst.lean` | renaming, weakening and substitution of terms; `Term.eval_rename`, `Term.eval_subst`, β and `let` as substitution |
| `LeanScript/GenElab/` (`Signature.lean`, `GetCtor.lean`, `Read.lean`, `Translate.lean`, `Print.lean`, `Cache.lean`) | `leanscript_signature`, `#leanscript_get_ty`/`_ctor`/`_cases`, and the generator they share (reading Lean types, erasing fields that depend on earlier fields — `Fin n → Nat` is `Nat → Nat`, `TermTests/DependentFieldTest.lean`; on a recursive cycle `Fin m → X` is `Nat → Option X`, so the rose tree `node : (m : Nat) → (Fin m → Rose) → Rose` is a record of a `nat` and a function to `Option Rose`, different from the `List` and `Array` rose trees, `TermTests/RoseVariantsTest.lean` — and the indices of inductive families — `Vec α n` is the linked list `Vec α`, `TermTests/IndexedFamilyTest.lean`; a type index recursed at other indices goes through a generated element type — `Nest α` is a list of `Nest.Elem α` trees, `TermTests/NestTest.lean` —; a quotient is read as its carrier and a proof field is dropped — `Quot (· % 2 = · % 2)` is `Nat`, `Pos` is `Nat`, `TermTests/QuotientTest.lean` —, SCCs and grounding order, printing, cache) |
| `LeanScript/TyElab/Notation.lean` | the `[Ty| …]` notation |
| `LeanScript/TermElab/Anf.lean`, `LeanScript/TermElab/Notation.lean` | the A-normaliser of direct-style source trees, and the `[Term| …]` notation built on it |
| `LeanScript/TermElab/ToTerm.lean`, `LeanScript/TermElab/ToTerm/` | `#leanscript_to_term` (`ToTerm/Basic.lean`: translation state and helpers; `ToTerm/Expr.lean`: the expression translator `tr`, with calls of library functions as calls of catalogue externs (`PExpr.extern`, table `ToTerm/ExternTable.lean`), pure `if`s as `PExpr.cond` and externs that take a proof, `TermTests/CondExternTest.lean`; `ToTerm/While.lean`: which `while` loops are structurally terminating, `TermTests/WhileTest.lean`; `ToTerm.lean`: the definition translator and the syntax), including `mutual` groups of recursive functions and members of a block held inside an `Array` or a function (`TermTests/MutualToTermTest.lean`) |
| `LeanScript/LeanInitPureExterns.lean`, `LeanScript/LeanInitPureExterns/`, `LeanScript/LeanInitPureExternShorthands.lean`, `LeanScript/ExternElab/CatalogueShorthands.lean` | the catalogue of the pure externs of `Init`, indexed by signature (`LeanInitPureExtern σs τ`): the language's only kind of extern |
| `LeanScript/Term/Extern.lean`, `LeanScript/Term/ExternEval.lean`, `LeanScript/Term/ExternEval/`, `LeanScript/Term/ExternShorthands.lean`, `LeanScript/ExternElab/TermShorthands.lean` | the catalogue instantiated at the types of the language (`Extern ks σs τ`), the meaning of every entry (`Extern.eval`), and one term former per entry (`PExpr.lean_string_any s f`, `Neu.lean_nat_add a b`) |
| `LeanScript/TacticElab/KernelRfl.lean` | `kernel_rfl`, an equation checked by the kernel only |
| `NonEmpty/` | correct-by-construction non-empty lists, arrays and strings (their literal notations and `ToExpr` instances are in `NonEmpty/*Elab/`) |
| `TyTests/`, `TermTests/` | the tests, checked by `lake build` (`#guard_msgs` snapshots, `rfl` runs) |
| `proposals/` | proposals, reviews and stand-alone sketches; nothing here is part of the build (`NominalTyProposal.md` is the design that is implemented) |
| `scripts/` | benchmarking scripts |

Elaborators, notations, tactics and the meta-level code they use live in `XxxElab/`
directories (`TyElab/`, `TermElab/`, `GenElab/`, `ExternElab/`, `TacticElab/`), next to the
modules they elaborate into.

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
