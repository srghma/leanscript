# Reusing Mathlib / Batteries / core

`lakefile.toml` requires `mathlib` and `batteries` at `v4.34.0`.  (`lake-manifest.json`
has no Mathlib entry, so a fresh checkout needs `lake update mathlib` first.)

What the project takes from libraries instead of defining itself, and where.  The
remaining candidates, and what was checked and rejected, are in
`proposals/DeduplicationProposal.md`.

## Mathlib

| Project | Library declaration | Where |
|---|---|---|
| polynomial functors (shapes `A`, holes `B`) | `PFunctor` (`Mathlib.Data.PFunctor.Univariate.Basic`) | `LeanScript/Den/PFunctor.lean`, used directly (the former `Cont` structure is gone) |
| the values of a recursive shape | `WType` (`Mathlib.Data.W.Basic`) | `LeanScript/Den/PFunctor.lean` |
| `GlobalEnv ds` | `List.TProd` (`Mathlib.Data.Prod.TProd`) | `LeanScript/Eval/Env.lean`; `Ty.denList_eq_tprod` and `TyWf.denList_eq_tprod` relate `Ty.DenList` / `TyWf.DenList` to it |
| plain fold of a W-tree whose answer ignores the subtrees (`Ty.DenRec.toList`, `TyWf.Den.toName`, `WType.Memo.tree`) | `WType.elim` (`Mathlib.Data.W.Basic`) | `LeanScript/Den/Rec.lean`, `LeanScript/Expr/Extern.lean`, `LeanScript/Den/PFunctor.lean`.  `WType.fold` stays for the one fold that reads the subtrees (`RecUnionEvalFacts.lean`) |
| building / taking apart the root node of a recursive record or newtype (`Ty.DenObj.mk`/`unfold`, `Ty.DenAlias.mk`/`unfold`) | `WType.ofSigma` / `WType.toSigma`, with `WType.ofSigma_toSigma` / `WType.toSigma_ofSigma` for the round trips | `LeanScript/Den/RecObjectAlias.lean` |
| the round trips of `mk` / `unfold` of recursive values, and of `ofList`/`toList`, `ofArray`/`toArray` of container extensions | bundled as Mathlib `Equiv`s: `Ty.DenRec.equiv`, `Ty.DenObj.equiv`, `Ty.DenAlias.equiv` (and the `TyWf.` versions), `PFunctor.Obj.listEquiv`, `PFunctor.Obj.arrayEquiv` | `LeanScript/Den/Rec.lean`, `LeanScript/Den/RecObjectAlias.lean`, `LeanScript/Den/PFunctor.lean` |
| "a shape has no holes" (`Ty.NoSelfHoles`, `Ty.NoMemberHoles`) | `IsEmpty` | `LeanScript/Den/Holes.lean` |
| `map`, `traverse`, `Functor`, `LawfulFunctor` of `LeanRecordSchema`, `CtorsWithPayload`, `LeanTaggedUnionSchema`, `LeanFamMemberSchema`, `LeanMutualRecFamily`, `TyShape` | `deriving Traversable` and `LawfulTraversable` (`Mathlib.Tactic.DeriveTraversable`) | `Traversable` is derived where each type is declared (`LeanScript/Ty/Schema/*.lean`, `LeanScript/Ty/Shape.lean`); the laws are derived in `LeanScript/Ty/Traversable.lean` |

Notes on the derived instances:

- `NonEmptyList` and `LeanPrimTyCovariant` keep their hand-written `map` and `Functor`
  instance; each gets a short `traverse` and a `Traversable` instance
  (`LeanScript/Ty/Schema/Containers.lean`, `LeanScript/Ty/Shape.lean`), so the `NonEmpty`
  library and the `prelude` file `LeanScript/LeanPrimTyCovariant.lean` need no Mathlib.
  `deriving instance Traversable for …` was tried for them, but in a `module` the instance
  it produces is not exposed to other modules.
- The `LawfulTraversable` derivations all live in one module (`LeanScript/Ty/Traversable.lean`)
  and outside an exposed section: Mathlib's handler proves the laws with auxiliary lemmas
  that are private to the module it runs in.
- The functor laws are `id_map` and `comp_map` (or `Functor.map_map`).  `x.map f` is the
  derived function and unfolds to `f <$> x`; a proof that needs `simp` to see through a
  nested `<$>` adds `Functor.map` to its simp set.
- Because `LeanScript/Ty/Schema/Containers.lean` imports Mathlib, every module of the
  `LeanScript` library now loads Mathlib.  Two visible effects: messages print `Nat` as `ℕ`
  (two `#guard_msgs` expectations in `TyTests/` were updated), and Mathlib's linters run on
  every file.

## Core Lean

| Project | Library declaration | Where |
|---|---|---|
| "no name of the signature is declared twice" (`Sig.h_names_unique`, formerly the Boolean `declNamesUnique`) | `List.Nodup` of the names (decidable, so `by decide` still discharges it; an empty signature is `⟨[], List.nodup_nil⟩`) | `LeanScript/ExprCtx.lean` |
| entry `i` of a list of containers, empty past the end (`IPFunctor.at`) | `List.getD` | `LeanScript/Den/IPFunctor.lean`; `IPFunctorFacts.at_map`/`at_map_of_le` are proved from `List.getD_eq_getElem?_getD` and `List.getElem?_map` |
| `natFold` | `Nat.rec` (the compiler supports it); `listFold` stays written out because the compiler does not support `List.rec` | `LeanScript/Eval/Env.lean` |
| strongly connected component of a `mutual` block | `Lean.SCC.scc` | `blockComponent`, `LeanScript/Ty/Deriving/Read.lean` |
| reading a numeral | `Lean.Meta.getNatValue?` (after `whnf`) | `natOf?`, `LeanScript/Ty/WfTactic/Leaves.lean` |
| `flatMap (#[f ·]) = map f` | `Array.map_eq_flatMap` | `NonEmpty/ArrayUtil.lean`, `NonEmpty/ArrayCorrectByConstruction/*` |
| `ToExpr (NonEmptyList α)`, `ToExpr (NonEmptyArray α)` | `deriving instance ToExpr` | `NonEmpty/*/ToExpr.lean` |
| a `Functor.map` without laws (`NonEmpty.DowngradeMap`) | `Functor` | the class is removed |

## Checked and not provided by the libraries

See the last table of `proposals/DeduplicationProposal.md`: `NonEmptyList` /
`NonEmptyArray` / `NonEmptyString`, `DeBruijnProj`, a type-valued `List.Any` (the project
defines `ListAnyT`), the `PFunctor` formers (`const`, `prod`, `sigma`, `pi`, `list`,
`array`, `mu`), `WType.fold` / `WType.memo`, and `DecidableEq` / `ReflBEq` for the nested
inductive `Ty`.
