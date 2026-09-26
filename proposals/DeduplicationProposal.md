# What else can be replaced or de-duplicated

This follows the earlier step that swapped our own container type and tree type for Mathlib's
`PFunctor` and `WType`. It is a proposal only: **no Lean file of the project was changed.**

`docs/MATHLIB_REUSE.md` is out of date. It still describes `Cont` as a separate structure that
converts to and from `PFunctor`. In fact `Cont` has since been removed and
`LeanScript/Den/PFunctor.lean` uses `PFunctor` directly. It should be updated or folded into
this file.

## How the claims were checked

This workspace has no local Mathlib: `lake-manifest.json` has no Mathlib entry, as before.
So every claim that involves Mathlib was checked in a **separate scratch project** pinned to
Lean 4.34.0 and Mathlib `v4.34.0`, using stand-in copies of the relevant types rather than
the project itself. The test files are in `proposals/dedup-probes/`. They are outside every
`lean_lib` glob and are not part of `lake build`; each one's header states its expected
result. Claims that only need core Lean were checked with the project's toolchain the same
way. Anything not backed by a probe is marked *(not tested)*.

## Summary

| # | What | Replace / merge with | Removes (approx.) | Risk | Checked |
|---|---|---|---|---|---|
| 1 | Hand-written `map`, `map_id`, `map_comp`, `Functor`/`LawfulFunctor` for 8 schema types | Mathlib `deriving Traversable, LawfulTraversable` | ~170 lines, ~16 lemmas, 16 instances | low–medium (imports) | yes (probe) |
| 2 | `GlobalEnv` (right-nested product over a list) | Mathlib `List.TProd` | 3 definitions | low | yes (probe) |
| 3 | Internal duplicates: `NonEmptyListSchema.*`, `LeanTaggedUnionSchema.map_map`, `DowngradeMap` | existing project declarations / `Functor` | ~40 lines, 1 class | very low | by reading |
| 4 | `TaggedUnionCases` / `CtorsWithPayloadCases` / `TaggedUnionCasesRest` | the existing `…FoldCases` trio at `ι := TyWf`, `bind := id` | 3 of the 28 types in the `mutual` block of `Expr/Term.lean` | medium | yes (toy probe) |
| 5 | `SelfField` and `FamilyMemberField` (two copies of the same shape) | one generic, type-valued "some element satisfies `p`" family | 1 inductive | low | *(not tested)* |
| 6 | `NonEmpty.ArrayUtil` lemmas, hand-written `ToExpr (NonEmptyList α)` | core lemmas, `deriving ToExpr` | 2 lemmas, 1 instance | very low | yes (probe) |
| 7 | Meta helpers: `nameReach` + `blockComponent`, `natOf?` | core `Lean.SCC.scc`, `Lean.Meta.getNatValue?` | ~25 lines | low | names checked |
| 8 | `TyWf` vs `TyWfIn 0` (two structures, duplicated instances) | `abbrev TyWf := TyWfIn 0` | 1 structure + ~6 instances/lemmas | medium–high | partly |

Items 1–3 and 6 are the cheapest and safest. Item 4 is the one that also helps build time.

---

## 1. Derive `Functor` / `Traversable` for the schemas

**What is duplicated.** Each of these types has a hand-written `map`, `map_id` and `map_comp`,
plus hand-written `Functor` and `LawfulFunctor` instances:

| Type | File(s) |
|---|---|
| `NonEmptyList` | `NonEmpty/ListCorrectByConstruction/{Basic,Instances}.lean`, and again as `NonEmptyListSchema` in `Ty/Schema/Containers.lean` and `Ty/Schema.lean` |
| `LeanRecordSchema`, `CtorsWithPayload` | `Ty/Schema/Containers.lean`, `Ty/Schema.lean` |
| `LeanTaggedUnionSchema` | `Ty/Schema/Sum.lean`, `Ty/Schema.lean`, and again in `Den/Rec.lean` (`map_map`) |
| `LeanFamMemberSchema`, `LeanMutualRecFamily` | `Ty/Schema/Family.lean`, `Ty/Schema.lean` |
| `LeanPrimTyCovariant` | `LeanPrimTyCovariant.lean`, `Ty/Shape.lean` |
| `TyShape` | `Ty/Shape.lean` |

**Replacement.** `Mathlib.Tactic.DeriveTraversable` provides
`deriving Traversable, LawfulTraversable`. From that one line you get `Functor`, `Traversable`,
`LawfulFunctor` and `LawfulTraversable`, so `id_map` and `comp_map` come for free. You also get
`traverse`, which is the same thing as the hand-written `NonEmptyList.mapA` / `mapM`.

**Evidence** (`dedup-probes/DeriveTraversableSchemas.lean`). The derivation succeeds on
stand-in copies of all eight types. That includes the nested fields (`NonEmptyList α`,
`List (List α)`, `List (LeanFamMemberSchema α)`) and the non-`α` fields (`LeanPrimTy`,
`LeanEnumSchema`). The derived `map` is structurally recursive and unfolds to the same terms as
the hand-written one; the probe checks this by `rfl`:
```lean
Functor.map f (NEL.mk a l)  = NEL.mk (f a) (l.map f)            -- rfl
Functor.map f (CWP.skip c)  = CWP.skip (Functor.map f c)         -- rfl
#print TU.map
-- | payloadFirst fields next rest => payloadFirst (f <$> fields) (f <$> next) (Functor.map f <$> rest)
```
So `Ty.DenTU (l.map TyWf.toTy)` and similar terms should still reduce by kernel `rfl`.

**How to migrate while keeping call sites.** There are about 15 uses of `….map TyWf.toTy`. Keep
each `map` name as `@[reducible] def map (f) (x) := Functor.map f x`, or as an `abbrev`, so
`fs.map TyWf.toTy` keeps working. Then delete the seven `map_id`/`map_comp` pairs (`NonEmptyListSchema`, the five schemas and
`TyShape`), the eight `Functor`/`LawfulFunctor` instance pairs, and `LeanTaggedUnionSchema.map_map` (section 3).
Lemmas such as `toList_map` should still be `rfl` or `simp [Functor.map]`, but this was not
tested on the real files.

**Caveats.**
- **Imports.** Today only `Den/PFunctor.lean` imports Mathlib. Deriving in `Ty/Schema/*` moves a
  Mathlib import to the root of the dependency chain. In the scratch project,
  `Mathlib.Tactic.DeriveTraversable` loads 1 370 modules and adding
  `Mathlib.Control.Traversable.Instances` (needed for `List`'s lawful instance) brings it to
  2 076. The Mathlib files already imported by `Den/PFunctor.lean` load 2 208 on their own, and
  all four together load 2 255. So the whole project loads about 50 extra modules, but modules
  that currently load no Mathlib at all would start loading about 2 000. Check this against
  `proposals/BuildSpeedResults.md` before adopting.
- **`NonEmpty` library.** The `NonEmpty` library has no Mathlib dependency. Deriving
  `Traversable` for the schemas needs a `Traversable NonEmptyList` instance. Either derive it
  inside `NonEmpty`, which makes that library depend on Mathlib, or declare the instance in
  `LeanScript` next to the schemas and keep `NonEmpty` free of Mathlib.
- `NonEmptyArray` cannot take part: Mathlib has no `Traversable Array` instance (none found in
  the Mathlib `v4.34.0` sources).

## 2. `GlobalEnv` is `List.TProd`

`GlobalEnv` in `Eval/Env.lean` is `PUnit` for `[]` and `TyWf.Den d.ty × GlobalEnv ds` for
`d :: ds`. That is Mathlib's `List.TProd (fun d => TyWf.Den d.ty) ds` (`Mathlib.Data.Prod.TProd`),
a right fold of `×` ending in `PUnit`. The same holds for `Ty.DenList`, `TyWf.DenList`,
`Env` and `NatWin` up to propositional equality.

**Evidence** (`dedup-probes/TProdEnv.lean`). With `abbrev Env Γ := List.TProd D Γ`, the existing
`get` (by structural match on the de Bruijn index) and `append` compile unchanged, and a concrete
lookup reduces by `rfl`.

**Proposal.**
- Define `GlobalEnv ds := List.TProd (fun d => TyWf.Den d.ty) ds`. This is cheap and self-contained,
  and gives `List.TProd.mk` and `Inhabited` for free.
- **Do not** redefine `Ty.DenList` as `TProd`. It is one of the `Ty.toPFunctorList` shapes inside
  the `mutual` block, and `TProd` goes through `List.foldr`, which is not structural there. Add a
  bridge lemma `Ty.DenList ts = List.TProd Ty.Den ts`, proved by induction with `rfl` per case,
  in case you want Mathlib's `TProd` lemmas.
- `List.TProd.elim` takes a `Prop` membership proof and `DecidableEq`, so it does **not** replace
  `Env.get`, which is indexed by a typed de Bruijn index.

## 3. Duplicates inside the project

These need no library at all.

- **`NonEmptyListSchema.map`** (`Ty/Schema/Containers.lean`) has the same body as
  `NonEmptyList.map` (`NonEmpty/ListCorrectByConstruction/Basic.lean`):
  `⟨f xs.head, xs.tail.map f⟩`. Likewise:
  - `NonEmptyListSchema.ofList?` is `NonEmptyList.fromList?`;
  - `NonEmptyListSchema.map_id` / `map_comp` (`Ty/Schema.lean`) are `NonEmptyList.map_id` /
    `map_comp` (`…/Instances.lean`).

  Delete the `NonEmptyListSchema` namespace; there are about 10 uses.
- **`LeanTaggedUnionSchema.map_map`** (`Den/Rec.lean`) is `LeanTaggedUnionSchema.map_comp`
  (`Ty/Schema.lean`) with the sides swapped. It is proved a second time, via `ofList?`, and used
  once.
- **`NonEmpty.DowngradeMap`** is `Functor.map` without the laws, with the same universe shape
  (`Type u → Type u`). Its only instances are for `NonEmptyList` and `NonEmptyArray`, which both
  already have `Functor` and `LawfulFunctor` instances, and nothing uses the class. Delete it.
- **`WfAllIn.of_append_left/right` and `HabAllIn.of_append_left`** (`Ty/WfSubst.lean`,
  `Ty/Wf.lean`) repeat, for each "every element" predicate, facts that follow from core `List`
  lemmas. One `wfAllIn_iff : WfAllIn n ts ↔ ∀ t ∈ ts, WfIn n t` (and the same for `HabAllIn`)
  would let `List.forall_mem_append`, `List.mem_flatten` and similar do the rest. The predicates
  themselves must stay: an inductive cannot nest through `∀ t ∈ ts`. *(not tested)*

## 4. Merge the plain-dispatch cases into the fold cases (`Expr/Term.lean`)

`TaggedUnionCases`, `CtorsWithPayloadCases` and `TaggedUnionCasesRest` have exactly the shape
of `TaggedUnionFoldCases`, `CtorsWithPayloadFoldCases` and `TaggedUnionFoldCasesRest`. The fold
versions are already indexed by the element type `ι` and by a function
`bind : List ι → List TyWf`. The plain versions are therefore the fold versions at
`ι := TyWf` and `bind := id`, where each branch's context is `id fs ++ Γ`, which is
definitionally `fs ++ Γ`.

**Evidence** (`dedup-probes/CasesAsFoldCases.lean`). In a toy `mutual` block, a `cases`
constructor that takes `FoldCases Nat id Γ l τ` compiles, and a branch lookup returns
`Term (fs ++ Γ) τ` with no cast.

**Effect.** It removes 3 of the 28 types in the `mutual` block, and every function that
recurses over them (evaluator clauses, facts files). `proposals/BuildSpeedProposals.md` measured that most
of that file's kernel time goes to code generated per type in the block, so this should also
help build time *(not measured)*. There are about 77 references to the three names to rewrite.

**What cannot be merged.** A single generic "one branch per constructor" family, parameterised
by the branch type, cannot be used inside the block: Lean rejects it with *"nested inductive
datatypes parameters cannot contain local variables"*
(`dedup-probes/GenericBranchesRejected.lean`). So the `…FoldKCases` trio and the
`Family…FoldKCases` trio, whose branch types differ, stay separate unless their branch types
(`FoldKBranch`, `FamilyFoldKBranch`) are merged first. That would be a larger redesign.

Indexing every case family by `l.toList` alone, instead of the three-constructor schema split,
would remove more types. But the evaluator would then need `Ty.denAt_eq` casts, because
`Ty.DenAt` is defined per schema shape. Not recommended.

## 5. One type-valued "some element satisfies `p`"

`SelfField fs` and `FamilyMemberField i fs` (`Expr/SelfField.lean`) are the same inductive:
`here : p a → F (a :: fs)` and `there : F fs → F (a :: fs)`, where `p a` is `a.toTy = Ty.self`
in one and `a.toTy = Ty.familyMember i` in the other. Neither Lean core nor Mathlib has a
**type-valued** `List.Any`: `List.Mem` and the `∃ x ∈ l` forms are `Prop`, and `List.Any` /
`List.Forall` do not exist in core Lean 4.34.0. So the proposal is one local
`inductive ListAnyT {α} (p : α → Prop) : List α → Type` with two abbreviations.
`FamilyMemberAt` is close, but it also fixes the position number, so leave it.

This is not the same as `DeBruijnProj`. `DeBruijnProj` puts the equation in the *index*
(`head : DeBruijnProj f (x :: xs) (f x)`), which is what makes `Env.get` reduce. Matching on
`DeBruijnProj TyWfIn.toTy fs Ty.self` would require solving `x.toTy = Ty.self` by unification,
which fails for a variable `x`. Keep both. *(not tested)*

## 6. Small things core Lean already has

- `NonEmpty.ArrayUtil.flatMap_singleton_eq_map` is `Array.map_eq_flatMap.symm`, and
  `flatten_map_singleton` is `by simp [← Array.flatMap_def, ← Array.map_eq_flatMap]`
  (`dedup-probes/ArrayUtilInCore.lean`). `mapA`, `sequence` and `foldMap` have no core
  counterpart for `Array` with only `Applicative`, so they stay.
- The hand-written `ToExpr (NonEmptyList α)` (and very likely the one for `NonEmptyArray`) can be
  `deriving Lean.ToExpr`, since core now has that handler (`dedup-probes/DeriveToExpr.lean`).
  `NonEmptyString` cannot use it, because of its proof field (the same probe shows the failure),
  so its instance and `mkDecidableProof` stay. Core's `Lean.Meta.mkDecideProof` runs in `MetaM`
  and so does not fit a pure `ToExpr`.

## 7. Meta code that re-implements core Lean

- `nameReach` and `blockComponent` (`Ty/Deriving/Read.lean`) compute strongly connected
  components with a breadth-first closure and fuel. Core has
  `Lean.SCC.scc : List α → (α → List α) → List (List α)` (`Lean.Util.SCC`), whose component
  containing `n` is what `blockComponent` returns. Check that the order within a component still
  matches declaration order, or re-filter `names` by membership as the current code does.
- `natOf?` (`Ty/WfTactic/Leaves.lean`) is `whnf` followed by `Expr.rawNatLit?`/`Expr.nat?`. Core's
  `Lean.Meta.getNatValue?` or `Lean.Meta.evalNat` does the same job. `listElems` and `natListOf`
  call `whnf` at every cons, which `Expr.listLit?` does not, so keep them.

## 8. `TyWf` as `TyWfIn 0` (optional, larger)

`Ty.Wf t` is `abbrev Wf t := WfIn 0 t`, so `TyWf` (`toTy`, `isWf : Ty.Wf toTy := by ty_wf`) is
field for field `TyWfIn 0` (`toTy`, `isWfIn : Ty.WfIn 0 toTy := by ty_wf`). Both have the same
hand-written `ext`, `CoeOut … Ty`, `BEq`, `LawfulBEq`, `DecidableEq` and `Inhabited`.
`abbrev TyWf := TyWfIn 0` with `abbrev TyWf.isWf (t : TyWf) : Ty.Wf t.toTy := t.isWfIn` would
remove one copy, and `Coe TyWf (TyWfIn n)` would become the `n = 0` case of `ofTyWf`.

What was checked (plain Lean, toy types): the `:= by …` default still works through the
`abbrev` exactly as it does for a structure (`{ toTy := … }` and `TyWfIn.mk t`). Anonymous-
constructor notation `⟨t⟩` does **not** fill the auto-param for either form, so nothing changes
there.

Risks, *(not tested on the project)*:
- `ty_wf` and `Ty/WfTactic/Leaves.lean` recognise `LeanScript.TyWf`, `TyWf.toTy` and `TyWf.isWf`
  by name. So do the `deriving LeanScriptTyWf` handler and the translator (`CtorFn/Cache.lean`
  builds `mkConst ``LeanScript.TyWf`). All of them would need updating.
- There would be a coercion from `TyWfIn 0` to itself.
- `Term` is indexed by `TyWf` everywhere, so this touches most of the project.

Only worth doing together with another large refactor.

## Checked and **not** replaceable

| Project declaration | Why it stays |
|---|---|
| `PFunctor.const/prod/sigma/pi/list/array/mu`, `ListPos`, `Obj.pair/prodFst/prodSnd/…` | Mathlib `v4.34.0`'s `PFunctor` (univariate) has only `Obj`, `map`, `W`, `Idx`, `comp` and the M-type. None of these formers exist (confirmed with `#check`). They could be offered upstream. |
| `WType.fold`, `WType.memo`, `Memo` | `WType.elim` does not pass the subtrees. `WType.rec` is a recursor, so the compiler cannot run it, and `#guard` tests need compiled code. `WType.equivSigma` could still be used to *state* `Den/Rec.lean`'s roll/unroll round-trips. |
| `Ty.beq` and its 12 companions (`Ty/TyBEq.lean`) | `deriving DecidableEq` and `deriving ReflBEq` fail for nested inductives in Lean 4.34.0 (`dedup-probes/NestedDecidableEqNotDerivable.lean`). |
| `NonEmptyList`, `NonEmptyArray`, `NonEmptyString` | Mathlib, Batteries and core have no such structure types; only `List.recNeNil` and similar recursion principles exist. |
| `DeBruijnProj` / `DeBruijn` | No type-valued list membership exists; see section 5 for why the equation-in-index form matters. |
| `natFold`, `listFold`, `natFoldK`, `listFoldK`, `NatWin` | `Nat.rec` and `List.rec` cannot be compiled. `Nat.fold` has a different signature, and `List.foldr` does not pass the tail. `NatWin` could be `Vector`, but it is kept definitionally equal to an environment on purpose, so no cast is needed. |
| All the per-shape `mutual` families (`toPFunctor*`, `Den*`, `roll*`, `unroll*`, `substOcc*`, `beq*`) | Writing them through a derived `map` would be nested recursion through `Functor.map`, which is not structural. That means well-founded recursion and the loss of the definitional unfolding that kernel `rfl` relies on. The existing `substOcc*_eq_map` lemmas are the right way to connect the two. |
| `LeanRecordSchema`, `CtorsWithPayload`, `LeanTaggedUnionSchema`, … as types | A subtype `{ l : List α // P l }` cannot appear as a nested occurrence inside `Ty` (see the note in `Ty/Schema.lean`). |

## Suggested order

1. Section 3 and section 6: pure deletions, no new dependencies.
2. Section 2: `GlobalEnv := List.TProd …`.
3. Section 1, after deciding where the Mathlib import may go.
4. Section 4: likely to help build time; measure before and after.
5. Sections 5 and 7 when those files are next touched. Section 8 only as part of a larger
   refactor.
