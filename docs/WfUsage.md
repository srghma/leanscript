# How the well-formedness proofs in `TyWf` are used

This note answers the question: *are the scope facts carried by `TyWf` / `TyWfIn` used to
skip impossible branches in the W-type / `PFunctor` machinery, and can that be improved?*

## 1. What `Ty.WfIn` actually guarantees about occurrences

`Ty.WfIn n t` (in `LeanScript/Ty/Wf.lean`) is indexed by a scope size `n`:

| scope | where | occurrences allowed | rule / lemma that forbids the others |
| :-- | :-- | :-- | :-- |
| `n = 0` | a closed type (`Ty.Wf`) | none | `Ty.not_wf_self`, `Ty.not_wf_familyMember` |
| `n = 1` | payload of `recTaggedUnion`, `recObject`, `recAlias` | `Ty.self` only | `Ty.not_wfIn_one_familyMember` |
| `n ≥ 2` | payload of `mutualRecursiveFamily` | `Ty.familyMember i`, `i < n` only | `Ty.not_wfIn_self_of_family`, `Ty.not_wfIn_familyMember_of_le` |

So: inside a `recTaggedUnion` (or `recObject`, `recAlias`) only `Ty.self` can appear, and
inside a `mutualRecursiveFamily` only `Ty.familyMember` can appear. A binder nested inside
a payload opens its own scope, so `Ty.self` always refers to the closest enclosing binder.

About `Ty.enum`: the payload is a `LeanEnumSchema`, which holds no `Ty`. So an enum
contains no occurrences simply because of how the data type is built, and no proof is
involved. The non-recursive shapes that do hold `Ty`s (`fn`, `array`, `thunk`, `lazy`,
`record`, `taggedUnion`) **can** hold `Ty.self` / `Ty.familyMember` when they are nested
inside a binder's payload (for example, `Option self` inside the payload of a recursive
union). Only at the top level (`n = 0`) are they free of occurrences.

`Ty.WfIn` also carries three conditions that are not about scope:

* **Positivity**: the domain of `fn` is checked in scope `0`.
* **Real recursion**: `OccursSomeIn 0 …` / `MembersOccur`.
* **Inhabitation**: `HabIn [] …` / `FamHab`.

## 2. How the denotation uses them (before this change)

The functions that build containers (`Ty.toPFunctor`, `Ty.toIPF` in `LeanScript/Den.lean`)
and their companions (`Ty.roll`/`unroll`, `Ty.famRoll`/`famUnroll`, …) take a **raw `Ty`**
and are defined by structural recursion on it. They never look at a proof. For the cases
that the scope rules make impossible, they return a harmless placeholder value instead:

* `Ty.toPFunctor (.familyMember _) = PFunctor.const PEmpty`, so `roll`/`unroll` get rid of
  that case with `PEmpty.elim`. This works because the value is empty, not because of a
  proof.
* `Ty.toPFunctor .self` has one hole wherever it appears, including in a closed type or a
  family's payload, where no binder exists to fill it.
* `Ty.toIPF .self = IPFunctor.const PUnit`.

Where the proofs **are** used:

* They form the *types*: `TyWfIn.unfold` needs `Ty.wf_unfoldSelf`, `TyWf.recTaggedUnion l
  hwf` needs `hwf`, and so on. `Term` is indexed by `TyWf`, so every type the evaluator
  sees is well formed.
* In `WfSubst.lean` (`wfAllIn_recBinders`), to show that the binders of a fold branch are
  well formed. Here the `familyMember` case is ruled out by `absurd … not_wfIn_one_familyMember`.

Where they were **not** used, although they could have been:

* `recBindEnv` (`Den/Rec.lean`) and `recBindEnvOf` (`RecUnionEvalFacts.lean`) had a real
  branch for a field `⟨.familyMember i, h⟩` of a lone binder's payload. That branch cannot
  happen, since `h : WfIn 1 (.familyMember i)` is false.
* `famBindEnv` (`Den/Family.lean`) had a real branch for a field `⟨.self, h⟩` of a
  family's payload. That branch cannot happen either, since `h : WfIn (n+2) .self` is false.
* Nothing in the project used `HabIn` / `FamHab` or `OccursIn` to compute anything, and no
  theorem connected them to `Ty.Den`.

## 3. What was changed in this session

1. **The impossible branches now use the proof.** In `recBindEnv`, `recBindEnvOf` and
   `famBindEnv`, the impossible case is now `absurd h Ty.not_wfIn_one_familyMember` or
   `absurd h (Ty.not_wfIn_self_of_family _)`. The code no longer produces a meaningless
   value there, and the matching case of `recBindEnv_eq_recBindEnvOf` is now a one-line
   contradiction instead of a rewrite. The evaluator's results are unchanged, and the full
   `lake build` passes.

2. **New file `LeanScript/Den/Holes.lean`**, which proves that the placeholder cases of the
   containers are never reached from well-formed trees:
   * `Ty.noSelfHoles_of_wfIn : WfIn n t → n ≠ 1 → Ty.NoSelfHoles t`. A tree that is well
     formed outside a lone binder's scope (closed, or in a family) has no holes in
     `Ty.toPFunctor`. Special cases: `Ty.noSelfHoles_of_wf` (closed types) and
     `Ty.noSelfHoles_of_family`.
   * `Ty.noMemberHoles_of_wfIn : WfIn n t → n ≤ 1 → Ty.NoMemberHoles t`. A tree that is
     well formed outside a family's scope has no holes in `Ty.toIPF`: the payload of a
     recursive union, record or newtype recurses only through `Ty.self`. Special cases:
     `Ty.noMemberHoles_of_binder` and `Ty.noMemberHoles_of_wf`.

   These are the formal version of "inside a `recTaggedUnion` only `Ty.self` can be used,
   inside a `mutualRecursiveFamily` only `Ty.familyMember`", stated at the level of the
   W-type containers. Both theorems depend only on the axioms `propext` and `Quot.sound`.

## 4. Further room for improvement (not done)

* **Keeping the placeholder values is a reasonable choice.** Threading `WfIn` through
  `Ty.toPFunctor` so that the impossible cases become `absurd` would make every
  denotation function take a proof argument. It would also make the `rfl` equations that
  `Term.eval` relies on harder to state, and the resulting types would depend on proofs.
  Keeping the placeholders and proving that they are never reached (section 3.2) gives
  the same guarantee.
* **Make inhabitation mean something for `Den`.** The docstring of `Den.lean` says "every
  closed type has values", but nothing proves it. The natural theorem is
  `Ty.Wf t → Nonempty (Ty.Den t)`, proved by induction on `HabIn` with a hypothesis about
  the members in `S`. For recursive binders it needs a W-tree built from the `HabIn []`
  witness, and for families it needs the `FamKnown` iteration. It would be the only place
  where `HabIn` / `FamHab` are used semantically.
* **Positivity is used without being stated.** `substOccShape` leaves the domain of `fn`
  untouched, and `toPFunctorShape (.fn a b)` uses only `(toPFunctor a).A`. So an
  occurrence in a domain would be quietly treated as closed. `roll`/`unroll` are
  inverse to each other regardless. What positivity ensures is that the result is the
  *intended* fixpoint. A theorem saying that the holes of a domain are empty under
  `WfIn` (a small corollary of `noSelfHoles_of_wf`, since the domain is `WfIn 0`) would
  make this explicit.
* **Rule out wrong occurrences with the types instead of proofs.** A scope-indexed syntax
  (for example `Ty : Scope → Type` with `Scope := closed | binder | family n`, where
  `self : Ty .binder` and `familyMember : Fin n → Ty (.family n)`) would make the wrong
  occurrences impossible to write. The impossible branches and the placeholder cases would
  then disappear. The costs: a nested inductive with an index (harder `deriving`,
  `BEq`/`DecidableEq`, and the `ty_wf` tactic), and positivity, recursion and inhabitation
  would still need proofs. This is a larger redesign.
* **Fewer duplicated cases.** `recBindEnv` / `famBindEnv` list all seven `Ty`
  constructors only so that `TyWf.recBinders` reduces (it matches `.self` against
  everything else). A small view such as `isSelf : Ty → Bool` or a `SelfView` inductive,
  used by both `recBinders` and `recBindEnv`, would reduce each to two cases.
* **Recursive records and newtypes.** `Ty.not_wf_recObject_self` / `not_wf_recAlias_self`
  already prove that a field of a record (or the body of a newtype) is never literally
  `Ty.self`. The code handles this with separate binders
  (`recObjectRecBinders`, `recAliasRecBinders`) and does not use those lemmas to remove a
  branch. This is fine as it is.
