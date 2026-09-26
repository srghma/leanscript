# Review of the assessment of `proposals/RecTaggedUnionEvalProposal.md`

Summary: the bottom line of the assessment is right. The construction doesn't weaken
totality or soundness, and the parts that are least checked are the `TyWf` bridge and the
memoised fold. Of its four points, two were fair and now have concrete answers, one was
partly overtaken (the round trips now have proofs), and one gets its example wrong.

Everything below was checked against the current tree:

* `proposals/RecTaggedUnionEvalStep1.patch` applies steps 1–2 of the proposal's §10 to
  the real library. After the patch, a full `lake build` (all 294 jobs, tests included)
  passes with no errors or warnings. The patch was **not** applied to the tree.
* `proposals/RecTaggedUnionEvalSketch.lean` now also contains both round-trip proofs and
  two positivity checks. It compiles with no `sorry` (see the header of that file for the
  command).

## 1. "The `substOcc` change is global": fair, and the audit found one thing the proposal missed

The call-site audit:

* `Ty.substOcc` itself appears only in `Ty/Unfold.lean`, `Ty/WfSubst.lean` and
  `Ty/TyWfIn.lean`. Everything else reaches it through `unfoldSelf`, `unfoldMembers` /
  `unfoldFamily` and the `*Unfold` / `recBinders` definitions. So the change also affects
  **mutual-family** unfolding, which the proposal didn't mention. There the domain is
  closed too, so well-formed trees give the same result.
* **The proposal missed one lemma.** `Ty.substOccShape_eq_map`
  (`substOccShape s m sh = sh.map (substOcc s m)`) becomes **false**, because
  `TyShape.map` maps both sides of an arrow. The build stops on its `fn` case. Nothing
  else uses it, so the patch deletes it.
* The repair in `Ty/WfSubst.lean` is two one-line edits: the `fn` case of `wf_substOcc`
  and of `wf_substOccFam` now pass the domain's existing `WfIn 0` hypothesis through
  unchanged.
* Nothing else broke. That covers every `rfl`/`decide` test on unfolded types and every
  `*RecFacts` file.

So "everything else unaffected" was nearly right, but it was only an assertion. There was
one real casualty, and the proposal has been corrected (§3.3, §10).

## 2. "`Ty.Den .self : PUnit` was checked by `rg`, not by argument": fair, and now checked by building

The same patch changes `| .self => PEmpty` to `| .self => PUnit` in `LeanScript/Den.lean`.
The full build passes. That includes `EvalCoverageTest` (whose emptiness arguments are
about `recTaggedUnion`, not `self`) and anything that found `Subsingleton`, `IsEmpty` or
`decide` instances for a type. So no proof depended on `Ty.Den .self` being empty, either
directly or through instance search. The proposal (§3.2) now cites the build instead of
`rg`.

## 3. "The sketch checked the easy half": partly overtaken

* **Round trips: now proved.** `unroll_roll`
  (`unroll R a (roll R a x) = x`) and `roll_unroll` (`roll R a (unroll R a x) = x` on
  `Cont.Ext`) hold for every tree, with **no extra hypothesis** and no naturality
  condition. They are proved by mutual structural recursion over `Ty`, using only
  `propext` and `Quot.sound`. What caused trouble was not a missing property but
  definitional unfolding. `Ty.ContShape` and friends are ordinary definitions, so
  `rw`/`simp` can't see that `(Ty.ContShape (.fn a b)).Ext X` *is*
  `(Cont.pi …).Ext X`. Each case has to restate its goal at the unfolded container first.
  In the list case the two components also have to be generalised before substituting.
  Expect the same friction in the real library.
* **The `TyWf` bridge cast: still unchecked, but not new.** `TyWf.DenTU.mk` already
  chains two casts (`get_map`, then `Ty.denAt_eq`) and is evaluated concretely in the
  existing tests. Lean's kernel reduces `cast` on concrete closed types because both
  sides are definitionally equal, whatever the equality proof is. So the claim that
  concrete runs still compute is well founded. What still needs writing is the
  equational lemma (`denRecFields_eq`) and the ι-rules through it.
* **The memoised fold: still unchecked.** It is the least de-risked part, as the
  assessment says.

## 4. "Positivity check granularity": right that it's a flat ban, but the example is wrong, and the flat ban is what the construction needs

* It **is** a flat ban. `Ty.WfShapeIn.fn` requires `WfIn 0 a` for the domain `a`. In
  scope `0` there is no `Ty.self` at all, only inside a nested binder, where it belongs to
  that binder.
* The example is wrong. In `(X → self) → Y`, `self` sits in the codomain of the domain,
  so it is flipped **once**: that is a *negative* occurrence, and refusing it is required.
  The doubly-negated, *positive* shape would be `(self → X) → Y`.
* Both are refused. The sketch proves
  `¬ Ty.WfIn 1 ((self → Nat) → Nat)` and `¬ Ty.WfIn 1 ((Nat → self) → Nat)` against the
  real definitions.
* Refusing the positive one is **intended**. The check is *strict* positivity, which is
  the same rule Lean's own kernel applies to inductive types. The container encoding
  depends on it: `Cont.pi` uses the domain only as a *type* of indices and gives it no
  holes. A positive but not strictly positive occurrence is not a polynomial functor, so
  it has no W-type fixpoint. Allowing polarity tracking would break the construction, not
  merely extend it. So the soundness argument (§2, fact 1) rests on exactly the check the
  code performs.

## Bottom line

I agree with the conclusion that the design doesn't let anything unsound in. As for how
far it is de-risked: the substitution change and the `Ty.Den .self` change are now
checked on the real library by a full build. The round trip, which the assessment
predicted would be the first casualty, is proved. What is still design only is the `TyWf`
bridge lemmas, the memoised depth-`k` fold, and the `Term.eval` / `Term.NoRecMk` changes.
The advice to prototype those standalone before touching `Eval.lean` still stands.
