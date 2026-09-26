# Proposal: let `Term.eval` run recursive tagged unions

> **Status: implemented.**  The construction below is now in the library:
> `LeanScript/Den/Cont.lean` (containers, W-trees, `WTree.memo`), `LeanScript/Den.lean`
> (`Ty.Cont`, and `Ty.Den` as its shapes), `LeanScript/Den/Rec.lean` (`roll`/`unroll`,
> `Ty.DenRec.mk`/`unfold`, the `TyWf` bridge, `recBindEnv`, `Ty.DenRec.toList`),
> `LeanScript/Eval/NoRecMk.lean` and `LeanScript/Eval.lean` (the four clauses and the four
> `FoldK` evaluators), and `LeanScript/RecUnionEvalFacts.lean` (the theorems of §5).  The
> text below is kept as the design record; its "not added" wording describes the state
> before the implementation.


This is a **proposal**. None of it has been added to the library: no file under
`LeanScript/` or `TyTests/` was changed. The central construction has been type-checked as
a standalone sketch, `proposals/RecTaggedUnionEvalSketch.lean`, against the current tree
(see [§9](#9-what-was-checked)). The rest of this document is a design and has **not**
been checked in Lean.

The goal:

* give `Ty.recTaggedUnion l` real values in `Ty.Den`, in place of `PEmpty`;
* make `Term.eval` interpret `recTaggedUnion_mk`, `recTaggedUnion_casesOn`,
  `recTaggedUnion_casesOnWithDefault` and `recTaggedUnion_rec` (at every depth `k`);
* change the `recTaggedUnion_mk` clause of `Term.NoRecMk` from `False` to
  `Spine.NoRecMk fields`, so `recTaggedUnion` leaves `NoRecMk`;
* keep `Term.eval` a **total, structurally recursive** Lean function, with no fuel, no
  `partial` and no Mathlib.

`recObject`, `recAlias` and `mutualRecursiveFamily` stay as they are (`PEmpty`,
`NoRecMk = False` at their `_mk`). [§8](#8-later-the-other-three-recursive-shapes) says
how the same construction would extend to them.

---

## 1. Where things stand

* `LeanScript/Den.lean`: `Ty.Den` maps each of the four binders, and `Ty.self` /
  `Ty.familyMember`, to `PEmpty`.
* `LeanScript/Eval/NoRecMk.lean`: `Term.NoRecMk` is `False` at the four `_mk`
  constructors. At the eliminators it only asks about the scrutinee, because the branches
  are never reached.
* `LeanScript/Eval.lean`: the eliminators evaluate to `PEmpty.elim (Term.eval G v env h)`.
* `TermTests/EvalCoverageTest.lean` proves that this restriction is forced by the model:
  `natListTy` denotes an empty type, so no evaluator can be total.

So a translated `List Nat` program (`TermTests/ToTermTest/Basic.lean`, "Lists") can be
type-checked but not run.

## 2. Why this is hard in Lean

`Ty.Den (.recTaggedUnion l)` has to be the **least fixpoint** of the functor that `l`
describes. In that functor `Ty.self` stands for the argument, and each constructor's
fields are a product. The obvious encodings don't work:

| idea | problem |
| :-- | :-- |
| an inductive `Val : Ty → Type` | `Val (fn a b) = Val a → Val b` puts `Val` in a negative position, so Lean rejects it |
| an inductive `RVal` defined together with `Ty.Den` (induction-recursion) | Lean has no induction-recursion |
| iterate `Den_n` and take a limit | not structural; needs quotients or extra proofs |
| fuel / `partial` | gives up totality, which is the point of the evaluator |

What *does* work is to describe every tree as a **container** (a type of shapes and, for
each shape, a type of holes where `Ty.self` sits) and take the least fixpoint as a
**W-type**. This works because of three facts the project already has:

1. **Positivity.** `Ty.WfShapeIn.fn` checks the domain of an arrow in the closed scope,
   so `Ty.self` never appears to the left of an arrow.
2. **Nested binders are opaque.** An occurrence inside a nested binder belongs to that
   binder (`Ty.WfIn`, and `Ty.substOcc` stops at binders). So within one payload there is
   exactly **one** variable to take the fixpoint of, and never an outer one.
3. **The payload's formers are all containers:** constants (closed types), `→` with a
   closed domain (an exponent), `Array` (a list), `Thunk`/`Lazy` (identity), records
   (products) and tagged unions (sums).

## 3. The construction

### 3.1 Containers and W-trees

These are self-contained and need no Mathlib. The names avoid Mathlib's `WType`.

```lean
structure Cont where
  S : Type          -- shapes
  P : S → Type      -- the holes of a shape

inductive WTree (S : Type) (P : S → Type) : Type
  | mk (s : S) (f : P s → WTree S P)

def Cont.const (A : Type) : Cont := ⟨A, fun _ => PEmpty⟩
def Cont.prod  (c d : Cont) : Cont := ⟨c.S × d.S, fun p => c.P p.1 ⊕ d.P p.2⟩
def Cont.sigma (I : Type) (c : I → Cont) : Cont := ⟨(i : I) × (c i).S, fun p => (c p.1).P p.2⟩
def Cont.pi    (A : Type) (c : Cont) : Cont := ⟨A → c.S, fun f => (a : A) × c.P (f a)⟩
def Cont.list  (c : Cont) : Cont := ⟨List c.S, ListPos c.P⟩   -- holes of each element
def Cont.mu    (c : Cont) : Cont := Cont.const (WTree c.S c.P) -- closed: no holes left
def Cont.Ext   (c : Cont) (X : Type) : Type := (s : c.S) × (c.P s → X)
```

### 3.2 One container per tree, with `Ty.Den` as its shape type

`Ty.Cont : Ty → Cont` is one mutual, **structurally recursive** family. It has the same
layout as today's `Ty.Den` / `Ty.DenShape` / … / `Ty.DenAtList`, one function per
container:

| tree | `Ty.Cont` |
| :-- | :-- |
| `Ty.self` | `⟨PUnit, fun _ => PUnit⟩`: one hole |
| `Ty.prim p`, `Ty.enum s` | `Cont.const …`: no holes |
| `a ⇒ b` | `Cont.pi (Ty.Cont a).S (Ty.Cont b)`: the domain is used as a type, its holes are ignored |
| `Array a` | `Cont.list (Ty.Cont a)` |
| `Thunk a`, `Lazy a` | `Ty.Cont a` |
| record, one constructor's fields | `Cont.prod` along the fields |
| `taggedUnion l` | `Cont.sigma (Fin l.length) (fun t => Ty.ContAt l t)` |
| **`recTaggedUnion l`** | **`Cont.mu (Cont.sigma (Fin l.length) (fun t => Ty.ContAt l t))`** |
| `recObject`, `recAlias`, `mutualRecursiveFamily`, `familyMember` | `Cont.const PEmpty`, as today |

Then

```lean
@[reducible] def Ty.Den     (t : Ty)      : Type := (Ty.Cont t).S
@[reducible] def Ty.DenList (ts : List Ty) : Type := (Ty.ContList ts).S
@[reducible] def Ty.DenAt   (l) (t : Nat) : Type := (Ty.ContAt l t).S
-- … and likewise DenShape, DenCov, DenNE, DenRecord, DenAtCP, DenAtList
```

**Every equation of today's `Ty.Den` still holds by `rfl`.** The sketch checks
`Ty.Den (.fn a b) = (Ty.Den a → Ty.Den b)`, `Array`, `Thunk`, record, `prim`,
`DenList (t :: ts)` and `taggedUnion`, all with `rfl`. So `Eval.lean`, `Eval/Env.lean`,
`Eval/Extern.lean`, the `*RecFacts` files and the existing `rfl` tests should not need to
change. What is new:

```lean
Ty.Den (.recTaggedUnion l)
  = WTree ((t : Fin l.length) × Ty.DenAt l t) (fun p => (Ty.ContAt l p.1).P p.2)   -- rfl
```

A value is a node: a constructor number, that constructor's fields **with the holes
blanked out**, and one subtree per hole. The existing lemmas (`Ty.denNE_eq`,
`Ty.denAt_eq`, …) keep their statements and proofs.

The one visible change is that `Ty.Den .self` becomes `PUnit` instead of `PEmpty`. Only
ill-formed trees have a `Ty.self` outside a binder, and nothing relies on the `PEmpty`:
with this one-line change (together with §3.3) the whole project, tests included, still
passes `lake build` (see `proposals/RecTaggedUnionEvalStep1.patch` and
`proposals/RecTaggedUnionEvalReview.md`).

### 3.3 Leave the domain of an arrow alone when substituting

`Ty.substOcc` (in `LeanScript/Ty/Unfold.lean`) currently substitutes in both sides of an
arrow. Change one clause:

```lean
def substOccShape (s : Ty) (m : Nat → Ty) : TyShape Ty → TyShape Ty
  | .fn a b => .fn a (substOcc s m b)        -- was: .fn (substOcc s m a) (substOcc s m b)
  …
```

For well-formed trees the result is the same, because the domain is closed. For
ill-formed trees it is just a different total function. What the change buys: the domain
of an unfolded arrow is **definitionally** the domain of the container, so `roll` and
`unroll` below need **no `cast` and no `Ty.Wf` hypothesis**. Without the change, the `fn`
clause would need `WfIn 0 a → substOcc s m a = a` and a cast along it.

The proofs that follow the arrow case (`Ty.wf_substOcc`, `Ty.wf_substOccFam` in
`Ty/WfSubst.lean`) get simpler in that clause, because the domain is returned unchanged.

The change also makes one existing lemma **false**: `Ty.substOccShape_eq_map` in
`Ty/Unfold.lean` (`substOccShape s m sh = sh.map (substOcc s m)`), because `TyShape.map`
maps both sides of an arrow. Nothing else in the project uses it, so it has to be deleted
(or restated for well-formed shapes). `Ty.substOcc` is used only in `Ty/Unfold.lean`,
`Ty/WfSubst.lean` and `Ty/TyWfIn.lean`; everything else reaches it through `unfoldSelf` /
`unfoldFamily`, so the change also affects the mutual-family unfolding, where the domain
is closed as well. `proposals/RecTaggedUnionEvalStep1.patch` is this step, checked with a
full `lake build`.

### 3.4 `roll` and `unroll`: an unfolded field is a shape plus a value in each hole

Fix `R : Ty` (the binder) and write `X := Ty.Den R`. By structural recursion on the
payload tree `a`, in one mutual block (one function per container, as in `Ty.Den`):

```lean
roll   R : (a : Ty) → Ty.Den (unfoldSelf R a) → (Ty.Cont a).Ext X
unroll R : (a : Ty) → (Ty.Cont a).Ext X      → Ty.Den (unfoldSelf R a)
-- plus rollShape / rollCov / rollList / rollAt / rollAtCP / rollAtList, same for unroll
```

The clauses are the obvious ones: `self ↦ ⟨(), fun _ => x⟩`; constants have no holes;
`fn` maps pointwise; `Array` maps along the list; a nested binder is a constant. The
helpers that walk a *list of values* (`Cont.Ext.list`, `Cont.Ext.unlist`) and a function
(`Cont.Ext.pi`) are written **outside** the mutual block and take the recursive call as a
function argument. That keeps the block structural on `Ty` alone. The sketch found this
restriction the hard way: a `rollArray` placed inside the block, or a partial application
of `roll`, breaks structural recursion.

Then the introduction and one-level elimination of a recursive union are:

```lean
def Ty.DenRec.mk (l) (t : Fin l.length)
    (v : Ty.DenAt (substOccTU (.recTaggedUnion l) .familyMember l) t) : Ty.Den (.recTaggedUnion l) :=
  let r := rollAt (.recTaggedUnion l) l t v
  WTree.mk ⟨t, r.1⟩ r.2

def Ty.DenRec.unfold (l) : Ty.Den (.recTaggedUnion l) →
    (t : Fin l.length) × Ty.DenAt (substOccTU (.recTaggedUnion l) .familyMember l) t
  | .mk ⟨t, s⟩ f => ⟨t, unrollAt (.recTaggedUnion l) l t ⟨s, f⟩⟩
```

A tag bound for the unfolded schema is moved over with `length_substTU ▸ t.isLt`. This
is a proof, not data, so no cast is involved.

### 3.5 The `TyWf` layer

`Term` is indexed by `TyWf`, and the fields of `recTaggedUnion_mk` have type
`TyWf.DenList ((TyWf.recTaggedUnionUnfold l hwf).get t ht)`. This is the same type as
`Ty.DenAt (substOccTU R .familyMember (l.map toTy)) t` up to `List.map` fusion,
`LeanTaggedUnionSchema.get_map`, `Ty.substOccTU_eq_map` and `Ty.denAt_eq`. So add one
bridging equation

```lean
theorem TyWf.denRecFields_eq (l hwf t ht) :
    TyWf.DenList ((TyWf.recTaggedUnionUnfold l hwf).get t ht)
      = Ty.DenAt (Ty.substOccTU (TyWf.recTaggedUnionTy l) .familyMember (l.map TyWfIn.toTy)) t
```

and define `TyWf.DenRec.mk` / `TyWf.DenRec.unfold` by casting along it. This is the same
pattern `TyWf.DenTU.mk` already uses. Lean's kernel reduces `Eq.rec`/`cast` on concrete
types by K-like reduction, so concrete runs still compute by `rfl`/`decide`, as they do
for `taggedUnion_mk` today.

## 4. The evaluator

### 4.1 `Term.NoRecMk` (`LeanScript/Eval/NoRecMk.lean`)

```lean
  | _, _, .recTaggedUnion_mk _ _ _ _ fields => Spine.NoRecMk fields              -- was False
  | _, _, .recTaggedUnion_casesOn v cases =>
      Term.NoRecMk v ∧ TaggedUnionCases.NoRecMk cases                             -- branches now run
  | _, _, .recTaggedUnion_casesOnWithDefault v cases dflt _ =>
      Term.NoRecMk v ∧ TaggedUnionSomeCases.NoRecMk cases ∧ Term.NoRecMk dflt
  | _, _, .recTaggedUnion_rec _ v cases =>
      Term.NoRecMk v ∧ TaggedUnionFoldKCases.NoRecMk cases
```

Add four new members to the mutual block: `FoldKBranch.NoRecMk`,
`TaggedUnionFoldKCases.NoRecMk`, `CtorsWithPayloadFoldKCases.NoRecMk` and
`TaggedUnionFoldKCasesRest.NoRecMk`. They follow the same pattern as the existing
branch-family predicates. The `no_rec_mk` macro (`trivial` / `And.intro`) needs no change.

The branches now appear in the conjunction. That is required: once the scrutinee has
values, a branch that builds a `recObject` value really is evaluated.

### 4.2 The four clauses of `Term.eval` (`LeanScript/Eval.lean`)

```lean
  | _, _, .recTaggedUnion_mk l hwf t ht fields, env, h =>
      TyWf.DenRec.mk l hwf ⟨t, _⟩ (Spine.eval G fields env h)
  | _, _, .recTaggedUnion_casesOn v cases, env, h =>
      TaggedUnionCases.eval G cases env (TyWf.DenRec.unfold (Term.eval G v env h.1)) h.2
  | _, _, .recTaggedUnion_casesOnWithDefault v cases dflt _, env, h =>
      TaggedUnionSomeCases.eval G cases env (TyWf.DenRec.unfold (Term.eval G v env h.1))
        (Term.eval G dflt env h.2.2) h.2.1
  | _, _, .recTaggedUnion_rec _ v cases, env, h =>
      WTree.memoFold (fun node kids => TaggedUnionFoldKCases.eval G cases env node kids h.2)
        (Term.eval G v env h.1)
```

`TaggedUnionCases.eval` and `TaggedUnionSomeCases.eval` are reused unchanged. The
unfolded schema is an ordinary `LeanTaggedUnionSchema TyWf`, and `DenRec.unfold` returns
exactly the `TyWf.DenTU` of it (after the §3.5 cast).

### 4.3 The fold at depth `k`: memoising on the tree

A depth-`k` branch (`FoldKBranch.deep`) may dispatch again on a field that is an
occurrence of the union (`SelfField`), up to `k` times, and read the fold's answers down
there. Recomputing those answers inside the recursion is possible but costs exponential
time, and it makes structural recursion awkward (the call would be on a grandchild
`g q` of `mk s f`). This proposal does what `natFoldK`/`listFoldK` do with their windows
instead: **carry the answers along**.

```lean
/-- The tree with the fold's answer stored at every node. -/
abbrev Memo (S : Type) (P : S → Type) (β : Type) := WTree (S × β) (fun p => P p.1)

def Memo.answer : Memo S P β → β | .mk (_, b) _ => b

/-- Bottom-up: compute the children's memos, then the answer at this node from the node
    and its children's memos (which hold every answer below). -/
def WTree.memo (step : (s : S) → (P s → Memo S P β) → β) : WTree S P → Memo S P β
  | .mk s f => let kids := fun p => WTree.memo step (f p)
               .mk (s, step s kids) kids

def WTree.memoFold (step) (v : WTree S P) : β := (WTree.memo step v).answer
```

Both are structural on `WTree` and non-mutual, like `WTree.fold` in the sketch, which the
kernel reduces. The `step` is a new member of `Term.eval`'s mutual block, structural on
the branch tree:

```lean
TaggedUnionFoldKCases.eval G cases env
    (node : (t : Fin l.length) × Ty.DenAt l t)        -- the node's shape
    (kids : holes node → Memo …)                      -- memos of its subtrees
    (h : TaggedUnionFoldKCases.NoRecMk cases) : TyWf.Den τ
-- + CtorsWithPayloadFoldKCases.eval, TaggedUnionFoldKCasesRest.eval, FoldKBranch.eval
```

* It selects the branch by the node's tag, exactly as `TaggedUnionCases.eval` does.
* `FoldKBranch.here body`: evaluate `body` in `Env.append (bindEnv fs node kids) env`.
  Here `bindEnv` builds the environment `TyWf.recBinders R τ fs` describes. A field that
  is **literally** `Ty.self` contributes the subtree **and** its answer (read off the
  child's memo). Every other field contributes `unroll` of the field, with the subtrees
  read off the memos. `bindEnv` is a plain recursion on the field list `fs`, splitting on
  `⟨.self, _⟩ :: _` just as `TyWf.recBinders` does, so the environment's type reduces in
  each case.
* `FoldKBranch.deep sf cases'`: `sf : SelfField fs` identifies one hole of the node. Take
  that child's memo `.mk (s', _) kids'`, extend the environment with this node's
  `bindEnv`, and recurse into `cases'` on `(s', kids')`. The answers of the grandchildren
  are already stored in `kids'`, so no fold is recomputed. Each level costs time linear in
  the size of the branch tree, and the whole fold is linear in the size of the value.

At `k = 0` there is no `deep`. The memo is then just a fold with some bookkeeping: the
answer at a node is the branch evaluated on the children's answers.

## 5. What to prove

Put these in a new `LeanScript/RecUnionEvalFacts.lean`. They are the recursive analogue
of the `rfl` facts at the end of `Eval.lean`:

1. **Round trip.** `unroll R a (roll R a x) = x`, and `roll ∘ unroll = id` on
   `Cont.Ext`. These need `funext` (for arrow fields and for hole functions) and induction
   on lists (for `Array` fields), so they are propositional and not `rfl`.
2. **ι-rule for cases.**
   `eval (recTaggedUnion_casesOn (recTaggedUnion_mk l hwf t ht fields) cases) env
     = eval (taggedUnion_casesOn-like dispatch) … (Spine.eval fields env)`,
   i.e. `TyWf.DenRec.unfold (TyWf.DenRec.mk t fields) = TyWf.DenTU.mk t ht fields`. This
   follows from (1). There is a matching lemma through `TyWf.DenTU.field?` for the
   `WithDefault` form.
3. **ι-rule for the fold** at `k = 0`: the fold of `mk t fields` is branch `t` evaluated
   on the fields and, after each field that is literally `self`, the fold at that field.
4. **Depth does not change meaning.** `eval (rec k v (toFoldK c)) = eval (rec 0 v c)`,
   using `TaggedUnionFoldCases.toFoldK` from `LeanScript/RecUnionRecFacts.lean`. More
   generally, a `deep` branch equals the depth-0 program that recomputes the fold at the
   subvalue.
5. **Totality is kept.** This is not a theorem: `Term.eval` still compiles by structural
   recursion. It is worth one sentence in the `Eval.lean` header.

## 6. Tests to update or add

* `TermTests/EvalCoverageTest.lean`: `natNil_not_noRecMk`, `natListTy_den_empty`,
  `den_fun_natList_subsingleton` and `run_natHead_eq_run_natFoldZero` become **false**.
  Comment them out with an explanation. Restate `no_total_evaluator` with a `recObject_mk`
  term, which is still outside the model. Add the positive checks:
  `Term.run natHead (cons 5 nil) = 5`,
  `Term.run natFoldZero … ≠ Term.run natHead …` on some input.
* `TermTests/RecTermTest.lean`: the `#guard_msgs` block that expects `⊢ natNil.NoRecMk` to
  fail now succeeds. Replace it with `Term.run GlobalEnv.nil natNil` and a `rfl` about its
  tag.
* `TermTests/RecUnionRecDepthTest.lean` §7: the `NoRecMk` examples stay, and there is now
  something to run. For example, `fib`/`hexa`/`fibTR`/`fibPair`/`cont` on Peano numbers
  and lists, checked by `decide`/`rfl` against their Lean versions (as `NatRecDepthTest`
  does for `nat_rec`).
* `TermTests/ToTermTest/Basic.lean` "Lists": `digitList_term`, `prepend_term`,
  `firstOrZero`, … can now be run, e.g. `run firstOrZero_term digitList_term = 1`. Their
  results are W-trees, so a result of list type should be compared after a small
  `toList` read-back (§7).
* Update the prose in `LeanScript/Den.lean` (header table), `LeanScript/Eval.lean`
  (header), `LeanScript/Eval/NoRecMk.lean` (section header),
  `LeanScript/ToTerm/Overview.lean` (the "Lists" paragraph) and
  `TermTests/ToTermTest/Basic.lean`, all of which say that a recursive tree has no values.

## 7. Nice to have

* **Read-back to Lean values.** `TyWf.DenRec.toList : Ty.Den (tyOf (List α)) → List (Den α)`
  and its inverse. Tests could then compare with Lean lists, and this is the first step
  of `LawfulLeanScriptTyWf` (`proposals/ImprovementProposals.md`, A2).
* **`Repr` for W-trees** through `unfold`, so `#eval` can print a recursive value.
* **`DecidableEq`**: not in general, since arrow fields contain functions. It is possible
  for payloads without `fn`, but that needs a decidability predicate on trees and is not
  needed for this proposal.

## 8. Later: the other three recursive shapes

The container view covers them with little extra work:

* `recAlias b`: `Cont.mu (Ty.Cont b)`, a single-constructor W-tree.
* `recObject fs`: `Cont.mu (Ty.ContRecord fs)`. Its lookback window
  (`TyWf.recObjectRecBinders`) reads answers at the literally-self positions of the
  record's `Array`/arrow fields, and the same memo supplies them.
* `mutualRecursiveFamily`: needs an **indexed** W-type,
  `IWTree (I) (S : I → Type) (P : (i : I) → S i → Type) (r : … → I)`, with `Fin n` as the
  index of the member. `Ty.Cont` becomes `Ty.Cont : Ty → (Fin n → Type) → Cont` for the
  family's scope. This is still structural, but it is the largest step, and should be
  done only after the three lone binders work.

After all four are done, `Term.NoRecMk` is `True` everywhere and can be deleted, together
with the `h` argument of `Term.eval`/`Term.run`.

## 9. What was checked

`proposals/RecTaggedUnionEvalSketch.lean` is **not** part of the Lake build: no library
glob matches `proposals/`. It compiles with no errors and no `sorry` when checked with

```
lake build LeanScript.Den LeanScript.Ty.Unfold LeanScript.Ty.WfFacts
lake env lean proposals/RecTaggedUnionEvalSketch.lean
```

on the current tree (Lean `v4.34.0`). Everything in it lives in the namespace
`LeanScript.Proto` and does not touch the real definitions. It contains:

* `Cont`, `WTree`, the combinators of §3.1, and the full `Ty.Cont` family of §3.2. These
  compile by **structural** recursion.
* `rfl` checks that `Ty.Den` defined as `(Ty.Cont t).S` satisfies today's equations for
  `fn`, `Array`, `Thunk`, record, `prim`, `DenList` and `taggedUnion`, and that
  `recTaggedUnion l` denotes the W-tree of §3.2.
* A copy of the substitution with the §3.3 change (`subst`), and the full `roll`/`unroll`
  families of §3.4 **without a single `cast`**.
* `mkRec` / `unfoldRec` (the §3.4 introduction and one-level elimination), a `WTree.fold`,
  and `List Nat` examples. Building `[3, 4]` and summing it is `7` by `decide` and by
  `rfl`. `head (5 :: [])` is `5` and `head []` is `0`, by `rfl`.
* The round trips of §5.1, `unroll_roll` and `roll_unroll`, proved with no extra
  hypothesis (axioms: `propext`, `Quot.sound`).
* Two checks against the real `Ty.WfIn` that positivity is strict positivity: both
  `(self → Nat) → Nat` and `(Nat → self) → Nat` are refused.

Separately, `proposals/RecTaggedUnionEvalStep1.patch` (steps 1 and the `Ty.Den .self`
line of step 2 of §10, applied to the real library) passes a full `lake build`.

The sketch does **not** contain the `TyWf` bridge of §3.5, the memoised depth-`k` fold of
§4.3, or any change to `Term.eval`/`Term.NoRecMk`. Those are the implementation work this
proposal describes.

## 10. Suggested order of work

1. `Ty/Unfold.lean`: the §3.3 one-clause change, and delete `Ty.substOccShape_eq_map`.
   Repair `Ty/WfSubst.lean`. `proposals/RecTaggedUnionEvalStep1.patch` does exactly this
   (plus the `Ty.Den .self` line) and passes `lake build`.
2. `Den.lean`: add `Cont`/`WTree`/`Ty.Cont` and redefine the `Ty.Den*` family as
   projections. Run `lake build`: all existing `rfl`s should still pass.
3. New `Den/Rec.lean`: `roll`/`unroll`, `Ty.DenRec.mk`/`unfold`, the `TyWf` bridge, and
   `WTree.memo`.
4. `Eval/NoRecMk.lean` and `Eval.lean`: the clauses of §4, plus the four `FoldK` evaluators.
5. `RecUnionEvalFacts.lean`: the theorems of §5.
6. Tests and prose (§6).
