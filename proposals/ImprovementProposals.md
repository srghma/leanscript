# Proposals for improving LeanScript

These are **proposals only**. Nothing in this file is implemented, and none of the claims
about what an item would take has been checked in Lean. Each item says what the code
does today, what could change, and why the change might be worth making. Items are grouped
by area and ordered roughly by how much they would help compared with what they would cost.

---

## A. Correctness guarantees (the biggest gaps)

### A1. Prove that `#leanscript_to_term` is correct
**Today.** `#leanscript_to_term` (in `LeanScript/ToTerm/*`) is a meta-program. What it
produces has the right type, because `Term` is intrinsically typed. Nothing states that
it has the right *value*. `TermTests/ToTermTest/` checks individual outputs with
`example : run foo_term 7 = 7 := rfl`.

**Proposal.** Make the translator also produce a proof that `Term.run G t = f`, where `f` is
the source definition, read through `Ty.Den` (Lean's own values). Two ways to do it:
- *Per translation (translation validation):* the elaborator also emits
  `theorem foo_term_correct : Term.run … foo_term = foo`. It proves it by `rfl` or
  `decide` where possible and by congruence lemmas otherwise. This fits the existing
  meta-program with the least disruption.
- *Once and for all:* prove a general theorem about the translator. That needs a
  deep embedding of the Lean fragment being translated, which is much more work.

Translation validation is the realistic first step. It would also turn every
`example … := rfl` in the tests into a checked theorem that holds for all inputs.

### A2. Relate `tyWfOf α` to `α`
**Today.** `LeanScriptTyWf α` (`LeanScript/Ty/Class.lean`) holds a `TyWf`, but nothing
connects `Ty.Den (tyOf α)` to `α`. `TyWf.asModelOf` even lets any tree serve as the model
of any type.

**Proposal.** Add a second, lawful class:
`class LawfulLeanScriptTyWf (α) extends LeanScriptTyWf α where equiv : Ty.Den (tyOf α) ≃ α`
(or a pair of functions with round-trip laws, since the project does not use Mathlib).
The `deriving` handler would write the two functions and prove the laws. A1 needs this
to state correctness for inputs and outputs of user-defined types.

### A3. Syntactic metatheory for `Term`
**Today.** `Term` has no renaming, weakening or substitution. `Term.eval_beta`
(`LeanScript/Eval.lean`) states β-reduction semantically.

**Proposal.** Define `Term.rename` (for context inclusions) and `Term.subst`, and prove
`eval (rename ρ t) env = eval t (env ∘ ρ)` and the same for substitution. This lets you
write optimisation passes (inlining, dead-`let` elimination, constant folding) with a
proof that each pass preserves meaning, and a later backend could use them as well.

### A4. Make well-formedness decidable
**Today.** `Ty.Wf` is proved by the `ty_wf` tactic (`LeanScript/Ty/WfTactic.lean`), which
builds a proof term with about 20 `partial def`s. If it fails, it fails with an error and no
counterexample.

**Proposal.** Write a checker `Ty.wf? : Ty → Bool`, prove it sound and complete, and
derive `Decidable (Ty.Wf t)`. Then:
- `ty_wf` could fall back to `decide` (or `by exact of_decide_eq_true rfl`) when the
  structural proof search fails;
- a missing `by ty_wf` proof would give a clear `false` instead of a failed search;
- the `partial def`s in the tactic could shrink or go away.

The hard part is the inhabitation condition (`Ty.HabIn`), which is a least fixed point
over the family. The checker would iterate until nothing changes, bounded by the number
of members.

---

## B. The type language (`LeanScript/Ty/`)

### B1. Replace the `bind` function in `TaggedUnionFoldCases` with a small datatype
This is the residual item already noted in `docs/TermTypeSafety.md`. `TaggedUnionFoldCases` takes
an arbitrary `bind : List ι → List TyWf`, but it is only ever given `TyWf.recBinders`
or `TyWf.famRecBinders`. A two-constructor datatype (`single` / `family`) would make the
index say exactly what it means. It would also rule out reindexings that are well typed
but make no sense.

### B2. Existentially typed fields (deferred on purpose)
You have said you do not want this yet, and do not want it done with the old `Twin`/`Seal`
approach. For when you come back to it: `TermTests/InductiveTypesTest/Existentials.lean`
already records the refusals and has a `TODO: we should be able to model using Term`. One
design that avoids twins is a `Ty.exists` binder with its own de Bruijn level. Values
would be pairs of a type code from a *closed universe of codes* and a value, which keeps
everything in `Type`. Note the `Unfold` example you gave only erases a `Prop` field
(`decreasing`). A narrower first step would be to erase proof fields and leave
`State : Type` as the only real existential.

### B3. More derived instances on the core trees
`BEq`/`LawfulBEq`/`DecidableEq` are now in place. Other cheap instances:
- `Repr` for `Ty`, `TyWf` and `TyWfIn`. Only 3 `Repr` instances exist under `LeanScript/`,
  so `#eval` of a tree currently prints nothing useful. A `Repr TyWf` that prints only the tree
  would help when debugging.
- `Hashable Ty`, so trees can be keys in the `deriving` handler's table of trees
  (`Ty/Deriving/Read.lean`) and in `ToTerm/Cache.lean`, instead of looking them up by
  `Expr` or by name.
- `ToString`/pretty-printing of a `Ty` in the surface notation (e.g.
  `{ tag: 0, _1: nat }`). Error messages would read better.

### B4. A generic traversal for `Ty`
`Ty.beq`, `Ty.Den`, `substOcc`, the `WfIn` family and several `TyWf.*Map` functions each
repeat a pass over `Ty`/`TyShape`/`List Ty`/schemas. A single `Ty.foldM` (or a
`TyShape.map` with a `LawfulFunctor` proof) would remove most of that repetition. The catch:
`Ty.Den` depends on these equations holding *definitionally*
(`LeanScript/Den.lean`, line 40 onward), so that one should stay hand-written. The
proof-level traversals are the candidates.

### B5. Syntax for trees
Nested trees in tests are written out with anonymous constructors. A small `ty!{ … }`
term elaborator (or `declare_syntax_cat lsty`) with `nat`, `α → β`, `[α]`,
`{ a, b }`, `A | B c` and `μ self. …` would make the test files shorter and easier to read,
especially `TyTests/WfTest.lean` and the `*RecDepthTest/Programs.lean` files.

---

## C. The term language and evaluator

### C1. Get rid of `Expr/Design.lean`'s commented-out sketch
`LeanScript/Expr/Design.lean` holds 35 of the project's remaining `sorry` mentions, all in
a commented-out historical sketch. `LeanScript/Expr/Term.lean` lines 279–286 hold 8 more.
If the history matters, move it into a markdown design note. The Lean sources would then
have no `sorry` mentions at all, and a `sorry` check in CI (D2) would be exact.

### C2. A `ToExpr`/pretty-printer for `Term`
A `Term` printed by the delaborator is hard to read. A pretty-printer, even one that
only prints the target language's surface syntax, would make translation failures and test
output much easier to follow. The `proposals/FibProposals.md` section "How each depth prints" already
sketches what the output should look like.

### C3. Unify the depth-indexed folds
There are now six folds that take a lookback depth `k`: `nat_rec`, `array_rec`,
`recTaggedUnion_rec`, `recObject_rec`, `recAlias_rec` and `mutualRecursiveFamily_rec`.
Each has its own case families and its own `…RecFacts.lean` file proving that depth 0
agrees with the plain fold. The recursive shapes might all be instances of
one fold over `mutualRecursiveFamily`, with a single-member family standing for `self`, plus a
translation. If so, the proofs would be written once. This is a large refactor. First check
that it does not make the terms `#leanscript_to_term` produces for the common cases worse.

### C4. Evaluator performance
`Term.eval` is a structural denotational evaluator, and `run` is used in `rfl` proofs.
Kernel reduction of deep folds (tribonacci to hexanacci at depth 5) may become slow.
Options: a `@[csimp]`-justified faster evaluator for `#eval`, which is checked by the
kernel and is *not* `implemented_by`, or `decide`-friendly specialisations for closed terms.

---

## D. Engineering

### D1. CI
Add a GitHub Actions workflow that runs `lake build`, and fails on any `sorry`
(`rg -n '\bsorry\b' --glob '*.lean'` after C1), on any `axiom`, and on any warning,
using `-DwarningAsError=true` for the `LeanScript` library.

### D2. Split the remaining large files
`LeanScript/Expr/Term.lean` (1071 lines) is over the 1000-line mark.
(`LeanScript/ToTerm/Trans.lean` is now about 480 lines: its recursor clauses moved to
`ToTerm/TransRec.lean` and `ToTerm/TransBrec.lean`, which take `trans` as an argument.)
`Term.lean` could split along its
existing structure: primitive forms / non-recursive shapes / recursive shapes / case
families (the `…Cases` inductives from about line 490 on). Being one `mutual` block
limits this, so the case families would need to stay with the constructors that use
them, or be parametrised the way `ToTerm/Cases.lean` now takes a `BranchFn`.

### D3. A test that the import graph has no cycles or umbrella modules
You want every file to import its children one by one. A small script or a `#guard`
over `Lean.Environment.importGraph` could check two things: that no
`LeanScript/Ty.lean`-style file re-exporting other modules comes back, and that
`Ty/Class.lean` does not become circular again.

### D4. Put the loose markdown files in one place
`proposals/FibProposals.md`, `docs/RecSnapshots.md`, `docs/TermTypeSafety.md`, `LeanScript/Ty/README.md` and
this file are all design notes. A `docs/` folder with an index would make them easier to
find, and stale sections could then be removed. For example, `proposals/FibProposals.md` records
five proposals, one of which is now implemented.

### D5. Refusal-message tests for every `throwError`
`LeanScript/ToTerm` has about 90 `throwError` sites. `TermTests/ToTermTest/` and
`TyTests/DocumentedMistakesTest.lean` cover some of them with `#guard_msgs`. A
`#guard_msgs` test for each user-facing refusal would keep the messages from drifting
unnoticed. Messages marked `internal:` should be unreachable, and a comment or a proof
could say why.

---

## Suggested order

1. **C1, D1**: cheap, and every later change can then be checked mechanically.
2. **B3, B5**: small changes that make daily work easier.
3. **A2, then A1** (translation validation): the main correctness gain.
4. **A4, B1**: tighten the type language.
5. **A3, C3, C4**: larger refactors, worth doing once A1 exists to catch regressions.
6. **B2**: only when you decide to support existential fields.
