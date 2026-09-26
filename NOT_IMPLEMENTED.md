# What is not implemented yet

This list was collected from the sources as they stand now: the refusal lists in
`LeanScript/ToTerm/Overview.lean`, `LeanScript/Ty/README.md` and `LeanScript/Expr/Design.lean`,
the error messages pinned by `#guard_msgs` tests, the comments in the code, and the
proposals in `proposals/`. Each item names the file where you can read more.

The proposal files are partly out of date. For example, `proposals/ImprovementProposals.md`
says that nothing in it is implemented, but `Term.rename` (A3) and the `BEq`/`DecidableEq`
instances (B3) exist now. The items below were checked against the code, not just copied
from those files.

---

## 1. The type language (`LeanScript/Ty/`)

- **Existentially typed fields.** A field whose value is a type (`State : Type`, or any
  field whose type ends in `Type`) makes `deriving LeanScriptTyWf` fail with *existential
  typing is not yet supported*. This covers `Unfold`, `Process`, `Client`, `StreamPipeline`,
  `CompilerEngine`, `Keyed` and similar types. The refusals are pinned in
  `TyTests/InductiveTypesTest/Parameters.lean` and
  `TermTests/InductiveTypesTest/Existentials.lean`, which also has
  `-- TODO: we should be able to model using Term`. You deferred this on purpose, and
  `LeanScript.Ty.Twin` / `LeanScript.Ty.Seal` were removed. `proposals/ImprovementProposals.md`
  §B2 and `proposals/LeanScriptTyCtorProposal.md` sketch possible designs. That proposal
  is marked *proposal only*.
- **Inductive families whose index changes the tree.** An example is
  `lit {α} (x : α) : E α`, where a value field has a type field as its type. Families
  indexed by types where only the indices mention the type (`TExpr`) are supported.
- **Nested inductives under an unknown type former.** A recursive occurrence is refused
  if it sits under something that is not `List`, `Array`, `Thunk`, a function, a union, a
  structure, or a type with its own `LeanScriptTyWf` instance.
- **`Ty.Wf` is not decidable.** There is no `Ty.wf? : Ty → Bool` checker and no
  `Decidable (Ty.Wf t)` instance. `ty_wf` is a proof search that builds the proof term,
  and when it fails you get no counterexample (`ImprovementProposals.md` §A4).
- **No link between a tree and its Lean type.** No class relates `Ty.Den (tyOf α)` to `α`
  (for example a `LawfulLeanScriptTyWf` with an equivalence), so nothing proves that a
  derived tree is a faithful model of the type (§A2).
- **Missing convenience instances.** There are no `Repr`, `Hashable` or `ToString`
  instances for `Ty`, `TyWf` or `TyWfIn`. Only `TyShape` derives `Repr`. There is also no
  surface syntax for writing trees (§B3, §B5).
- **`TyWf` and `TyWfIn 0` are still two structures,** each with its own instances
  (`proposals/DeduplicationProposal.md` item 8).

## 2. Leaf types and the extern catalogue

- **Effects.** `Ty` has no effectful former, so an `IO` declaration cannot be expressed.
  The impure externs are in the disabled file `LeanScript/LeanInitImpureExterns.lean_`,
  which is not part of the build. The catalogue sections for `Init/System/IO`,
  `Init/System/Promise`, `Init/ShareCommon`, `Init/Data/ByteArray`,
  `Init/Data/FloatArray`, `Init/Data/Repr` and `Init/Data/Nat/Gcd` are all commented out
  (`LeanScript/LeanInitPureExterns.lean`).
- **`task` and `promise`** are commented out of `LeanPrimTyCovariant`. `ChildProcess` and
  the `ShareCommon` handles are commented out of `LeanPrimTy`. `ByteArray` and `Fin` are
  not leaf types.
- **Three eliminators are missing** because their fields have no type in the language:
  `bitvec_casesOn`, `string_casesOn` and `stringSlice_casesOn`
  (`LeanScript/Expr/Design.lean`).
- **Universe-polymorphic catalogue entries** are refused
  (`LeanScript/CatalogueShorthands.lean`).

## 3. The term language (`LeanScript/Expr/`, `LeanScript/Eval*`)

- **Well-founded recursion.** It is *not supported yet* according to the table in
  `LeanScript/Expr/Design.lean`. `proposals/WellFoundedRecursionAssessment.md` plans a
  `Comp.fix` node with a `Nat` measure, a fallback and a run-time check, plus translator
  support for `WellFounded.Nat.fix`. None of that is in the library. The only version is
  the stand-alone model `proposals/WellFoundedRecursionToy.lean`, which is not part of the
  build, and it has no agreement theorem for the lexicographic combinator.
- **Partial fixpoints, coinductive types, `partial` and `unsafe`** cannot be expressed,
  and that is by design.  There is no fuel anywhere: a `while` loop is accepted only
  when the translator reads off its syntax that it is a structural recursion (a `Nat`
  counter that moves by one towards a bound on every path that goes on), and is then a
  `nat_rec` (`LeanScript/ToTerm/While.lean`, proved equal to Lean's loop for every input
  by `LeanScript.loop_forIn_eq_natRec` in `LeanScript/WhileFacts.lean`).  Any other
  `while` loop — `m := m / 2`, Euclid, Collatz, `while true` with no counter — is
  rejected.
- **No substitution theory.** `Term.rename` / `Term.weaken` exist (`Expr/Rename.lean`),
  but there is no `Term.subst` and no theorem that evaluation respects renaming or
  substitution (§A3). A proved-correct optimisation pass would need these.
- **The proof from `if h : …` is not reused.** `a[i]'h` inside `if h : i < a.size`
  becomes `Term.externCallChecked`, which tests the condition again and carries a
  fallback. `proposals/ProofCarryingDiteProposal.md` is not implemented.
- **No `Repr`/`ToExpr`/pretty-printer for `Term`** (§C2). The depth-indexed folds are not
  unified (§C3), and nothing was done on evaluator performance (§C4).
- **The two copies `SelfField` / `FamilyMemberField`** have not been merged into one
  generic family (`DeduplicationProposal.md` item 5). The meta helper `natOf?` has not
  been replaced by core's `getNatValue?` (item 7).

## 4. The translator `#leanscript_to_term` (`LeanScript/ToTerm/`)

These are the refusals listed in `LeanScript/ToTerm/Overview.lean`, *What is refused*:

- `partial` and `unsafe` definitions, `opaque` constants and axioms.
- Well-founded recursion (`WellFounded.fix`, `Acc.rec`, `termination_by`) and partial
  fixpoints (`Lean.Order.fix`).
- A `Nat` recursion that does not go down by a fixed number of steps, such as a call at
  `n / 2`. So `fibFast` in `TermTests/RecObjectRecDepthTest.lean` is refused.
- A `match` on a field of a value from *another* `mutual` block, written directly in the
  branch of a structural recursion. The workaround is to move the `match` into an
  `@[inline]` helper.
- In a structural recursion on a family whose member sits inside an `Array`, a function
  or a `Thunk` (`List (Array T)`, `node (qs : Array Q)`, `node (f : Nat → G)`), a call
  that looks more than one level deep through that field. A `Thunk` field must be read
  as `⟨f⟩` / `f ()` in the pattern: `t.get` in a recursive call makes Lean compile the
  definition by well-founded recursion. (Recursions on such families are supported —
  `TermTests/StructRecTest/NestedFamily.lean`.)
- Folds deeper than the search bounds: 64 for `nat_rec`/`array_rec`, 24 for
  `recObject_rec`/`recAlias_rec`, 16 for `recTaggedUnion_rec`/`mutualRecursiveFamily_rec`.
  The bounds can be raised with `set_option`.
- A call of a function that is not inlinable, not declared in the signature, and not a
  structural recursion or a wrapper of one. This includes a higher-order helper applied to
  a recursion, such as `applyTwice (go 2)`.
- A recursion written with the recursor of a user-defined type (`Tree.rec …`). Only
  `Nat.rec` and `List.rec` are read as folds. Pattern matching on `Tree` works.
- A function whose result type is the index of a family (`eval : TExpr α → α`). It is
  refused as a dependent motive.
- Existentials:
  - a function on a recursive datatype with existentials (`Process`) whose argument is not
    written out as a value;
  - a function on a non-recursive one at a fixed index (`Tag Nat → …`).
- A `match` on an `Array` (only array literals, `array_casesOn` on the elements taken off
  a list, and `a.toList` folds work). A `go` over `a.toList` that reads further than its
  first `k` elements is refused.
- `for` over a collection other than a `List` or a range (an `Array`, say). (Ranges
  with a start or a step, `[a:n:k]`, are translated: see
  `TermTests/ToTermTest/ForRangeStep.lean`; so is `for h : i in r` over a range, the form
  that names the membership proof: see `TermTests/ToTermTest/ForRangeMem.lean`.) `do` blocks in any monad other than `Id`. (`for x in l` and
  `for h : x in l` over a list are translated, as `List.foldl`: see
  `TermTests/ToTermTest/ForList.lean`; `break`, and an early `return` from inside a loop, are translated by folding the
  step `ForInStep β`: see `TermTests/ToTermTest/ForBreak.lean` and
  `TermTests/ToTermTest/ForReturn.lean`; `while`, `repeat` and `repeat … until` are
  translated when they are structural recursions — a `Nat` counter going down by one
  under a test that it is not `0`, or up by one below a bound the loop does not change —
  and rejected otherwise: see `TermTests/ToTermTest/While.lean`.)
- `List.pmap`, and `attach` / `attachWith` on anything but a `List`, are not translated.
  (`Subtype`, `List.attach` and `List.attachWith` are: a subtype has the tree of its
  values, see `TermTests/ToTermTest/ListLibrary.lean`.)

## 5. Correctness guarantees

- **No proof that `#leanscript_to_term` is correct.** The output has the right *type*,
  because `Term` is intrinsically typed. Its *value* is only checked on examples
  (`kernel_rfl`, `decide +kernel`, `rfl` in the tests). No translation-validation theorem
  `Term.run … foo_term = foo` is generated (§A1).
- `TermTests/NormalizeTest.lean` shows that normalization preserves six specific terms,
  not the normalizer in general.

## 6. Backend

- **There is no JavaScript backend or printer.** `LeanScript/LeanPrimTy.lean` and
  `LeanScript/Expr/Design.lean` describe a later stage (`MoreJsTy`, printing `Thunk` as
  memoised JS, `UInt53` vs `bigint`, …), but none of it exists in the code. A
  `TODO` in `LeanPrimTy.lean` also leaves open whether there should be an optimisation
  pass at that stage.

## 7. Engineering and housekeeping

- **`lake-manifest.json` has no Mathlib entry** even though `lakefile.toml` requires it,
  so a fresh checkout needs `lake update mathlib` before it builds.
- **No CI** (there is no `.github/` workflow) (§D1). There is no test that the import graph
  has no cycles or umbrella modules (§D3), and there is no `#guard_msgs` test for every
  `throwError` in `LeanScript/ToTerm` (§D5).
- `LeanScript/Expr/Term.lean` is still about 1150 lines long (§D2). It is one `mutual`
  block, and Lean needs a `mutual` block to be in a single file, so it can only get shorter
  by changing the grammar (e.g. build-speed proposal 3 below).
- Build-speed proposals that were not done (`proposals/BuildSpeedResults.md`, *Not
  implemented*):
  - 3: one indexed inductive instead of the `mutual` block (left out at your request);
  - 2c: merging the light test files;
  - 4b / 4c: `#guard` samples and smaller bounds (not done, at your request).
- Small `TODO`s in code:
  - `NonEmpty/String/Basic.lean`: `CoeOut NonEmptyString String` is commented out because
    it breaks `++`;
  - `LeanScript/LeanPrimTy.lean:136`: a name should be built as `recTaggedUnion`.
- The design notes are spread over `docs/`, `proposals/` and `LeanScript/Ty/README.md`,
  and some of them are stale (§D4). For example, the status note of
  `proposals/RecTaggedUnionEvalProposal.md` points to `LeanScript/Den/Cont.lean`, which no
  longer exists, and `proposals/ImprovementProposals.md` says that none of its items is
  implemented.
