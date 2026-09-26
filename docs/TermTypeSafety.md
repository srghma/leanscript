# Type safety of the constructors of `Term` — an audit

This note records an audit of every constructor of `LeanScript.Term` (and of the branch
families it mentions) for *things a well-typed term can say that it should not be able
to say*.  It lists what was found, what was changed, and what was looked at and found
sound.  Three gaps were found and closed; the rest of the audit is a record of the
checks that passed.  Of the two residual items it described, the first has since been
closed — the grammar is now indexed by `LeanScript.TyWf`, a tree together with the proof
that it is a type — and that change is recorded below as well; the second is still
described precisely so it can be picked up if wanted.

Everything below is in `LeanScript/Expr/Term.lean` (at the time of writing,
`LeanScript/Expr.lean`, since split into `LeanScript/Expr/{Design,NatRecCtx,Term}.lean`)
unless another file is named, and the whole
project (`lake build`, 218 jobs, tests included) builds after the changes.

---

## 1. Fixed: a partial dispatch could name **every** constructor

**Before.**  `enum_casesOnWithDefault`, `taggedUnion_casesOnWithDefault`,
`recTaggedUnion_casesOnWithDefault` and `mutualRecursiveFamily_casesOnWithDefault` took a
branch list (`EnumSomeCases`, `TaggedUnionSomeCases`) whose type already guaranteed that
the constructor numbers strictly increase and that at least one is named.  Nothing
stopped the list from naming *all* of them, and then the default branch is unreachable:
the term is an exhaustive dispatch written the long way round, with a branch that the
evaluator can never take.

**After.**  Both branch lists carry a new index, the **number of branches** — `last`
gives `1` and `cons` gives one more than its tail — and each dispatch carries the bound
`k < n`, where `n` is the number of constructors the type has (`s.nOfConstructors`,
`l.length`, `(Ty.recTaggedUnionUnfold l).length`, `(Ty.famCtorsUnfold f l).length`).  So
a partial dispatch always leaves at least one constructor to its default, and a dispatch
that names them all has to be written as the exhaustive `xxx_casesOn` that it is.

The bound is the last argument of the constructor and its default is the new tactic
`ctor_lt` (`LeanScript/CtorTag.lean`), so nothing is written by hand: existing terms are
unchanged, and the count is inferred from the branch list.

`TermTests/TermTest.lean` pins both directions: naming two of the three constructors of
`natBoolNat` still elaborates, while naming all three constructors of the enum `three`,
or both constructors of the union `optNat`, does not.

## 2. Fixed: `EnumSomeCases` was indexed by a bare constructor count

**Before.**  `EnumSomeCases Sg Γ τ n` was indexed by a `Nat`, so a branch list written for
one enum was also a branch list for any other enum with the same number of constructors
— unlike `TaggedUnionSomeCases`, which is indexed by its schema.

**After.**  `EnumSomeCases Sg Γ τ s k` is indexed by the `LeanEnumSchema` itself, and a
branch names its constructor as a `Fin s.nOfConstructors`.  This matches `EnumCases`,
`TaggedUnionCases` and `TaggedUnionSomeCases`, all of which are indexed by the schema
they branch on.

## 3. Fixed: a recursive introduction form accepted a tree that is not a type

**Before.**  `recTaggedUnion_mk`, `recObject_mk`, `recAlias_mk` and
`mutualRecursiveFamily_mk` accepted *any* schema.  A `Ty` is a tree, and
`LeanScript.Ty.Wf` (in `LeanScript/Ty/Wf.lean`) is the proposition that a tree really is a
type; the grammar never asked for it, so all of the following were writable:

* a binder that mentions itself **nowhere** — a record or a union declared recursive that
  is not;
* a **non-positive** binder, `μX. (X ⇒ Nat) | …`, at which a term language diverges;
* an **uninhabited** binder, `μX. X`, and more generally any recursive record or newtype
  with a field written `Ty.self`, which states an equation such as `T = Nat × T` that no
  value satisfies;
* a family that names a member the family does not have.

**After.**  Each of the four carries `(hwf : Ty.Wf … := by ty_wf)` for the tree it builds a
value of.  The proof is written by the existing `ty_wf` tactic, so a schema written out
needs nothing by hand, and `#leanscript_to_term` (`LeanScript/ToTerm.lean`) writes it with
`Ty.mkWfProof`, the same derivation the tactic uses.

The **eliminators** deliberately do not carry it: a tree that is not a type has no value,
so there is nothing to take apart, and requiring the proof there would only make
unreachable code unwritable at the cost of the existing fold examples.

`TermTests/RecTermTest.lean` pins it: the uninhabited `cellTy` and a union that mentions
itself in the domain of a function are both refused, each with the tactic's own
explanation.

---

## What was checked and found sound

* **Every literal is a literal of its own type** — `bool_mk : Bool → Term Sg Γ (.prim
  .bool)` and so on for each leaf of `LeanPrimTy`; `bitvec_mk` carries the width's
  positivity (and proof irrelevance makes the type index independent of which proof), and
  `stringPos_mk` carries the string the position is into, because the type of a checked
  position names it.
* **A constructor number is a number with a proof.**  `taggedUnion_mk`,
  `recTaggedUnion_mk` and `FamilyMemberValue.ctors` state the bound against the schema's
  own `length`, and the fields are a `Spine` typed by *that constructor's* field types, so
  a constructor cannot be applied to the wrong fields and a tag cannot be out of range.
  An enum constructor is a `Fin s.nOfConstructors`.
* **A dispatch is exhaustive by construction.**  `TaggedUnionCases` /
  `CtorsWithPayloadCases` / `TaggedUnionCasesRest` mirror `LeanTaggedUnionSchema`,
  `EnumCases` mirrors `LeanEnumSchema`, `FamilyMemberCases` mirrors `LeanFamMemberSchema`
  and `FamilyFoldCases` / `FamilyFoldKCases` are indexed by `f.members`: none of them has
  a default branch or an early end.
* **A branch binds, it does not look up.**  Every `_casesOn` gives its branch the fields of
  the constructor it matched, as a context extension, so no field is ever fetched by index
  at run time.
* **A fold cannot recurse on anything it likes.**  `nat_rec`, `array_rec` and the four
  recursive `_rec`s *give* the branch the value at the smaller argument
  (`TyWf.recBinders` / `TyWf.famRecBinders`), so a term is terminating by construction.
* **Variables and globals are typed.**  `Γ ∋ τ` and `GlobalRef Sg.decls τ` are de Bruijn
  indices carrying the type they are bound at, so a term cannot name an undeclared global
  or use one at a type it does not have.
* **A partial dispatch is ordered and non-empty**, by the `lo` index and the `last`
  constructor — unchanged, and now also non-exhaustive (item 1).

## Since the audit: the grammar is indexed by a **type**, not by a tree

This was the first of the two residual items the audit recorded, and it has since been
closed.

**Before.**  `Term`, `Ctx` and the branch families were indexed by `Ty`.  `record_mk`,
`taggedUnion_mk` and `enum_mk` therefore accepted a schema whose fields may contain a free
occurrence leaf (`Ty.self`, `Ty.familyMember i`) — a tree that is not a type — and so did
the context and the type of a term.  No *closed* term was affected (an occurrence leaf
denotes `PEmpty`, so such a field can only be filled from a variable of that type, and a
closed term has none), but the rule "every type in a term is a type" was not stated
anywhere.

**After.**  `Term Sg : Ctx → TyWf → Type 1` and `Ctx = List TyWf`, where
`LeanScript.TyWf` (`LeanScript/Ty/TyWf.lean`) is a tree **together with** the proof that
it is a type of the language, and a payload written inside a binder is
`LeanScript.TyWfIn n` (`LeanScript/Ty/TyWfIn.lean`), the same bundle for the scope the
binder opens.  The schemas of the grammar are schemas of bundles — a record is a
`LeanRecordSchema TyWf`, the payload of a recursive union a
`LeanTaggedUnionSchema (TyWfIn 1)`, the members of a mutual family a
`LeanMutualRecFamily (TyWfIn (n + 2))` — and a type is built out of types by the bundled
constructors `TyWf.prim`, `TyWf.fn` (`⇒`), `TyWf.array`, `TyWf.thunk`, `TyWf.lazy`,
`TyWf.enum`, `TyWf.record`, `TyWf.taggedUnion`, each of which **composes** the proof out of
its arguments'.  So nothing is rechecked, nothing is carried twice, and no proof obligation
appears on a record, union or enum node.

A tree that is not a type indexes no term at all: it reaches an index only through
`Ty.toTyWf`, whose proof argument defaults to `by ty_wf`, and the tactic refuses it.
`TermTests/TermTest.lean` pins both halves — the theorems `type_of_term_is_wf` and
`ctx_of_term_is_wf` (the type of a term, and every type of its context, is well formed),
and two `#guard_msgs` tests that a free occurrence leaf and a non-positive binder are
refused at the index.

The four recursive introduction forms keep their `hwf` argument (item 3): being a *binder*
that describes a type is not a consequence of its payload being well formed in the scope it
opens, and that is exactly what `TyWf.recTaggedUnion`, `TyWf.recObject`, `TyWf.recAlias`
and `TyWf.mutualRecursiveFamily` ask for as well.

---

## Residual item, described but not changed

* **`TaggedUnionFoldCases` is indexed by an arbitrary function** `bind : List ι → List
  TyWf`.  This is not a hole in `Term`, which only ever instantiates it with
  `TyWf.recBinders …` or `TyWf.famRecBinders …`, but the family itself admits any
  reindexing of what a branch binds.  A small datatype with those two cases as its
  constructors would make the family say exactly what it means.

## One observation about the fold over a record or a newtype

`TyWf.recBinders` gives a branch the value of the fold right after a field that is literally
`Ty.self`.  For a **recursive record** or a **recursive newtype** a field that is literally
`Ty.self` makes the type uninhabited (`T = … × T × …`, or `T = T`), so with item 3 in place
those types have no introduction form at all: the extra binder of `recObject_rec` and
`recAlias_rec` is only ever there for a type with no values.  A reachable fold binder
needs alternatives, which is to say a **tagged union** — `recTaggedUnion_rec`, and a
`ctors` member of a mutual family — where another constructor provides the base case.
This is a property of the type language, not a defect of the grammar, and nothing was
changed for it.

### Update: the fold over a record now answers

The observation above still holds of `recAlias_rec`, and of `TyWf.recBinders`, which is
unchanged.  `recObject_rec` no longer uses it.  A recursive record's occurrences of itself
always sit inside another former, so its branch is given the answers in the **shape of the
record's own fields** — `TyWf.recObjectMap`, and at depth `k` the answer trees
`TyWf.recObjectAnswerTree` of the immediate subvalues, which carry the answers `k + 1`
levels down.  `LeanScript/RecObjectRecFacts.lean` proves that no field of a recursive
record is literally `Ty.self` (`Ty.ne_self_of_wf_recObject`), and therefore that the old
branch context was exactly the fields (`TyWf.recBinders_recObject`) and that the default
depth adds to it precisely the one answer it was missing
(`TyWf.recObjectRecBinders_zero`).  `TermTests/RecObjectRecDepthTest.lean` writes the `fib`
family against it, at depths zero to five.

### Update: the fold over a newtype now answers too

`TyWf.recBinders` is still unchanged, and `recAlias_rec` no longer uses it either.  The
body of a recursive newtype is never literally `Ty.self`, so its occurrences of itself sit
inside another former, and its branch is given the answers in the **shape of the body** —
`TyWf.recAliasMap`, and at depth `k` the answer trees `TyWf.recAliasAnswerTree` of the
immediate subvalues, which carry the answers `k + 1` levels down.
`LeanScript/RecAliasRecFacts.lean` proves that the body of a recursive newtype is not
`Ty.self` (`Ty.ne_self_of_wf_recAlias`), and therefore that the old branch context was
exactly the body (`TyWf.recBinders_recAlias`) and that the default depth adds to it
precisely the one answer it was missing (`TyWf.recAliasRecBinders_zero`).
`TermTests/RecAliasRecDepthTest.lean` writes the `fib` family against it, at depths zero to
five.

So `TyWf.recBinders` is now used only where a field can really be an occurrence: the fold
of a recursive tagged union and the fold of a mutual family (which uses its family-scoped
counterpart, `TyWf.famRecBinders`).

## Since then: the fold of a mutual family has a depth too

`LeanScript.Term.mutualRecursiveFamily_rec` now takes a depth `k` (defaulting to `0`) and
its branches are `LeanScript.FamilyFoldKCases`: a branch is either an answer, in the
context the plain fold gave it, or a **deeper look**, which names one of its constructor's
occurrences of a member (`LeanScript.FamilyMemberField`), says which member of the family
that is (`LeanScript.FamilyMemberAt`) and dispatches on *that* member — whichever one it
is — at a depth one smaller.  Every answer a branch receives is therefore still the answer
at a subvalue, and a term stays terminating by construction at every depth.
`LeanScript/FamilyRecFacts.lean` gives the two translations between the plain branches and
the depth-zero branches and proves them mutually inverse
(`FamilyFoldKCases.ofFoldK_toFoldK`, `FamilyFoldKCases.toFoldK_ofFoldK`, and the same for
the four auxiliary families), so the default depth changes nothing, and
`TermTests/FamilyRecDepthTest.lean` writes the `fib` family against it at depths zero to
five.
