module

public import LeanScript.Expr.Term
public import LeanScript.Eval

/-!
# Which terms does the evaluator evaluate?

`Term.eval` is total on the terms that satisfy `Term.NoRecMk` — the terms that build no
value of a recursive shape — and on nothing else.  This file checks, with the kernel,
that the restriction is real and cannot be lifted without changing the model
`TyWf.Den`:

* a closed term such as `natNil` (the empty list of naturals) does **not** satisfy
  `Term.NoRecMk`;
* the recursive type it has denotes an **empty** type, so *no* function whatsoever —
  not just this evaluator — can send every closed term to a value of its type;
* the eliminators of a recursive shape are accepted by `Term.run`, but the value they
  get is a function out of an empty type, so any two of them are equal: `natHead` and
  `natFoldZero` get the same value.
-/

namespace TyTests

open LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-- The empty signature. -/
def covEmptySig : Sig := ⟨[], by decide⟩

/-- `List Nat` as a recursive tagged union: `nil`, and `cons` of a natural and the list. -/
def natListSchema : LeanTaggedUnionSchema (TyWfIn 1) :=
  .skip (.here ⟨(Ty.prim .nat).toTyWfIn, [Ty.self.toTyWfIn]⟩ [])

/-- The type of a list of naturals. -/
def natListTy : TyWf := .recTaggedUnion natListSchema

/-- The empty list. -/
def natNil : Term covEmptySig [] natListTy :=
  .recTaggedUnion_mk natListSchema (t := 0) (fields := .nil)

/-- The head of a list, or `0`. -/
def natHead : Term covEmptySig [] (natListTy ⇒ TyWf.prim .nat) :=
  .lam (.recTaggedUnion_casesOn (.var (v♯0))
    (.skip (.nat_mk 0) (.here (.var (v♯0)) .nil)))

/-- The fold over a list that answers `0`. -/
def natFoldZero : Term covEmptySig [] (natListTy ⇒ TyWf.prim .nat) :=
  .lam (.recTaggedUnion_rec 0 (.var (v♯0))
    (.skip (.here (.nat_mk 0)) (.here (.here (.var (v♯2))) .nil)))

/-- The empty list of naturals is outside the evaluator's fragment. -/
theorem natNil_not_noRecMk : ¬ Term.NoRecMk natNil := fun h => h

/-- A list of naturals — a recursive tagged union — has no value in the model. -/
theorem natListTy_den_empty : TyWf.Den natListTy → False := fun v => PEmpty.elim v

/-- **No evaluator into `TyWf.Den` can evaluate every closed term**: there is no function
    at all giving each closed term of the empty signature a value of its type, since
    `natNil` would need a value of the empty type `TyWf.Den natListTy`. -/
theorem no_total_evaluator (ev : ∀ τ : TyWf, Term covEmptySig [] τ → TyWf.Den τ) :
    False :=
  natListTy_den_empty (ev _ natNil)

/-- The functions out of a recursive type all have the same value in the model. -/
theorem den_fun_natList_subsingleton (f g : TyWf.Den (natListTy ⇒ TyWf.prim .nat)) :
    f = g :=
  funext fun v => PEmpty.elim v

/-- So the evaluator does run the eliminators of a recursive shape, but cannot tell them
    apart: the head of a list and the fold that answers `0` get the same value. -/
theorem run_natHead_eq_run_natFoldZero :
    Term.run (Sg := covEmptySig) GlobalEnv.nil natHead =
      Term.run (Sg := covEmptySig) GlobalEnv.nil natFoldZero :=
  den_fun_natList_subsingleton _ _

end TyTests
