module

public import LeanScript.Expr.Term
public import LeanScript.Eval

/-!
# Which terms does the evaluator evaluate?

`Term.eval` is total on the terms that satisfy `Term.NoRecMk` — the terms that build no
value of a recursive **record**, recursive **newtype** or **mutual family** — and on
nothing else.  A recursive *tagged union* has values in the model (a W-tree of its
constructors), so its introduction form is inside the fragment.  This file checks, with
the kernel, that

* a closed term such as `natNil` (the empty list of naturals) **does** satisfy
  `Term.NoRecMk`, and the evaluator runs it and the eliminators applied to it: `natHead`
  and `natFoldZero` are now told apart;
* the restriction that remains is real and cannot be lifted without changing the model
  `TyWf.Den`: a recursive record denotes an **empty** type, so *no* function whatsoever
  — not just this evaluator — can send every closed term to a value of its type.
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

/-- `[5]`. -/
def natFive : Term covEmptySig [] natListTy :=
  .recTaggedUnion_mk natListSchema (t := 1) (fields := .cons (.nat_mk 5) (.cons natNil .nil))

/-! The four statements below held when a recursive tagged union denoted `PEmpty`.  They
are **false** now that it denotes the W-tree of its constructors: `natNil` is inside the
fragment, `natListTy` has values, and `natHead` and `natFoldZero` differ on `[5]`.  They
are kept, commented out, as the record of what changed.

```
theorem natNil_not_noRecMk : ¬ Term.NoRecMk natNil := fun h => h
theorem natListTy_den_empty : TyWf.Den natListTy → False := fun v => PEmpty.elim v
theorem den_fun_natList_subsingleton (f g : TyWf.Den (natListTy ⇒ TyWf.prim .nat)) :
    f = g := funext fun v => PEmpty.elim v
theorem run_natHead_eq_run_natFoldZero :
    Term.run (Sg := covEmptySig) GlobalEnv.nil natHead =
      Term.run (Sg := covEmptySig) GlobalEnv.nil natFoldZero
```
-/

/-- The empty list of naturals is inside the evaluator's fragment. -/
theorem natNil_noRecMk : Term.NoRecMk natNil := by no_rec_mk

/-- The head of `[5]` is `5`. -/
theorem run_natHead_natFive :
    Term.run (Sg := covEmptySig) GlobalEnv.nil (.ap natHead natFive) = 5 := by decide

/-- The head of a list and the fold that answers `0` are told apart, on `[5]`. -/
theorem run_natHead_ne_run_natFoldZero :
    Term.run (Sg := covEmptySig) GlobalEnv.nil (.ap natHead natFive) ≠
      Term.run (Sg := covEmptySig) GlobalEnv.nil (.ap natFoldZero natFive) := by decide

/-- A rose tree: a label and an array of subtrees — a recursive **record**. -/
def roseSchema : LeanRecordSchema (TyWfIn 1) :=
  ⟨(Ty.prim .nat).toTyWfIn, (Ty.array Ty.self).toTyWfIn, []⟩

/-- The type of a rose tree. -/
def roseTy : TyWf := .recObject roseSchema

/-- A leaf: the label `1` and no children. -/
def roseLeaf : Term covEmptySig [] roseTy :=
  .recObject_mk roseSchema (fields := .cons (.nat_mk 1) (.cons (.array_mk .nil) .nil))

/-- A leaf is outside the evaluator's fragment. -/
theorem roseLeaf_not_noRecMk : ¬ Term.NoRecMk roseLeaf := fun h => h

/-- A rose tree — a recursive record — has no value in the model. -/
theorem roseTy_den_empty : TyWf.Den roseTy → False := fun v => PEmpty.elim v

/-- **No evaluator into `TyWf.Den` can evaluate every closed term**: there is no function
    at all giving each closed term of the empty signature a value of its type, since
    `roseLeaf` would need a value of the empty type `TyWf.Den roseTy`. -/
theorem no_total_evaluator (ev : ∀ τ : TyWf, Term covEmptySig [] τ → TyWf.Den τ) :
    False :=
  roseTy_den_empty (ev _ roseLeaf)

end TyTests
