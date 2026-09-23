module

public import LeanScript.Den
public import LeanScript.LeanInitPureExterns

@[expose] public section

set_option autoImplicit false

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

namespace LeanScript

/-!
# The externs of `Init`, as terms of the language

`LeanScript.LeanInitPureExtern` is written against an abstract type language `MyTy` with a
denotation `denote : MyTy → Type`.  This module instantiates it at the types of the
language, `LeanScript.TyWf`, with the evaluator's denotation `LeanScript.TyWf.Den`; the result,
`LeanScript.Extern`, is what `LeanScript.Term.extern` holds.

The catalogue asks for a few type formers the language does not have as primitives; each
is one of the shapes it does have:

| catalogue      | here                                                              |
| :------------- | :---------------------------------------------------------------- |
| `list α`       | `TyWf.array α` — an array denotes a `List`                         |
| `option α`     | the tagged union `none \| some α` (`TyWf.option`)                  |
| `prod α β`     | the record with the two fields `α`, `β` (`TyWf.prod`)              |
| `ordering`     | the enum with three constructors `lt`, `eq`, `gt` (`TyWf.ordering`)|

The three coercions the catalogue expects (from `LeanPrimTy`, from a covariant wrapper of a
`LeanPrimTy`, and from a covariant wrapper of a type of the language) are instances below.
-/

namespace TyWf

/-- A covariant wrapper (array, thunk or lazy value) of a type of the language. -/
@[reducible] def primCovariant : LeanPrimTyCovariant TyWf → TyWf
  | .array a => TyWf.array a
  | .thunk a => TyWf.thunk a
  | .lazy a => TyWf.lazy a

/-- `Option α`: the tagged union whose constructor `0` (`none`) has no field and whose
    constructor `1` (`some`) has one field of type `α`. -/
@[reducible] def option (α : TyWf) : TyWf :=
  TyWf.taggedUnion (.skip (.here ⟨α, []⟩ []))

/-- `List α`: an array, which denotes a `List`. -/
@[reducible] def list (α : TyWf) : TyWf := TyWf.array α

/-- `α × β`: the record of the two fields `α` and `β`, in that order. -/
@[reducible] def prod (α β : TyWf) : TyWf := TyWf.record ⟨α, β, []⟩

/-- `Ordering`: the enum with the three constructors `lt`, `eq` and `gt`, numbered
    `0`, `1`, `2` like the constructors of `Ordering`. -/
@[reducible] def ordering : TyWf := TyWf.enum {}

end TyWf

instance instCoeLeanPrimTyTyWf : Coe LeanPrimTy TyWf := ⟨TyWf.prim⟩

instance instCoePrimCovariantLeanPrimTyTyWf : Coe (LeanPrimTyCovariant LeanPrimTy) TyWf :=
  ⟨fun c => TyWf.primCovariant (c.map TyWf.prim)⟩

instance instCoePrimCovariantTyWf : Coe (LeanPrimTyCovariant TyWf) TyWf :=
  ⟨TyWf.primCovariant⟩

/-- A pure extern of `Init`, applied to all of its arguments, whose result has type `τ`:
    `LeanScript.LeanInitPureExtern` at the types of the language and their values. -/
abbrev Extern : TyWf → Type :=
  LeanInitPureExtern TyWf.Den TyWf.option TyWf.list TyWf.prod TyWf.ordering

/-! ## Values of the derived type formers

`TyWf.option`, `TyWf.prod` and `TyWf.ordering` are shapes of the language, so their values
are the values of those shapes; these functions build them from the Lean values. -/

/-- The value of `TyWf.option α` a Lean `Option` stands for. -/
def TyWf.Den.ofOption {α : TyWf} : Option α.Den → (TyWf.option α).Den
  | none => ⟨⟨0, Nat.zero_lt_succ 1⟩, PUnit.unit⟩
  | some a => ⟨⟨1, Nat.lt_succ_self 1⟩, (a, PUnit.unit)⟩

/-- The value of `TyWf.prod α β` a Lean pair stands for. -/
def TyWf.Den.ofProd {α β : TyWf} : α.Den × β.Den → (TyWf.prod α β).Den
  | (a, b) => (a, b, PUnit.unit)

/-- The value of `TyWf.ordering` a Lean `Ordering` stands for. -/
def TyWf.Den.ofOrdering : Ordering → TyWf.ordering.Den
  | .lt => ⟨0, by decide⟩
  | .eq => ⟨1, by decide⟩
  | .gt => ⟨2, by decide⟩

end LeanScript

end
