module
public import Lean.ToExpr
import Lean
public import NonEmpty.ListCorrectByConstruction.Basic

open Lean Meta Elab

@[expose] public section

@[default_instance]
instance instToExprNonEmptyListCBC {α : Type u} [ToLevel.{u}] [ToExpr α] : ToExpr (NonEmpty.ListCorrectByConstruction.NonEmptyList α) :=
  let type := toTypeExpr α
  let level := toLevel.{u}
  { toExpr := fun
      | ⟨hd, tl⟩ =>
        mkApp3 (mkConst ``NonEmpty.ListCorrectByConstruction.NonEmptyList.mk [level]) type (toExpr hd) (toExpr tl),
    toTypeExpr := mkApp (mkConst ``NonEmpty.ListCorrectByConstruction.NonEmptyList [level]) type }
