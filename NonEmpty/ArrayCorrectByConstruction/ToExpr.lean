module
public import Lean.ToExpr
import Lean
public import NonEmpty.ArrayCorrectByConstruction.Basic
public import NonEmpty.ArrayCorrectByConstruction.Ops
public import NonEmpty.ArrayCorrectByConstruction.Instances
public import NonEmpty.ArrayCorrectByConstruction.Notation

open Lean Meta Elab

@[expose] public section

@[default_instance]
instance instToExprNonEmptyArrayCBC {α : Type u} [ToLevel.{u}] [ToExpr α] : ToExpr (NonEmpty.ArrayCorrectByConstruction.NonEmptyArray α) :=
  let type := toTypeExpr α
  let level := toLevel.{u}
  { toExpr := fun
      | ⟨hd, tl⟩ =>
        mkApp3 (mkConst ``NonEmpty.ArrayCorrectByConstruction.NonEmptyArray.mk [level]) type (toExpr hd) (toExpr tl),
    toTypeExpr := mkApp (mkConst ``NonEmpty.ArrayCorrectByConstruction.NonEmptyArray [level]) type }
