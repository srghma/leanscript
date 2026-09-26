import Lean

/-! Probe for proposals/DeduplicationProposal.md, section 6.
Plain Lean 4.34.0.  Expected: `NEL` (fields `α`, `List α`) derives `ToExpr`; `NES`
(which has a proof field) FAILS, so `NonEmptyString`'s hand-written instance stays. -/

open Lean
structure NEL (α : Type u) where
  head : α
  tail : List α
  deriving ToExpr
structure NES where
  toString : String
  isNonEmpty : toString ≠ "" := by decide
  deriving ToExpr
