/-! Probe for proposals/DeduplicationProposal.md, section 8 (what cannot be done).
Plain Lean 4.34.0.  Expected: FAILS: DecidableEq and ReflBEq cannot be derived
for a nested inductive, so the hand-written `Ty.beq` stays. -/

structure Two (α : Type) where
  a : α
  b : List α
  deriving DecidableEq, BEq
inductive T where
  | leaf : Nat → T
  | node : Two T → T
  | many : List (List T) → T
  deriving DecidableEq
#print axioms instDecidableEqT
example : (T.node ⟨.leaf 1, [.leaf 2]⟩ = T.node ⟨.leaf 1, [.leaf 2]⟩) := by decide
inductive U where
  | leaf : Nat → U
  | node : Two U → U
  deriving BEq, ReflBEq, LawfulBEq
