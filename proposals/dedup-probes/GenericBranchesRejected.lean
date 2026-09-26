/-! Probe for proposals/DeduplicationProposal.md, section 4 (what cannot be done).
Plain Lean 4.34.0.  Expected: FAILS with a kernel error: nested inductive
parameters cannot contain local variables.  So one generic "branch per constructor"
family cannot replace the several families in Expr/Term.lean. -/

inductive Branches {ι : Type} (B : List ι → Type) : List (List ι) → Type
  | nil : Branches B []
  | cons {fs rest} : B fs → Branches B rest → Branches B (fs :: rest)

inductive Term : List Nat → Nat → Type
  | var {Γ τ} : Term (τ :: Γ) τ
  | cases {Γ τ} (l : List (List Nat)) : Branches (fun fs => Term (fs ++ Γ) τ) l → Term Γ τ
