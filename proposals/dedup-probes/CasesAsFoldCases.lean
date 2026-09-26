/-! Probe for proposals/DeduplicationProposal.md, section 4.
Plain Lean 4.34.0.  Expected: compiles with no errors.
A plain dispatch written as the fold-case family at `ι := Nat`, `bind := id`.
Branch lookup needs no cast. -/

mutual
inductive Term : List Nat → Nat → Type 1
  | var {Γ τ} : Term (τ :: Γ) τ
  | lit {Γ} : Nat → Term Γ 0
  | cases {Γ τ} (l : List (List Nat)) : FoldCases Nat id Γ l τ → Term Γ τ
  | fold {Γ τ} (l : List (List Nat)) (bind : List Nat → List Nat) : FoldCases Nat bind Γ l τ → Term Γ τ
inductive FoldCases : (ι : Type) → (List ι → List Nat) → List Nat → List (List ι) → Nat → Type 1
  | nil {ι bind Γ τ} : FoldCases ι bind Γ [] τ
  | cons {ι bind Γ τ fs rest} : Term (bind fs ++ Γ) τ → FoldCases ι bind Γ rest τ → FoldCases ι bind Γ (fs :: rest) τ
end
def pick : {Γ : List Nat} → {τ : Nat} → {l : List (List Nat)} → FoldCases Nat id Γ l τ → Nat → Option (Σ fs, Term (fs ++ Γ) τ)
  | _, _, _, .nil, _ => none
  | _, _, fs :: _, .cons t _, 0 => some ⟨fs, t⟩
  | _, _, _, .cons _ r, n+1 => pick r n
