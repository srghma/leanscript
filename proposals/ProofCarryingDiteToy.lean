/-
Toy model for `proposals/ProofCarryingDiteProposal.md` (not part of the Lake build; it has no
imports). Check it with the plain compiler:

    lean proposals/ProofCarryingDiteToy.lean

It shows that a context of *closed* hypotheses `Δ`, a `guard` node that pushes one, and an
`externHyp` node that hands the stored proof to an extern all typecheck, and that
evaluation works (`decide +kernel`).
-/

inductive Ty | nat | arr | bool
abbrev Ty.Den : Ty → Type | .nat => Nat | .arr => Array Nat | .bool => Bool
abbrev DenList : List Ty → Type | [] => PUnit | t :: ts => t.Den × DenList ts
structure Hyp where
  σs : List Ty
  prop : DenList σs → Prop
abbrev HEnv : List Hyp → Type | [] => PUnit | H :: Δ => {vs : DenList H.σs // H.prop vs} × HEnv Δ
inductive Var : List Ty → Ty → Type | z {Γ τ} : Var (τ :: Γ) τ | s {Γ σ τ} : Var Γ τ → Var (σ :: Γ) τ
def Var.get : {Γ : List Ty} → {τ : Ty} → Var Γ τ → DenList Γ → τ.Den
  | _ :: _, _, .z, (v, _) => v | _ :: _, _, .s x, (_, e) => x.get e
inductive Extern : Ty → Type | fget (a : Array Nat) (i : Nat) (h : i < a.size) : Extern .nat
def Extern.eval {τ} : Extern τ → τ.Den | .fget a i h => a[i]
mutual
inductive Term : List Ty → List Hyp → Ty → Type 1
  | var {Γ Δ τ} : Var Γ τ → Term Γ Δ τ
  | lit {Γ Δ} : Nat → Term Γ Δ .nat
  | guard {Γ Δ σs τ} : Spine Γ Δ σs → (p : DenList σs → Prop) → (∀ vs, Decidable (p vs)) →
      Term Γ (⟨σs, p⟩ :: Δ) τ → Term Γ (⟨σs, fun vs => ¬ p vs⟩ :: Δ) τ → Term Γ Δ τ
  | externHyp {Γ Δ ρs τ} : Spine Γ Δ ρs → (HEnv Δ → DenList ρs → Extern τ) → Term Γ Δ τ
inductive Spine : List Ty → List Hyp → List Ty → Type 1
  | nil {Γ Δ} : Spine Γ Δ []
  | cons {Γ Δ σ σs} : Term Γ Δ σ → Spine Γ Δ σs → Spine Γ Δ (σ :: σs)
end
mutual
def Term.eval : {Γ : List Ty} → {Δ : List Hyp} → {τ : Ty} → Term Γ Δ τ → DenList Γ → HEnv Δ → τ.Den
  | _, _, _, .var x, env, _ => x.get env
  | _, _, _, .lit n, _, _ => n
  | _, _, _, .guard args p dec t e, env, henv =>
      let vs := Spine.eval args env henv
      if h : p vs then Term.eval t env (⟨vs, h⟩, henv) else Term.eval e env (⟨vs, h⟩, henv)
  | _, _, _, .externHyp args call, env, henv => Extern.eval (call henv (Spine.eval args env henv))
def Spine.eval : {Γ : List Ty} → {Δ : List Hyp} → {σs : List Ty} → Spine Γ Δ σs → DenList Γ → HEnv Δ → DenList σs
  | _, _, _, .nil, _, _ => PUnit.unit
  | _, _, _, .cons t ts, env, henv => (Term.eval t env henv, Spine.eval ts env henv)
end
-- fun a => if h : 1 < a.size then a[1] else 0
def ex : Term [.arr] [] .nat :=
  .guard (.cons (.lit 1) (.cons (.var .z) .nil)) (fun vs => vs.1 < vs.2.1.size) (fun _ => inferInstance)
    (.externHyp .nil (fun henv _ => .fget henv.1.1.2.1 henv.1.1.1 henv.1.2))
    (.lit 0)
example : ex.eval (#[5, 7, 9], ()) () = 7 := by decide +kernel
example : ex.eval (#[5], ()) () = 0 := by decide +kernel
-- else-branch with a derived proof: fun a => if h : a.size ≤ 1 then 0 else a[1]
def ex2 : Term [.arr] [] .nat :=
  .guard (.cons (.var .z) .nil) (fun vs => vs.1.size ≤ 1) (fun _ => inferInstance)
    (.lit 0)
    (.externHyp .nil (fun henv _ => .fget henv.1.1.1 1 (Nat.lt_of_not_le henv.1.2)))
example : ex2.eval (#[5, 7, 9], ()) () = 7 := by decide +kernel
