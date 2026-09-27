module

public import LeanScript.Term.StepRename

@[expose] public section

set_option autoImplicit false

/-!
# Inverting a step

`Term.StepInv t t₂` lists, by the shape of `t`, the ways in which `t` can step to `t₂`, and
`Term.Step.inv` proves that every step is one of them (the same for every layer).  Case
analysis on a step through `inv` avoids unifying the level indices of `Term`, which are
computed (`Lvl.meet`, `Lvl.meetL`) and so cannot be unified by `cases`.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-- The steps out of a value. -/
def Val.StepInv : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ τ o → Val Δ d Φ Γ τ o → Prop
  | _, _, _, _, _, .lam b, v₂ => ∃ b', Body.Step b b' ∧ v₂ = .lam b'
  | _, _, _, _, _, .thunk_mk b, v₂ => ∃ b', Body.Step b b' ∧ v₂ = .thunk_mk b'
  | _, _, _, _, _, .lazy_mk b, v₂ => ∃ b', Body.Step b b' ∧ v₂ = .lazy_mk b'
  | _, _, _, _, _, _, _ => False

/-- The steps out of a body. -/
def Body.StepInv : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Body Δ d Φ Γ bs τ o → Body Δ d Φ Γ bs τ o → Prop
  | _, _, _, _, _, _, .closed t, b₂ => ∃ t', Term.Step t t' ∧ b₂ = .closed t'
  | _, _, _, _, _, _, .opened t h, b₂ => ∃ t', Term.Step t t' ∧ b₂ = .opened t' h

/-- The steps out of a computation. -/
def Comp.StepInv : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    Comp Δ d Φ Γ τ ℓ → Comp Δ d Φ Γ τ ℓ → Prop
  | _, _, _, _, _, .nat_rec n z s h, c₂ => ∃ s', Body.Step s s' ∧ c₂ = .nat_rec n z s' h
  | _, _, _, _, _, .array_foldl a z s h, c₂ => ∃ s', Body.Step s s' ∧ c₂ = .array_foldl a z s' h
  | _, _, _, _, _, .data_rec b ρ us brs j e h, c₂ => ∃ brs' i, Body.Step (brs i) (brs' i) ∧
      (∀ i', i' ≠ i → brs' i' = brs i') ∧ c₂ = .data_rec b ρ us brs' j e h
  | _, _, _, _, _, .data_brec b ρ k us brs j e h, c₂ => ∃ brs' i, Body.Step (brs i) (brs' i) ∧
      (∀ i', i' ≠ i → brs' i' = brs i') ∧ c₂ = .data_brec b ρ k us brs' j e h
  | _, _, _, _, _, _, _ => False

/-- The steps out of a statement. -/
def Term.StepInv : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {o : Lvl} → Term Δ d Φ Γ τ js o → Term Δ d Φ Γ τ js o → Prop
  | _, _, _, _, _, _, .ret _, _ => False
  | _, _, _, _, _, _, .letV u v b, t₂ =>
      (∃ b', b.rename KRen.drop URen.id JRen.id = some b' ∧ ∃ ho, t₂ = b'.castLvl ho) ∨
      (∃ v', Val.Step v v' ∧ t₂ = .letV u v' b) ∨
      (∃ b', Term.Step b b' ∧ t₂ = .letV u v b')
  | d, _, Γ, _, js, _, .letE (σ := σ) (ℓ := ℓ) u c b, t₂ =>
      (∃ b', b.rename KRen.id URen.drop JRen.id = some b' ∧ ∃ ho, t₂ = b'.castLvl ho) ∨
      (∃ x : UVar Γ σ ℓ, ∃ hl : ℓ = d, c = .share (.var x) ∧
        ∃ b', b.rename KRen.id (URen.subst x hl) JRen.id = some b' ∧ ∃ ho, t₂ = b'.castLvl ho) ∨
      (∃ n, ∃ hl : ℓ = d, ∃ e, c = .share n ∧ b = .ret e ∧
        ∃ e', PExpr.substHead n hl e = some e' ∧ ∃ ho, t₂ = (Term.ret e').castLvl ho) ∨
      (∃ n, ∃ hl : ℓ = d, ∃ σ' : Ty ks, ∃ j : JVar js σ', ∃ e, c = .share n ∧ b = .jump j e ∧
        ∃ e', PExpr.substHead n hl e = some e' ∧ ∃ ho, t₂ = (Term.jump j e').castLvl ho) ∨
      (∃ c', Comp.Step c c' ∧ t₂ = .letE u c' b) ∨
      (∃ b', Term.Step b b' ∧ t₂ = .letE u c b')
  | _, _, _, _, _, _, .record_casesOn us n b, t₂ =>
      (∃ b', b.rename KRen.id (URen.dropN _) JRen.id = some b' ∧ ∃ ho, t₂ = b'.castLvl ho) ∨
      (∃ b', Term.Step b b' ∧ t₂ = .record_casesOn us n b')
  | _, _, _, _, _, _, .branch br, t₂ => ∃ br', Branch.Step br br' ∧ t₂ = .branch br'
  | _, _, _, _, _, _, .jump _ _, _ => False

/-- The steps out of a branch. -/
def Branch.StepInv : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → Branch Δ d Φ Γ τ js ℓ → Prop
  | _, _, _, _, _, _, .ite c t e, b₂ =>
      (∃ t', Term.Step t t' ∧ b₂ = .ite c t' e) ∨ (∃ e', Term.Step e e' ∧ b₂ = .ite c t e')
  | _, _, _, _, _, _, .enum_casesOn e bs, b₂ => ∃ bs' i, Term.Step (bs i) (bs' i) ∧
      (∀ i', i' ≠ i → bs' i' = bs i') ∧ b₂ = .enum_casesOn e bs'
  | _, _, _, _, _, _, .union_casesOn e brs, b₂ =>
      ∃ brs', Branches.Step brs brs' ∧ b₂ = .union_casesOn e brs'
  | _, _, _, _, _, _, .join σ u uₓ body main, b₂ =>
      (∃ main', main.rename KRen.id URen.id JRen.drop = some main' ∧
        ∃ ho, b₂ = main'.castLvl ho) ∨
      (∃ body', Term.Step body body' ∧ b₂ = .join σ u uₓ body' main) ∨
      (∃ main', Branch.Step main main' ∧ b₂ = .join σ u uₓ body main')

/-- The steps out of the branches of a union's case analysis. -/
def Branches.StepInv : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → Branches Δ d Φ Γ cs τ js o → Prop
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, x =>
      (∃ b₁', Term.Step b₁ b₁' ∧ x = .two us₁ us₂ b₁' b₂) ∨
      (∃ b₂', Term.Step b₂ b₂' ∧ x = .two us₁ us₂ b₁ b₂')
  | _, _, _, _, _, _, _, _, .cons us b brs, x =>
      (∃ b', Term.Step b b' ∧ x = .cons us b' brs) ∨
      (∃ brs', Branches.Step brs brs' ∧ x = .cons us b brs')

theorem Val.Step.inv {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl}
    {v v₂ : Val Δ d Φ Γ τ o} (h : Val.Step v v₂) : Val.StepInv v v₂ := by
  cases h with
  | lam h => exact ⟨_, h, rfl⟩
  | thunk_mk h => exact ⟨_, h, rfl⟩
  | lazy_mk h => exact ⟨_, h, rfl⟩

theorem Body.Step.inv {d : Nat} {Φ : KCtx ks} {Γ bs : UCtx ks} {τ : Ty ks} {o : Lvl}
    {b b₂ : Body Δ d Φ Γ bs τ o} (h : Body.Step b b₂) : Body.StepInv b b₂ := by
  cases h with
  | closed h => exact ⟨_, h, rfl⟩
  | opened _ h => exact ⟨_, h, rfl⟩

theorem Comp.Step.inv {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat}
    {c c₂ : Comp Δ d Φ Γ τ ℓ} (h : Comp.Step c c₂) : Comp.StepInv c c₂ := by
  cases h with
  | nat_rec _ _ _ h => exact ⟨_, h, rfl⟩
  | array_foldl _ _ _ h => exact ⟨_, h, rfl⟩
  | data_rec _ _ _ _ _ _ i h hs => exact ⟨_, i, h, hs, rfl⟩
  | data_brec _ _ _ _ _ _ _ i h hs => exact ⟨_, i, h, hs, rfl⟩

theorem Term.Step.inv {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {o : Lvl} {t t₂ : Term Δ d Φ Γ τ js o} (h : Term.Step t t₂) : Term.StepInv t t₂ := by
  cases h with
  | letV_drop _ _ hb ho => exact Or.inl ⟨_, hb, ho, rfl⟩
  | letE_drop _ _ hb ho => exact Or.inl ⟨_, hb, ho, rfl⟩
  | copy _ x hl hb ho => exact Or.inr (Or.inl ⟨x, hl, rfl, _, hb, ho, rfl⟩)
  | share_ret _ n hl he ho => exact Or.inr (Or.inr (Or.inl ⟨n, hl, _, rfl, rfl, _, he, ho, rfl⟩))
  | share_jump _ n hl j he ho =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hl, _, j, _, rfl, rfl, _, he, ho, rfl⟩)))
  | casesOn_drop _ _ hb ho => exact Or.inl ⟨_, hb, ho, rfl⟩
  | letV_val _ _ h => exact Or.inr (Or.inl ⟨_, h, rfl⟩)
  | letV_body _ _ h => exact Or.inr (Or.inr ⟨_, h, rfl⟩)
  | letE_comp _ _ h => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, h, rfl⟩))))
  | letE_body _ _ h => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, h, rfl⟩))))
  | casesOn_body _ _ h => exact Or.inr ⟨_, h, rfl⟩
  | branch h => exact ⟨_, h, rfl⟩

theorem Branch.Step.inv {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {ℓ : Nat} {b b₂ : Branch Δ d Φ Γ τ js ℓ} (h : Branch.Step b b₂) : Branch.StepInv b b₂ := by
  cases h with
  | join_drop _ _ _ _ hm ho => exact Or.inl ⟨_, hm, ho, rfl⟩
  | ite_then _ _ h => exact Or.inl ⟨_, h, rfl⟩
  | ite_else _ _ h => exact Or.inr ⟨_, h, rfl⟩
  | enum_casesOn _ i h hs => exact ⟨_, i, h, hs, rfl⟩
  | union_casesOn _ h => exact ⟨_, h, rfl⟩
  | join_body _ _ _ _ h => exact Or.inr (Or.inl ⟨_, h, rfl⟩)
  | join_main _ _ _ _ h => exact Or.inr (Or.inr ⟨_, h, rfl⟩)

theorem Branches.Step.inv {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool}
    {cs : Ctors ks bs} {τ : Ty ks} {js : JCtx ks} {o : Lvl} {b b₂ : Branches Δ d Φ Γ cs τ js o}
    (h : Branches.Step b b₂) : Branches.StepInv b b₂ := by
  cases h with
  | two_left _ _ _ h => exact Or.inl ⟨_, h, rfl⟩
  | two_right _ _ _ h => exact Or.inr ⟨_, h, rfl⟩
  | cons_head _ _ h => exact Or.inl ⟨_, h, rfl⟩
  | cons_tail _ _ h => exact Or.inr ⟨_, h, rfl⟩

end LeanScript

end
