module

public import LeanScript.Term.Optimize.CondJump
public import LeanScript.Term.Optimize.CountJoinCtor
public import LeanScript.Term.Optimize.CountSubst

@[expose] public section

set_option autoImplicit false

/-!
# The rewrites of `LeanScript.Term.Optimize.CondJump` never add calls

`Term.numCalls_condJump`: a substitution never adds calls (`Term.numCalls_subst`), a test whose
arms only jump becomes a jump, and a join point reached by one jump is replaced by its body.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

theorem Term.numCalls_shareSubst {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks}
    {js : JCtx ks} {ℓ : Nat} {o' : Lvl} (u : Usage1ω) (c : Comp Δ d Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') :
    (Term.shareSubst u c b).2.numCalls ≤ c.numCalls + b.numCalls := by
  cases c with
  | share n =>
      simp only [Term.shareSubst, Comp.numCalls]
      by_cases hc : (n.isCond = true ∧ (u = .one ∨ b.onlyScrut 0 = true))
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
        cases hs : b.subst (D' := d) KLRen.id (USub.cons ⟨_, .neu n⟩ (USub.ofRen ULRen.idL))
            JRen.id with
        | none => simp [Term.numCalls, Comp.numCalls]
        | some r => have := Term.numCalls_subst b hs; simp only; omega
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]; simp [Term.numCalls, Comp.numCalls]
  | _ => exact Nat.le_refl _

theorem Term.numCalls_condJumps {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} {ℓ : Nat} {o₁ o₂ : Lvl} (c : Neu Δ Φ Γ .bool ℓ) (t : Term Δ d Φ Γ τ js o₁)
    (e : Term Δ d Φ Γ τ js o₂) :
    (Term.condJumps c t e).2.numCalls ≤ t.numCalls + e.numCalls := by
  cases t <;> cases e <;> simp only [Term.condJumps, Term.numCalls, Branch.numCalls] <;>
    try omega
  split <;> simp [Term.numCalls, Branch.numCalls]

theorem Term.numCalls_bindParam {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks}
    {js : JCtx ks} {o o' : Lvl} (uₓ : Usage01ω) (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o)
    (a : PExpr Δ Φ Γ σ o') {r : (o'' : Lvl) × Term Δ d Φ Γ τ js o''}
    (h : Term.bindParam uₓ body a = some r) : r.2.numCalls ≤ body.numCalls := by
  unfold Term.bindParam at h
  split at h
  · exact Term.numCalls_subst body h
  · cases a with
    | neu n =>
        cases uₓ with
        | zero => simp [Term.bindShare] at h
        | one =>
            simp only [Term.bindShare, Option.some.injEq] at h; subst h
            simp [Term.numCalls, Comp.numCalls]
        | many =>
            simp only [Term.bindShare, Option.some.injEq] at h; subst h
            simp [Term.numCalls, Comp.numCalls]
    | _ => cases h

theorem Branch.numCalls_joinJump {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} {o : Lvl} {ℓ : Nat} (σ : Ty ks) (u : Usage1ω) (uₓ : Usage01ω)
    (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o) (main : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ)
    (m : (o' : Lvl) × Term Δ d Φ Γ τ (⟨σ, u⟩ :: js) o') (hm : m.2.numCalls ≤ main.numCalls) :
    (Branch.joinJump σ u uₓ body main m).2.numCalls ≤ body.numCalls + main.numCalls := by
  obtain ⟨o', t⟩ := m
  cases t with
  | branch br =>
      simp only [Branch.joinJump, Term.numCalls, Branch.numCalls] at hm ⊢; omega
  | jump j a =>
      cases j with
      | head =>
          simp only [Branch.joinJump, JVar.split]
          cases hr : Term.bindParam uₓ body a with
          | some r =>
              show r.2.numCalls ≤ _
              have := Term.numCalls_bindParam uₓ body a hr
              omega
          | none =>
              show (Term.branch (Branch.join σ u uₓ body main)).numCalls ≤ _
              simp [Term.numCalls, Branch.numCalls]
      | tail j' =>
          show 0 ≤ _
          omega
  | _ => simp [Branch.joinJump, Term.numCalls, Branch.numCalls]

mutual
theorem Val.numCalls_cjWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → v.cjWalk.numCalls ≤ v.numCalls
  | _, _, _, _, _, .lam b => by simp only [Val.cjWalk, Val.numCalls]; exact Body.numCalls_cjWalk b
  | _, _, _, _, _, .thunk_mk b => by
      simp only [Val.cjWalk, Val.numCalls]; exact Body.numCalls_cjWalk b
  | _, _, _, _, _, .lazy_mk b => by
      simp only [Val.cjWalk, Val.numCalls]; exact Body.numCalls_cjWalk b
  | _, _, _, _, _, .record_mk _ => Nat.le_refl _
  | _, _, _, _, _, .union_mk _ _ => Nat.le_refl _
  | _, _, _, _, _, .array_mk _ => Nat.le_refl _
  | _, _, _, _, _, .list_mk _ => Nat.le_refl _
  | _, _, _, _, _, .data_in _ _ _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
theorem Body.numCalls_cjWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → b.cjWalk.numCalls ≤ b.numCalls
  | _, _, _, _, _, _, .closed t => by
      simp only [Body.cjWalk, Body.numCalls]; exact Term.numCalls_cjWalk t
  | _, _, _, _, _, _, .opened t _ => by
      simp only [Body.cjWalk, Body.numCalls]
      exact Term.numCalls_keepLvl t _ (Term.numCalls_cjWalk t)
  termination_by structural _ _ _ _ _ _ x => x
theorem Comp.numCalls_cjWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → c.cjWalk.numCalls ≤ c.numCalls
  | _, _, _, _, _, .app _ _ _ => Nat.le_refl _
  | _, _, _, _, _, .share _ => Nat.le_refl _
  | _, _, _, _, _, .nat_rec n z s _ => by
      simp only [Comp.cjWalk, Comp.numCalls]; exact Body.numCalls_cjWalk s
  | _, _, _, _, _, .array_foldl a z s _ => by
      simp only [Comp.cjWalk, Comp.numCalls]; exact Body.numCalls_cjWalk s
  | _, _, _, _, _, .data_rec b ρt us brs j e _ => by
      simp only [Comp.cjWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_cjWalk (brs i))
  | _, _, _, _, _, .data_brec b ρt k us brs j e _ => by
      simp only [Comp.cjWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_cjWalk (brs i))
  | _, _, _, _, _, .thunk_force _ => Nat.le_refl _
  | _, _, _, _, _, .lazy_force _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
theorem Term.numCalls_cjWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → t.cjWalk.2.numCalls ≤ t.numCalls
  | _, _, _, _, _, _, .ret _ => Nat.le_refl _
  | _, _, _, _, _, _, .letV u v b => by
      have hv := Val.numCalls_cjWalk v
      have hb := Term.numCalls_cjWalk b
      simp only [Term.cjWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .letE u c b => by
      have hc := Comp.numCalls_cjWalk c
      have hb := Term.numCalls_cjWalk b
      have h := Term.numCalls_shareSubst u c.cjWalk b.cjWalk.2
      simp only [Term.cjWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .record_casesOn us n b => by
      simp only [Term.cjWalk, Term.numCalls]; exact Term.numCalls_cjWalk b
  | _, _, _, _, _, _, .branch br => by
      simp only [Term.cjWalk, Term.numCalls]; exact Branch.numCalls_cjWalk br
  | _, _, _, _, _, _, .jump _ _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ _ x => x
theorem Branch.numCalls_cjWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) →
    br.cjWalk.2.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, .ite c t e => by
      have h₁ := Term.numCalls_cjWalk t
      have h₂ := Term.numCalls_cjWalk e
      have h := Term.numCalls_condJumps c t.cjWalk.2 e.cjWalk.2
      simp only [Branch.cjWalk, Branch.numCalls]; omega
  | _, _, _, _, _, _, .enum_casesOn e bs => by
      simp only [Branch.cjWalk, Term.numCalls, Branch.numCalls]
      exact Fin.sumNat_le _ (fun i => Term.numCalls_cjWalk (bs i))
  | _, _, _, _, _, _, .union_casesOn e bs => by
      simp only [Branch.cjWalk, Term.numCalls, Branch.numCalls]
      exact Branches.numCalls_cjWalk bs
  | _, _, _, _, _, _, .join σ u uₓ body main => by
      have h₁ := Term.numCalls_cjWalk body
      have h₂ := Branch.numCalls_cjWalk main
      have h := Branch.numCalls_joinJump σ u uₓ body.cjWalk.2 main main.cjWalk h₂
      simp only [Branch.cjWalk, Branch.numCalls]; omega
  termination_by structural _ _ _ _ _ _ x => x
theorem Branches.numCalls_cjWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → br.cjWalk.2.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ => by
      have h₁ := Term.numCalls_cjWalk b₁
      have h₂ := Term.numCalls_cjWalk b₂
      simp only [Branches.cjWalk, Branches.numCalls]; omega
  | _, _, _, _, _, _, _, _, .cons us b bs => by
      have h₁ := Term.numCalls_cjWalk b
      have h₂ := Branches.numCalls_cjWalk bs
      simp only [Branches.cjWalk, Branches.numCalls]; omega
  termination_by structural _ _ _ _ _ _ _ _ x => x
end

/-- **The rewrites of `Term.condJump` never add calls.** -/
theorem Term.numCalls_condJump {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} {o : Lvl} (t : Term Δ d Φ Γ τ js o) : t.condJump.numCalls ≤ t.numCalls :=
  Term.numCalls_keepLvl t _ (Term.numCalls_cjWalk t)

end LeanScript

end
