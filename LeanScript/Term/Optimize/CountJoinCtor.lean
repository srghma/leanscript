module

public import LeanScript.Term.Optimize.JoinCtor
public import LeanScript.Term.Optimize.OpenCall
public import LeanScript.Term.Optimize.CountInlineRet

@[expose] public section

set_option autoImplicit false

/-!
# Writing join points at their jumps, and inlining open closures, never add calls

`Term.numCalls_joinCtor`: a join point is only written at its jumps when the result has no more
calls than before (`Branch.joinCtor` checks it).  `Term.numCalls_openCall`: a call is replaced
by a shared neutral expression, which is not a call.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## `Term.joinCtor` -/

theorem Branch.numCalls_joinCtor {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} {o : Lvl} {ℓ : Nat} (σ : Ty ks) (u : Usage1ω) (uₓ : Usage01ω)
    (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o) (main : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ) :
    (Branch.joinCtor σ u uₓ body main).2.numCalls ≤ body.numCalls + main.numCalls := by
  unfold Branch.joinCtor
  cases body.caseJoin? with
  | none => exact Nat.le_refl _
  | some C =>
      simp only
      cases (main.jcRepl C JPos.init).2.rename KRen.id URen.id JRen.drop with
      | none => exact Nat.le_refl _
      | some b =>
          simp only
          by_cases hn : b.numCalls ≤ body.numCalls + main.numCalls
          · rw [ite_eq_left_of_eq_true _ _ (eq_true hn)]; exact hn
          · rw [ite_eq_right_of_eq_false _ _ (eq_false hn)]; exact Nat.le_refl _

theorem Branch.numCalls_caseCond {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool}
    {cs : Ctors ks bs} {h : UnionShape bs} {τ : Ty ks} {js : JCtx ks} {o : Lvl} {ℓ : Nat}
    (n : Neu Δ Φ Γ (.union cs (h := h)) ℓ) (brs : Branches Δ d Φ Γ cs τ js o) :
    (Branch.caseCond n brs).2.numCalls ≤ brs.numCalls := by
  unfold Branch.caseCond
  cases n.caseCond? brs with
  | none => exact Nat.le_refl _
  | some r =>
      simp only
      by_cases hn : r.2.numCalls ≤ brs.numCalls
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hn)]; exact hn
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hn)]; exact Nat.le_refl _

theorem Term.numCalls_caseCondTop {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} (r : (o : Lvl) × Term Δ d Φ Γ τ js o) :
    (Term.caseCondTop r).2.numCalls ≤ r.2.numCalls := by
  obtain ⟨o, t⟩ := r
  cases t with
  | branch br =>
      cases br with
      | union_casesOn n brs =>
          simp only [Term.caseCondTop, Term.numCalls, Branch.numCalls]
          exact Branch.numCalls_caseCond _ _
      | _ => exact Nat.le_refl _
  | _ => exact Nat.le_refl _

theorem Term.numCalls_shareCase {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks}
    {js : JCtx ks} {ℓ : Nat} {o' : Lvl} (u : Usage1ω) (c : Comp Δ d Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') :
    (Term.shareCase u c b).2.numCalls ≤ c.numCalls + b.numCalls := by
  cases c with
  | share n =>
      simp only [Term.shareCase, Comp.numCalls]
      by_cases hc : (u = .one ∧ n.isCond = true ∧ b.isCaseOnHead = true)
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
        cases b.subst (D' := d) KLRen.id (USub.cons ⟨_, .neu n⟩ (USub.ofRen ULRen.idL))
            JRen.id with
        | none => simp [Term.numCalls, Comp.numCalls]
        | some r =>
            simp only
            by_cases hn : (Term.caseCondTop r).2.numCalls ≤ b.numCalls
            · rw [ite_eq_left_of_eq_true _ _ (eq_true hn)]; omega
            · rw [ite_eq_right_of_eq_false _ _ (eq_false hn)]; simp [Term.numCalls, Comp.numCalls]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]; simp [Term.numCalls, Comp.numCalls]
  | _ => exact Nat.le_refl _

mutual
theorem Val.numCalls_jcWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → v.jcWalk.numCalls ≤ v.numCalls
  | _, _, _, _, _, .lam b => by simp only [Val.jcWalk, Val.numCalls]; exact Body.numCalls_jcWalk b
  | _, _, _, _, _, .thunk_mk b => by
      simp only [Val.jcWalk, Val.numCalls]; exact Body.numCalls_jcWalk b
  | _, _, _, _, _, .lazy_mk b => by
      simp only [Val.jcWalk, Val.numCalls]; exact Body.numCalls_jcWalk b
  | _, _, _, _, _, .record_mk _ => Nat.le_refl _
  | _, _, _, _, _, .union_mk _ _ => Nat.le_refl _
  | _, _, _, _, _, .array_mk _ => Nat.le_refl _
  | _, _, _, _, _, .list_mk _ => Nat.le_refl _
  | _, _, _, _, _, .data_in _ _ _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
theorem Body.numCalls_jcWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → b.jcWalk.numCalls ≤ b.numCalls
  | _, _, _, _, _, _, .closed t => by
      simp only [Body.jcWalk, Body.numCalls]; exact Term.numCalls_jcWalk t
  | _, _, _, _, _, _, .opened t _ => by
      simp only [Body.jcWalk, Body.numCalls]
      exact Term.numCalls_keepLvl t _ (Term.numCalls_jcWalk t)
  termination_by structural _ _ _ _ _ _ x => x
theorem Comp.numCalls_jcWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → c.jcWalk.numCalls ≤ c.numCalls
  | _, _, _, _, _, .app _ _ _ => Nat.le_refl _
  | _, _, _, _, _, .share _ => Nat.le_refl _
  | _, _, _, _, _, .nat_rec n z s _ => by
      simp only [Comp.jcWalk, Comp.numCalls]; exact Body.numCalls_jcWalk s
  | _, _, _, _, _, .array_foldl a z s _ => by
      simp only [Comp.jcWalk, Comp.numCalls]; exact Body.numCalls_jcWalk s
  | _, _, _, _, _, .data_rec b ρt us brs j e _ => by
      simp only [Comp.jcWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_jcWalk (brs i))
  | _, _, _, _, _, .data_brec b ρt k us brs j e _ => by
      simp only [Comp.jcWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_jcWalk (brs i))
  | _, _, _, _, _, .thunk_force _ => Nat.le_refl _
  | _, _, _, _, _, .lazy_force _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
theorem Term.numCalls_jcWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → t.jcWalk.2.numCalls ≤ t.numCalls
  | _, _, _, _, _, _, .ret _ => Nat.le_refl _
  | _, _, _, _, _, _, .letV u v b => by
      have hv := Val.numCalls_jcWalk v
      have hb := Term.numCalls_jcWalk b
      simp only [Term.jcWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .letE u c b => by
      have hc := Comp.numCalls_jcWalk c
      have hb := Term.numCalls_jcWalk b
      have h := Term.numCalls_shareCase u c.jcWalk b.jcWalk.2
      simp only [Term.jcWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .record_casesOn us n b => by
      simp only [Term.jcWalk, Term.numCalls]; exact Term.numCalls_jcWalk b
  | _, _, _, _, _, _, .branch br => by
      simp only [Term.jcWalk, Term.numCalls]; exact Branch.numCalls_jcWalk br
  | _, _, _, _, _, _, .jump _ _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ _ x => x
theorem Branch.numCalls_jcWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) →
    br.jcWalk.2.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, .ite c t e => by
      have h₁ := Term.numCalls_jcWalk t
      have h₂ := Term.numCalls_jcWalk e
      simp only [Branch.jcWalk, Branch.numCalls]; omega
  | _, _, _, _, _, _, .enum_casesOn e bs => by
      simp only [Branch.jcWalk, Branch.numCalls]
      exact Fin.sumNat_le _ (fun i => Term.numCalls_jcWalk (bs i))
  | _, _, _, _, _, _, .union_casesOn e bs => by
      simp only [Branch.jcWalk, Branch.numCalls]
      exact Nat.le_trans (Branch.numCalls_caseCond _ _) (Branches.numCalls_jcWalk bs)
  | _, _, _, _, _, _, .join σ u uₓ body main => by
      have h₁ := Term.numCalls_jcWalk body
      have h₂ := Branch.numCalls_jcWalk main
      have h := Branch.numCalls_joinCtor σ u uₓ body.jcWalk.2 main.jcWalk.2
      simp only [Branch.jcWalk, Branch.numCalls]; omega
  termination_by structural _ _ _ _ _ _ x => x
theorem Branches.numCalls_jcWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → br.jcWalk.2.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ => by
      have h₁ := Term.numCalls_jcWalk b₁
      have h₂ := Term.numCalls_jcWalk b₂
      simp only [Branches.jcWalk, Branches.numCalls]; omega
  | _, _, _, _, _, _, _, _, .cons us b bs => by
      have h₁ := Term.numCalls_jcWalk b
      have h₂ := Branches.numCalls_jcWalk bs
      simp only [Branches.jcWalk, Branches.numCalls]; omega
  termination_by structural _ _ _ _ _ _ _ _ x => x
end

/-- **Writing join points at their jumps never adds calls.** -/
theorem Term.numCalls_joinCtor {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} {o : Lvl} (t : Term Δ d Φ Γ τ js o) : t.joinCtor.numCalls ≤ t.numCalls :=
  Term.numCalls_keepLvl t _ (Term.numCalls_jcWalk t)

/-! ## `Term.openCall` -/

theorem Comp.numCalls_openCall? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {ℓ : Nat}
    (I : OInfo Δ Φ Γ) (c : Comp Δ d Φ Γ σ ℓ) {r : (ℓ' : Nat) × Comp Δ d Φ Γ σ ℓ'}
    (h : c.openCall? I = some r) : r.2.numCalls = 0 := by
  unfold Comp.openCall? at h
  split at h
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨f, hf, p, hp, n, hn, rfl⟩ := h
    rfl
  · cases h

mutual
theorem Val.numCalls_ocWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → (I : OInfo Δ Φ Γ) → (v.ocWalk I).numCalls ≤ v.numCalls
  | _, _, _, _, _, .lam b, I => by
      simp only [Val.ocWalk, Val.numCalls]; exact Body.numCalls_ocWalk b I
  | _, _, _, _, _, .thunk_mk b, I => by
      simp only [Val.ocWalk, Val.numCalls]; exact Body.numCalls_ocWalk b I
  | _, _, _, _, _, .lazy_mk b, I => by
      simp only [Val.ocWalk, Val.numCalls]; exact Body.numCalls_ocWalk b I
  | _, _, _, _, _, .record_mk _, _ => Nat.le_refl _
  | _, _, _, _, _, .union_mk _ _, _ => Nat.le_refl _
  | _, _, _, _, _, .array_mk _, _ => Nat.le_refl _
  | _, _, _, _, _, .list_mk _, _ => Nat.le_refl _
  | _, _, _, _, _, .data_in _ _ _, _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
theorem Body.numCalls_ocWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (I : OInfo Δ Φ Γ) →
    (b.ocWalk I).numCalls ≤ b.numCalls
  | _, _, _, _, _, _, .closed t, _ => by
      simp only [Body.ocWalk, Body.numCalls]; exact Term.numCalls_ocWalk t _
  | _, _, _, _, _, _, .opened t _, I => by
      simp only [Body.ocWalk, Body.numCalls]
      exact Term.numCalls_keepLvl t _ (Term.numCalls_ocWalk t _)
  termination_by structural _ _ _ _ _ _ x => x
theorem Comp.numCalls_ocWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (I : OInfo Δ Φ Γ) → (c.ocWalk I).numCalls ≤ c.numCalls
  | _, _, _, _, _, .app _ _ _, _ => Nat.le_refl _
  | _, _, _, _, _, .share _, _ => Nat.le_refl _
  | _, _, _, _, _, .nat_rec n z s _, I => by
      simp only [Comp.ocWalk, Comp.numCalls]; exact Body.numCalls_ocWalk s I
  | _, _, _, _, _, .array_foldl a z s _, I => by
      simp only [Comp.ocWalk, Comp.numCalls]; exact Body.numCalls_ocWalk s I
  | _, _, _, _, _, .data_rec b ρt us brs j e _, I => by
      simp only [Comp.ocWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_ocWalk (brs i) I)
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, I => by
      simp only [Comp.ocWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_ocWalk (brs i) I)
  | _, _, _, _, _, .thunk_force _, _ => Nat.le_refl _
  | _, _, _, _, _, .lazy_force _, _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
theorem Term.numCalls_ocWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → (I : OInfo Δ Φ Γ) →
    (t.ocWalk I).2.numCalls ≤ t.numCalls
  | _, _, _, _, _, _, .ret _, _ => Nat.le_refl _
  | _, _, _, _, _, _, .letV u v b, I => by
      have hv := Val.numCalls_ocWalk v I
      have hb := Term.numCalls_ocWalk b (I.cons (v.ocWalk I).openFnE?)
      simp only [Term.ocWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .letE u c b, I => by
      have hc := Comp.numCalls_ocWalk c I
      have hb := Term.numCalls_ocWalk b (I.wk1 _)
      have hc' : ((c.ocWalk I).openCall? I |>.getD ⟨_, c.ocWalk I⟩).2.numCalls ≤
          (c.ocWalk I).numCalls := by
        cases h : (c.ocWalk I).openCall? I with
        | none => exact Nat.le_refl _
        | some r =>
            simp only [Option.getD_some]
            rw [Comp.numCalls_openCall? I _ h]; exact Nat.zero_le _
      simp only [Term.ocWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .record_casesOn us n b, I => by
      simp only [Term.ocWalk, Term.numCalls]; exact Term.numCalls_ocWalk b _
  | _, _, _, _, _, _, .branch br, I => by
      simp only [Term.ocWalk, Term.numCalls]; exact Branch.numCalls_ocWalk br I
  | _, _, _, _, _, _, .jump _ _, _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ _ x => x
theorem Branch.numCalls_ocWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → (I : OInfo Δ Φ Γ) →
    (br.ocWalk I).2.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, .ite c t e, I => by
      have h₁ := Term.numCalls_ocWalk t I
      have h₂ := Term.numCalls_ocWalk e I
      simp only [Branch.ocWalk, Branch.numCalls]; omega
  | _, _, _, _, _, _, .enum_casesOn e bs, I => by
      simp only [Branch.ocWalk, Branch.numCalls]
      exact Fin.sumNat_le _ (fun i => Term.numCalls_ocWalk (bs i) I)
  | _, _, _, _, _, _, .union_casesOn e bs, I => by
      simp only [Branch.ocWalk, Branch.numCalls]; exact Branches.numCalls_ocWalk bs I
  | _, _, _, _, _, _, .join σ u uₓ body main, I => by
      have h₁ := Term.numCalls_ocWalk body (I.wk1 _)
      have h₂ := Branch.numCalls_ocWalk main I
      simp only [Branch.ocWalk, Branch.numCalls]; omega
  termination_by structural _ _ _ _ _ _ x => x
theorem Branches.numCalls_ocWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (I : OInfo Δ Φ Γ) → (br.ocWalk I).2.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, I => by
      have h₁ := Term.numCalls_ocWalk b₁ (I.wkN _)
      have h₂ := Term.numCalls_ocWalk b₂ (I.wkN _)
      simp only [Branches.ocWalk, Branches.numCalls]; omega
  | _, _, _, _, _, _, _, _, .cons us b bs, I => by
      have h₁ := Term.numCalls_ocWalk b (I.wkN _)
      have h₂ := Branches.numCalls_ocWalk bs I
      simp only [Branches.ocWalk, Branches.numCalls]; omega
  termination_by structural _ _ _ _ _ _ _ _ x => x
end

/-- **Inlining the calls of open closures computing an expression never adds calls.** -/
theorem Term.numCalls_openCall {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} {o : Lvl} (t : Term Δ d Φ Γ τ js o) : t.openCall.numCalls ≤ t.numCalls :=
  Term.numCalls_keepLvl t _ (Term.numCalls_ocWalk t _)

end LeanScript

end
