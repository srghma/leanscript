module

public import LeanScript.Term.Optimize.CondJump
public import LeanScript.Term.Optimize.JoinCtorEval

@[expose] public section

set_option autoImplicit false

/-!
# The rewrites of `LeanScript.Term.Optimize.CondJump` preserve the value

`Term.condJump_eval`: the walk does not change the value of a statement, in any environment.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

theorem Term.shareSubst_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks}
    {ℓ : Nat} {o' : Lvl} (u : Usage1ω) (c : Comp Δ d Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (jκ : JEnv Δ τ js) :
    (Term.shareSubst u c b).2.eval κ ρ jκ = (Term.letE u c b).eval κ ρ jκ := by
  cases c with
  | share n =>
      simp only [Term.shareSubst]
      by_cases hc : (n.isCond = true ∧ (u = .one ∨ b.onlyScrut 0 = true))
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
        cases hs : b.subst (D' := d) KLRen.id (USub.cons ⟨_, .neu n⟩ (USub.ofRen ULRen.idL))
            JRen.id with
        | none => rfl
        | some r =>
            exact Term.subst_eval (KLRen.Agree.id κ)
              (USub.Agree.cons (USub.Agree.ofRen (ULRen.Agree.idL ρ)) _) (JRen.Agree.id jκ) b hs
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
  | _ => rfl

theorem Term.condJumps_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {ℓ : Nat} {o₁ o₂ : Lvl} (c : Neu Δ Φ Γ .bool ℓ) (t : Term Δ d Φ Γ τ js o₁)
    (e : Term Δ d Φ Γ τ js o₂) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    (Term.condJumps c t e).2.eval κ ρ jκ = (Branch.ite c t e).eval κ ρ jκ := by
  cases t <;> cases e <;> try rfl
  rename_i σ₁ j a σ₂ j' b
  simp only [Term.condJumps]
  split
  · rename_i h hs
    have hj := JVar.same?_eq j' j hs
    obtain ⟨hσ⟩ := h
    subst hσ
    simp only at hj
    subst hj
    simp only [Term.eval, Branch.eval, PExpr.eval, Neu.eval]
    cases (c.eval κ ρ : Bool) <;> rfl
  · rfl

theorem Term.bindShare_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks}
    {o : Lvl} {ℓ : Nat} (n : Neu Δ Φ Γ σ ℓ) (uₓ : Usage01ω)
    (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o) {r : (o' : Lvl) × Term Δ d Φ Γ τ js o'}
    (h : Term.bindShare n uₓ body = some r) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    r.2.eval κ ρ jκ = body.eval κ (Tuple.cons (n.eval κ ρ) ρ) jκ := by
  cases uₓ with
  | zero => simp [Term.bindShare] at h
  | one => simp only [Term.bindShare, Option.some.injEq] at h; subst h; rfl
  | many => simp only [Term.bindShare, Option.some.injEq] at h; subst h; rfl

theorem Term.bindParam_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks}
    {o o' : Lvl} (uₓ : Usage01ω) (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o)
    (a : PExpr Δ Φ Γ σ o') {r : (o'' : Lvl) × Term Δ d Φ Γ τ js o''}
    (h : Term.bindParam uₓ body a = some r) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    r.2.eval κ ρ jκ = body.eval κ (Tuple.cons (a.eval κ ρ) ρ) jκ := by
  unfold Term.bindParam at h
  split at h
  · exact Term.subst_eval (KLRen.Agree.id κ)
      (USub.Agree.cons (USub.Agree.ofRen (ULRen.Agree.idL ρ)) _) (JRen.Agree.id jκ) body h
  · cases a with
    | neu n => exact Term.bindShare_eval n uₓ body h κ ρ jκ
    | _ => cases h

theorem Branch.joinJump_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {o : Lvl} {ℓ : Nat} (σ : Ty ks) (u : Usage1ω) (uₓ : Usage01ω)
    (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o) (main : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ)
    (m : (o' : Lvl) × Term Δ d Φ Γ τ (⟨σ, u⟩ :: js) o') (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (jκ : JEnv Δ τ js)
    (hm : m.2.eval κ ρ (Tuple.cons (fun v => body.eval κ (Tuple.cons v ρ) jκ) jκ) =
      main.eval κ ρ (Tuple.cons (fun v => body.eval κ (Tuple.cons v ρ) jκ) jκ)) :
    (Branch.joinJump σ u uₓ body main m).2.eval κ ρ jκ = (Branch.join σ u uₓ body main).eval κ ρ jκ := by
  obtain ⟨o', t⟩ := m
  cases t with
  | branch br =>
      simp only [Branch.joinJump, Term.eval, Branch.eval] at hm ⊢
      exact hm
  | jump j a =>
      cases j with
      | head =>
          simp only [Branch.joinJump, JVar.split]
          cases hr : Term.bindParam uₓ body a with
          | some r =>
              show r.2.eval κ ρ jκ = _
              rw [Term.bindParam_eval uₓ body _ hr κ ρ jκ]
              simp only [Branch.eval]
              rw [← hm]
              simp [Term.eval]
          | none => rfl
      | tail j' =>
          show jκ.get j' (a.eval κ ρ) = _
          simp only [Branch.eval]
          rw [← hm]
          simp [Term.eval]
  | _ => rfl

/-! ## The walk -/

mutual
theorem Val.cjWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    v.cjWalk.eval κ ρ = v.eval κ ρ
  | _, _, _, _, _, .lam b, κ, ρ => by
      simp only [Val.cjWalk, Val.eval]; funext x; rw [Body.cjWalk_eval b κ ρ]
  | _, _, _, _, _, .thunk_mk b, κ, ρ => by
      simp only [Val.cjWalk, Val.eval]; rw [Body.cjWalk_eval b κ ρ]
  | _, _, _, _, _, .lazy_mk b, κ, ρ => by
      simp only [Val.cjWalk, Val.eval]; rw [Body.cjWalk_eval b κ ρ]
  | _, _, _, _, _, .record_mk _, _, _ => rfl
  | _, _, _, _, _, .union_mk _ _, _, _ => rfl
  | _, _, _, _, _, .array_mk _, _, _ => rfl
  | _, _, _, _, _, .list_mk _, _, _ => rfl
  | _, _, _, _, _, .data_in _ _ _, _, _ => rfl
  termination_by structural _ _ _ _ _ x => x
theorem Body.cjWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (vs : UEnv Δ bs) → b.cjWalk.eval κ ρ vs = b.eval κ ρ vs
  | _, _, _, _, _, _, .closed t, κ, _, _ => by
      simp only [Body.cjWalk, Body.eval]; exact Term.cjWalk_eval t _ _ _
  | _, _, _, _, _, _, .opened t _, κ, ρ, vs => by
      simp only [Body.cjWalk, Body.eval]
      exact Term.keepLvl_eval t _ κ _ _ (Term.cjWalk_eval t _ _ _)
  termination_by structural _ _ _ _ _ _ x => x
theorem Comp.cjWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    c.cjWalk.eval κ ρ = c.eval κ ρ
  | _, _, _, _, _, .app _ _ _, _, _ => rfl
  | _, _, _, _, _, .share _, _, _ => rfl
  | _, _, _, _, _, .nat_rec n z s _, κ, ρ => by
      simp only [Comp.cjWalk, Comp.eval]
      congr 1; funext k acc; exact Body.cjWalk_eval s κ ρ _
  | _, _, _, _, _, .array_foldl a z s _, κ, ρ => by
      simp only [Comp.cjWalk, Comp.eval]
      congr 1; funext acc x; exact Body.cjWalk_eval s κ ρ _
  | _, _, _, _, _, .data_rec b ρt us brs j e _, κ, ρ => by
      simp only [Comp.cjWalk, Comp.eval]
      congr 1; funext i x; exact Body.cjWalk_eval (brs i) κ ρ _
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, κ, ρ => by
      simp only [Comp.cjWalk, Comp.eval]
      congr 1; funext i x; exact Body.cjWalk_eval (brs i) κ ρ _
  | _, _, _, _, _, .thunk_force _, _, _ => rfl
  | _, _, _, _, _, .lazy_force _, _, _ => rfl
  termination_by structural _ _ _ _ _ x => x
theorem Term.cjWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
    t.cjWalk.2.eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, .ret _, _, _, _ => rfl
  | _, _, _, _, _, _, .letV u v b, κ, ρ, jκ => by
      simp only [Term.cjWalk, Term.eval, Val.cjWalk_eval v κ ρ]
      exact Term.cjWalk_eval b _ ρ jκ
  | _, _, _, _, _, _, .letE u c b, κ, ρ, jκ => by
      simp only [Term.cjWalk]
      rw [Term.shareSubst_eval]
      simp only [Term.eval, Comp.cjWalk_eval c κ ρ]
      exact Term.cjWalk_eval b κ _ jκ
  | _, _, _, _, _, _, .record_casesOn us n b, κ, ρ, jκ => by
      simp only [Term.cjWalk, Term.eval]
      exact Term.cjWalk_eval b κ _ jκ
  | _, _, _, _, _, _, .branch br, κ, ρ, jκ => by
      simp only [Term.cjWalk, Term.eval]
      exact Branch.cjWalk_eval br κ ρ jκ
  | _, _, _, _, _, _, .jump _ _, _, _, _ => rfl
  termination_by structural _ _ _ _ _ _ x => x
theorem Branch.cjWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
    br.cjWalk.2.eval κ ρ jκ = br.eval κ ρ jκ
  | _, _, _, _, _, _, .ite c t e, κ, ρ, jκ => by
      simp only [Branch.cjWalk]
      rw [Term.condJumps_eval]
      simp only [Branch.eval, Term.cjWalk_eval t κ ρ jκ, Term.cjWalk_eval e κ ρ jκ]
  | _, _, _, _, _, _, .enum_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.cjWalk, Term.eval, Branch.eval]; exact Term.cjWalk_eval _ κ ρ jκ
  | _, _, _, _, _, _, .union_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.cjWalk, Term.eval, Branch.eval]
      exact Branches.cjWalk_eval bs κ ρ jκ _
  | _, _, _, _, _, _, .join σ u uₓ body main, κ, ρ, jκ => by
      simp only [Branch.cjWalk]
      rw [Branch.joinJump_eval σ u uₓ _ main _ κ ρ jκ (Branch.cjWalk_eval main κ ρ _)]
      simp only [Branch.eval, Term.cjWalk_eval body κ]
  termination_by structural _ _ _ _ _ _ x => x
theorem Branches.cjWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (jκ : JEnv Δ τ js) → ∀ x, br.cjWalk.2.eval κ ρ jκ x = br.eval κ ρ jκ x
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, κ, ρ, jκ, x => by
      simp only [Branches.cjWalk, Branches.eval, Term.cjWalk_eval b₁ κ, Term.cjWalk_eval b₂ κ]
  | _, _, _, _, _, _, _, _, .cons us b bs, κ, ρ, jκ, x => by
      simp only [Branches.cjWalk, Branches.eval, Term.cjWalk_eval b κ, Branches.cjWalk_eval bs κ ρ jκ]
  termination_by structural _ _ _ _ _ _ _ _ x => x
end

/-- **The rewrites of `Term.condJump` do not change the value of a statement**, in any
    environment. -/
theorem Term.condJump_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {o : Lvl} (t : Term Δ d Φ Γ τ js o) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    t.condJump.eval κ ρ jκ = t.eval κ ρ jκ :=
  Term.keepLvl_eval t _ κ ρ jκ (Term.cjWalk_eval t κ ρ jκ)

end LeanScript

end
