module

public import LeanScript.Term.Optimize.OpenCall

@[expose] public section

set_option autoImplicit false

/-!
# Inlining the calls of open closures computing an expression preserves the value

`Term.openCall_eval`: the walk of `LeanScript.Term.Optimize.OpenCall` does not change the value
of a statement, in any environment.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## What is known -/

theorem OpenFnE.rename_sem {Φ Φ' : KCtx ks} {Γ Γ' : UCtx ks} {rk : KRen Φ Φ'} {ru : URen Γ Γ'}
    {κ : KEnv Δ Φ} {κ' : KEnv Δ Φ'} {ρ : UEnv Δ Γ} {ρ' : UEnv Δ Γ'}
    (hk : KRen.Agree rk κ κ') (hu : URen.Agree ru ρ ρ') {ty : Ty ks} {f : OpenFnE Δ Φ Γ ty}
    {f' : OpenFnE Δ Φ' Γ' ty} (h : f.rename rk ru = some f') {x : Ty.Den Δ ty}
    (hs : f.Sem κ ρ x) : f'.Sem κ' ρ' x := by
  obtain ⟨σ, τ, hty, u, L, o, body⟩ := f
  simp only [OpenFnE.rename, Option.map_eq_some_iff] at h
  obtain ⟨b, hb, rfl⟩ := h
  intro v
  exact (hs v).trans (PExpr.rename_eval hk (URen.Agree.lift hu ⟨σ, u, L⟩ v) body hb).symm

theorem OInfo.Agree.empty {Φ : KCtx ks} {Γ : UCtx ks} (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (OInfo.empty : OInfo Δ Φ Γ).Agree κ ρ := by
  intro _ _ _ _ h
  cases h

theorem OInfo.Agree.cons {Φ : KCtx ks} {Γ : UCtx ks} {b : KBinder ks} {I : OInfo Δ Φ Γ}
    {κ : KEnv Δ Φ} {ρ : UEnv Δ Γ} (hI : I.Agree κ ρ) {new : Option (OpenFnE Δ Φ Γ b.ty)}
    {x : Ty.Den Δ b.ty} (hn : ∀ f, new = some f → f.Sem κ ρ x) :
    (OInfo.cons new I).Agree (Tuple.cons x κ : KEnv Δ (b :: Φ)) ρ := by
  intro ty o k f hf
  cases k with
  | head =>
      simp only [OInfo.cons, OInfo.consGet, Option.bind_eq_some_iff] at hf
      obtain ⟨g, hg, hr⟩ := hf
      rw [KEnv.get_cons_head]
      exact OpenFnE.rename_sem (KRen.Agree.wk1 κ x) (URen.Agree.id ρ) hr (hn g hg)
  | tail k =>
      simp only [OInfo.cons, OInfo.consGet, Option.bind_eq_some_iff] at hf
      obtain ⟨g, hg, hr⟩ := hf
      rw [KEnv.get_cons_tail]
      exact OpenFnE.rename_sem (KRen.Agree.wk1 κ x) (URen.Agree.id ρ) hr (hI k g hg)

theorem OInfo.Agree.wkN {Φ : KCtx ks} {Γ : UCtx ks} {I : OInfo Δ Φ Γ} {κ : KEnv Δ Φ}
    {ρ : UEnv Δ Γ} (hI : I.Agree κ ρ) (bs : UCtx ks) (vs : UEnv Δ bs) :
    (I.wkN bs).Agree κ (Tuple.append vs ρ) := by
  intro ty o k f hf
  simp only [OInfo.wkN, Option.bind_eq_some_iff] at hf
  obtain ⟨g, hg, hr⟩ := hf
  exact OpenFnE.rename_sem (KRen.Agree.id κ) (URen.Agree.wkN ρ bs vs) hr (hI k g hg)

theorem OInfo.Agree.wk1 {Φ : KCtx ks} {Γ : UCtx ks} {I : OInfo Δ Φ Γ} {κ : KEnv Δ Φ}
    {ρ : UEnv Δ Γ} (hI : I.Agree κ ρ) (b : UBinder ks) (v : Ty.Den Δ b.ty) :
    (I.wk1 b).Agree κ (Tuple.cons v ρ : UEnv Δ (b :: Γ)) := by
  intro ty o k f hf
  simp only [OInfo.wk1, Option.bind_eq_some_iff] at hf
  obtain ⟨g, hg, hr⟩ := hf
  exact OpenFnE.rename_sem (KRen.Agree.id κ) (URen.Agree.wk1 ρ v) hr (hI k g hg)

theorem Term.asRet?_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) : {o : Lvl} → (t : Term Δ d Φ Γ τ js o) →
    {p : (o' : Lvl) × PExpr Δ Φ Γ τ o'} → t.asRet? = some p → p.2.eval κ ρ = t.eval κ ρ jκ
  | _, .ret e, _, h => by simp only [Term.asRet?, Option.some.injEq] at h; subst h; rfl
  | _, .letV _ _ _, _, h => by simp [Term.asRet?] at h
  | _, .letE _ _ _, _, h => by simp [Term.asRet?] at h
  | _, .record_casesOn _ _ _, _, h => by simp [Term.asRet?] at h
  | _, .branch _, _, h => by simp [Term.asRet?] at h
  | _, .jump _ _, _, h => by simp [Term.asRet?] at h

theorem Val.openFnE?_sem {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {ty : Ty ks} {o : Lvl}
    (v : Val Δ d Φ Γ ty o) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (f : OpenFnE Δ Φ Γ ty)
    (h : v.openFnE? = some f) : f.Sem κ ρ (v.eval κ ρ) := by
  unfold Val.openFnE? at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨p, hp, rfl⟩ := h
    intro x
    exact (Term.asRet?_eval (js := []) κ _ PUnit.unit _ hp).symm
  · cases h

theorem OpenFnE.apply_eval {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {oa : Lvl}
    {f : OpenFnE Δ Φ Γ (.fn σ τ)} {κ : KEnv Δ Φ} {ρ : UEnv Δ Γ} {x : Ty.Den Δ (.fn σ τ)}
    (hs : f.Sem κ ρ x) (a : PExpr Δ Φ Γ σ oa) {r : (o' : Lvl) × PExpr Δ Φ Γ τ o'}
    (h : f.apply a = some r) : r.2.eval κ ρ = x (a.eval κ ρ) := by
  obtain ⟨σ', τ', hty, u, L, o, body⟩ := f
  simp only [OpenFnE.apply] at h
  split at h
  · rename_i hst
    obtain ⟨rfl, rfl⟩ := hst
    split at h
    · rw [PExpr.subst_eval (KLRen.Agree.id κ)
        (USub.Agree.cons (USub.Agree.ofRen (ULRen.Agree.idL ρ)) ⟨_, a⟩) body h]
      exact (hs (a.eval κ ρ)).symm
    · cases h
  · cases h

theorem Comp.openCall?_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {ℓ : Nat}
    {I : OInfo Δ Φ Γ} {κ : KEnv Δ Φ} {ρ : UEnv Δ Γ} (hI : I.Agree κ ρ)
    (c : Comp Δ d Φ Γ σ ℓ) {r : (ℓ' : Nat) × Comp Δ d Φ Γ σ ℓ'} (h : c.openCall? I = some r) :
    r.2.eval κ ρ = c.eval κ ρ := by
  unfold Comp.openCall? at h
  split at h
  · rename_i k a _
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨f, hf, p, hp, n, hn, rfl⟩ := h
    simp only [Comp.eval, PExpr.eval]
    rw [PExpr.toNeu?_eval κ ρ p.2 hn, OpenFnE.apply_eval (hI k f hf) a hp]
  · cases h

/-! ## The walk -/

mutual
theorem Val.ocWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → (I : OInfo Δ Φ Γ) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → I.Agree κ ρ → (v.ocWalk I).eval κ ρ = v.eval κ ρ
  | _, _, _, _, _, .lam b, I, κ, ρ, hI => by
      simp only [Val.ocWalk, Val.eval]; funext x; rw [Body.ocWalk_eval b I κ ρ hI]
  | _, _, _, _, _, .thunk_mk b, I, κ, ρ, hI => by
      simp only [Val.ocWalk, Val.eval]; rw [Body.ocWalk_eval b I κ ρ hI]
  | _, _, _, _, _, .lazy_mk b, I, κ, ρ, hI => by
      simp only [Val.ocWalk, Val.eval]; rw [Body.ocWalk_eval b I κ ρ hI]
  | _, _, _, _, _, .record_mk _, _, _, _, _ => rfl
  | _, _, _, _, _, .union_mk _ _, _, _, _, _ => rfl
  | _, _, _, _, _, .array_mk _, _, _, _, _ => rfl
  | _, _, _, _, _, .list_mk _, _, _, _, _ => rfl
  | _, _, _, _, _, .data_in _ _ _, _, _, _, _ => rfl
  termination_by structural _ _ _ _ _ x => x
theorem Body.ocWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (I : OInfo Δ Φ Γ) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → I.Agree κ ρ → (vs : UEnv Δ bs) → (b.ocWalk I).eval κ ρ vs = b.eval κ ρ vs
  | _, _, _, _, _, _, .closed t, _, κ, _, _, vs => by
      simp only [Body.ocWalk, Body.eval]
      exact Term.ocWalk_eval t _ _ _ (OInfo.Agree.empty _ _) _
  | _, _, _, bs, _, _, .opened t _, I, κ, ρ, hI, vs => by
      simp only [Body.ocWalk, Body.eval]
      exact Term.keepLvl_eval t _ κ _ _ (Term.ocWalk_eval t _ _ _ (hI.wkN bs vs) _)
  termination_by structural _ _ _ _ _ _ x => x
theorem Comp.ocWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (I : OInfo Δ Φ Γ) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → I.Agree κ ρ → (c.ocWalk I).eval κ ρ = c.eval κ ρ
  | _, _, _, _, _, .app _ _ _, _, _, _, _ => rfl
  | _, _, _, _, _, .share _, _, _, _, _ => rfl
  | _, _, _, _, _, .nat_rec n z s _, I, κ, ρ, hI => by
      simp only [Comp.ocWalk, Comp.eval]
      congr 1; funext k acc; exact Body.ocWalk_eval s I κ ρ hI _
  | _, _, _, _, _, .array_foldl a z s _, I, κ, ρ, hI => by
      simp only [Comp.ocWalk, Comp.eval]
      congr 1; funext acc x; exact Body.ocWalk_eval s I κ ρ hI _
  | _, _, _, _, _, .data_rec b ρt us brs j e _, I, κ, ρ, hI => by
      simp only [Comp.ocWalk, Comp.eval]
      congr 1; funext i x; exact Body.ocWalk_eval (brs i) I κ ρ hI _
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, I, κ, ρ, hI => by
      simp only [Comp.ocWalk, Comp.eval]
      congr 1; funext i x; exact Body.ocWalk_eval (brs i) I κ ρ hI _
  | _, _, _, _, _, .thunk_force _, _, _, _, _ => rfl
  | _, _, _, _, _, .lazy_force _, _, _, _, _ => rfl
  termination_by structural _ _ _ _ _ x => x
theorem Term.ocWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → (I : OInfo Δ Φ Γ) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → I.Agree κ ρ → (jκ : JEnv Δ τ js) →
    (t.ocWalk I).2.eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, .ret _, _, _, _, _, _ => rfl
  | _, _, _, _, _, _, .letV u v b, I, κ, ρ, hI, jκ => by
      simp only [Term.ocWalk, Term.eval]
      rw [Term.ocWalk_eval b _ _ ρ
        (hI.cons (fun f hf => Val.openFnE?_sem (v.ocWalk I) κ ρ f hf)) jκ,
        Val.ocWalk_eval v I κ ρ hI]
  | _, _, _, _, _, _, .letE u c b, I, κ, ρ, hI, jκ => by
      simp only [Term.ocWalk, Term.eval]
      have hc : ((c.ocWalk I).openCall? I |>.getD ⟨_, c.ocWalk I⟩).2.eval κ ρ = c.eval κ ρ := by
        cases h : (c.ocWalk I).openCall? I with
        | none => exact Comp.ocWalk_eval c I κ ρ hI
        | some r =>
            simp only [Option.getD_some]
            rw [Comp.openCall?_eval hI _ h, Comp.ocWalk_eval c I κ ρ hI]
      rw [hc]
      exact Term.ocWalk_eval b _ κ _ (hI.wk1 _ _) jκ
  | _, _, _, _, _, _, .record_casesOn us n b, I, κ, ρ, hI, jκ => by
      simp only [Term.ocWalk, Term.eval]
      exact Term.ocWalk_eval b _ κ _ (hI.wkN _ _) jκ
  | _, _, _, _, _, _, .branch br, I, κ, ρ, hI, jκ => by
      simp only [Term.ocWalk, Term.eval]
      exact Branch.ocWalk_eval br I κ ρ hI jκ
  | _, _, _, _, _, _, .jump _ _, _, _, _, _, _ => rfl
  termination_by structural _ _ _ _ _ _ x => x
theorem Branch.ocWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → (I : OInfo Δ Φ Γ) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → I.Agree κ ρ → (jκ : JEnv Δ τ js) →
    (br.ocWalk I).2.eval κ ρ jκ = br.eval κ ρ jκ
  | _, _, _, _, _, _, .ite c t e, I, κ, ρ, hI, jκ => by
      simp only [Branch.ocWalk, Branch.eval, Term.ocWalk_eval t I κ ρ hI,
        Term.ocWalk_eval e I κ ρ hI]
  | _, _, _, _, _, _, .enum_casesOn e bs, I, κ, ρ, hI, jκ => by
      simp only [Branch.ocWalk, Branch.eval]; exact Term.ocWalk_eval _ I κ ρ hI _
  | _, _, _, _, _, _, .union_casesOn e bs, I, κ, ρ, hI, jκ => by
      simp only [Branch.ocWalk, Branch.eval]; exact Branches.ocWalk_eval bs I κ ρ hI jκ _
  | _, _, _, _, _, _, .join σ u uₓ body main, I, κ, ρ, hI, jκ => by
      simp only [Branch.ocWalk, Branch.eval]
      rw [Branch.ocWalk_eval main I κ ρ hI]
      have hf : (fun v => (body.ocWalk (I.wk1 _)).2.eval κ (Tuple.cons v ρ) jκ) =
          (fun v => body.eval κ (Tuple.cons v ρ) jκ) :=
        funext fun v => Term.ocWalk_eval body _ κ _ (hI.wk1 _ v) jκ
      rw [hf]
  termination_by structural _ _ _ _ _ _ x => x
theorem Branches.ocWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (I : OInfo Δ Φ Γ) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → I.Agree κ ρ → (jκ : JEnv Δ τ js) →
      ∀ x, (br.ocWalk I).2.eval κ ρ jκ x = br.eval κ ρ jκ x
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, I, κ, ρ, hI, jκ, x => by
      simp only [Branches.ocWalk, Branches.eval]
      congr 1
      · funext v; exact Term.ocWalk_eval b₁ _ κ _ (hI.wkN _ _) jκ
      · funext v; exact Term.ocWalk_eval b₂ _ κ _ (hI.wkN _ _) jκ
  | _, _, _, _, _, _, _, _, .cons us b bs, I, κ, ρ, hI, jκ, x => by
      simp only [Branches.ocWalk, Branches.eval]
      congr 1
      · funext v; exact Term.ocWalk_eval b _ κ _ (hI.wkN _ _) jκ
      · funext r; exact Branches.ocWalk_eval bs I κ ρ hI jκ r
  termination_by structural _ _ _ _ _ _ _ _ x => x
end

/-- **Inlining the calls of known closures with an open body computing an expression does not
    change the value of a statement**, in any environment. -/
theorem Term.openCall_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {o : Lvl} (t : Term Δ d Φ Γ τ js o) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    t.openCall.eval κ ρ jκ = t.eval κ ρ jκ :=
  Term.keepLvl_eval t _ κ ρ jκ (Term.ocWalk_eval t _ κ ρ (OInfo.Agree.empty κ ρ) jκ)

end LeanScript

end
