module

public import LeanScript.Term.Optimize.InlineOnce
public import LeanScript.Term.Optimize.InlineSubstEval

@[expose] public section

set_option autoImplicit false

/-!
# Inlining a closure at its only call preserves the value

`Term.inlineAt_eval`: when the target describes the value of the closure it drops
(`InlTgt.Agree`), the statement with the closure inlined has the same value.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-- The renaming of the target agrees with the environments, and its body describes the value
    of the closure. -/
def InlTgt.Agree {Φ Φ' : KCtx ks} (T : InlTgt Δ Φ Φ') (κ : KEnv Δ Φ) (κ' : KEnv Δ Φ') : Prop :=
  KRen.Agree T.rk κ κ' ∧
    ∀ {ty : Ty ks} {o : Lvl} (k : KVar Φ ty o) (f : BlockFn Δ Φ' ty), T.get k = some f →
      f.Sem κ' (κ.get k)

theorem InlTgt.Agree.single {Φ : KCtx ks} {b : KBinder ks} {f : BlockFn Δ Φ b.ty}
    {κ : KEnv Δ Φ} {x : Ty.Den Δ b.ty} (hf : f.Sem κ x) :
    (InlTgt.single f).Agree (Tuple.cons x κ : KEnv Δ (b :: Φ)) κ := by
  refine ⟨KRen.Agree.drop x κ, ?_⟩
  intro _ _ k g hg
  cases k with
  | head =>
      simp only [InlTgt.single, Option.some.injEq] at hg
      subst hg
      rw [KEnv.get_cons_head]
      exact hf
  | tail k => simp [InlTgt.single] at hg

theorem InlTgt.Agree.lift {Φ Φ' : KCtx ks} {T : InlTgt Δ Φ Φ'} {κ : KEnv Δ Φ} {κ' : KEnv Δ Φ'}
    (hT : T.Agree κ κ') (b : KBinder ks) (x : Ty.Den Δ b.ty) :
    (T.lift b).Agree (Tuple.cons x κ : KEnv Δ (b :: Φ)) (Tuple.cons x κ' : KEnv Δ (b :: Φ')) := by
  refine ⟨KRen.Agree.lift hT.1 b x, ?_⟩
  intro _ _ k g hg
  cases k with
  | head => simp [InlTgt.lift] at hg
  | tail k =>
      simp only [InlTgt.lift, Option.bind_eq_some_iff] at hg
      obtain ⟨f, hf, hr⟩ := hg
      rw [KEnv.get_cons_tail]
      exact BlockFn.rename_sem (KRen.Agree.wk1 κ' x) hr (hT.2 k f hf)

theorem Comp.tgtCall?_eval {d : Nat} {Φ Φ' : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {ℓ : Nat}
    {js : JCtx ks} {T : InlTgt Δ Φ Φ'} {κ : KEnv Δ Φ} {κ' : KEnv Δ Φ'} (hT : T.Agree κ κ')
    (ρ : UEnv Δ Γ) (jκ : JEnv Δ σ js) (c : Comp Δ d Φ Γ σ ℓ)
    {r : (o : Lvl) × Term Δ d Φ' Γ σ js o} (h : c.tgtCall? T = some r) :
    r.2.eval κ' ρ jκ = c.eval κ ρ := by
  unfold Comp.tgtCall? at h
  split at h
  · rename_i k a _
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨f, hf, a', ha', h⟩ := h
    rw [BlockFn.applyP_eval (hT.2 k f hf) a' ρ jκ h,
      PExpr.rename_eval hT.1 (URen.Agree.id ρ) a ha']
    rfl
  · cases h

theorem Term.tgtLetE_eval {d : Nat} {Φ Φ' : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks}
    {ℓ : Nat} {o' : Lvl} {T : InlTgt Δ Φ Φ'} {κ : KEnv Δ Φ} {κ' : KEnv Δ Φ'} (hT : T.Agree κ κ')
    (u : Usage1ω) (c : Comp Δ d Φ Γ σ ℓ) (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o')
    (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) {r : (o : Lvl) × Term Δ d Φ' Γ τ js o}
    (h : Term.tgtLetE T u c b = some r) :
    r.2.eval κ' ρ jκ = (Term.letE u c b).eval κ ρ jκ := by
  unfold Term.tgtLetE at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨b', hb', h⟩ := h
  have hb := fun v => Term.rename_eval hT.1 (URen.Agree.id (Tuple.cons v ρ)) (JRen.Agree.id jκ) b hb'
  split at h
  · rename_i hh hr
    obtain ⟨hh⟩ := hh
    subst hh
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    simp only [Term.eval]
    rw [← hb, Term.retHead?_eval b' hr κ' ρ _ jκ]
    exact Comp.tgtCall?_eval hT ρ jκ c hr'
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨r', hr', h⟩ := h
    rw [Term.bindRet_eval r'.2 b' κ' ρ jκ h, Comp.tgtCall?_eval (js := []) hT ρ PUnit.unit c hr',
      hb]
    rfl

mutual
theorem Term.inlineAt_eval : {d : Nat} → {Φ Φ' : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → {T : InlTgt Δ Φ Φ'} → {κ : KEnv Δ Φ} → {κ' : KEnv Δ Φ'} →
    T.Agree κ κ' → (t : Term Δ d Φ Γ τ js o) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
    {r : (o' : Lvl) × Term Δ d Φ' Γ τ js o'} → t.inlineAt T = some r →
    r.2.eval κ' ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, _, _, _, _, _, .ret _, _, _, _, h => by simp [Term.inlineAt] at h
  | _, _, _, _, _, _, _, _, _, _, _, .jump _ _, _, _, _, h => by simp [Term.inlineAt] at h
  | _, _, _, _, _, _, _, _, κ, _, hT, .letV u v b, ρ, jκ, _, h => by
      simp only [Term.inlineAt, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨v', hv', r', hr', rfl⟩ := h
      simp only [Term.eval]
      rw [Val.rename_eval hT.1 (URen.Agree.id ρ) v hv']
      exact Term.inlineAt_eval (hT.lift _ (v.eval κ ρ)) b ρ jκ hr'
  | _, _, _, _, _, _, _, _, κ, _, hT, .letE u c b, ρ, jκ, _, h => by
      simp only [Term.inlineAt] at h
      split at h
      · rename_i r' hr'
        simp only [Option.some.injEq] at h
        subst h
        exact Term.tgtLetE_eval hT u c b ρ jκ hr'
      · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
        obtain ⟨c', hc', r', hr', rfl⟩ := h
        simp only [Term.eval]
        rw [Comp.rename_eval hT.1 (URen.Agree.id ρ) c hc']
        exact Term.inlineAt_eval hT b _ jκ hr'
  | _, _, _, _, _, _, _, _, κ, _, hT, .record_casesOn us n b, ρ, jκ, _, h => by
      simp only [Term.inlineAt, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨n', hn', r', hr', rfl⟩ := h
      simp only [Term.eval]
      rw [Neu.rename_eval hT.1 (URen.Agree.id ρ) n hn']
      exact Term.inlineAt_eval hT b _ jκ hr'
  | _, _, _, _, _, _, _, _, _, _, hT, .branch br, ρ, jκ, _, h => by
      simp only [Term.inlineAt, Option.map_eq_some_iff] at h
      obtain ⟨r', hr', rfl⟩ := h
      simp only [Term.eval]
      exact Branch.inlineAt_eval hT br ρ jκ hr'
theorem Branch.inlineAt_eval : {d : Nat} → {Φ Φ' : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → {T : InlTgt Δ Φ Φ'} → {κ : KEnv Δ Φ} → {κ' : KEnv Δ Φ'} →
    T.Agree κ κ' → (br : Branch Δ d Φ Γ τ js ℓ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
    {r : (ℓ' : Nat) × Branch Δ d Φ' Γ τ js ℓ'} → br.inlineAt T = some r →
    r.2.eval κ' ρ jκ = br.eval κ ρ jκ
  | _, _, _, _, _, _, _, _, κ, _, hT, .ite c t e, ρ, jκ, _, h => by
      simp only [Branch.inlineAt, Option.bind_eq_some_iff] at h
      obtain ⟨c', hc', h⟩ := h
      split at h
      · rename_i t' ht'
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨r', hr', rfl⟩ := h
        simp only [Branch.eval, Neu.rename_eval hT.1 (URen.Agree.id ρ) c hc',
          Term.rename_eval hT.1 (URen.Agree.id ρ) (JRen.Agree.id jκ) t ht',
          Term.inlineAt_eval hT e ρ jκ hr']
      · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
        obtain ⟨r', hr', e', he', rfl⟩ := h
        simp only [Branch.eval, Neu.rename_eval hT.1 (URen.Agree.id ρ) c hc',
          Term.rename_eval hT.1 (URen.Agree.id ρ) (JRen.Agree.id jκ) e he',
          Term.inlineAt_eval hT t ρ jκ hr']
  | _, _, _, _, _, _, _, _, _, _, _, .enum_casesOn _ _, _, _, _, h => by
      simp [Branch.inlineAt] at h
  | _, _, _, _, _, _, _, _, _, _, _, .union_casesOn _ _, _, _, _, h => by
      simp [Branch.inlineAt] at h
  | _, _, _, _, _, _, _, _, κ, _, hT, .join σ u uₓ body main, ρ, jκ, _, h => by
      simp only [Branch.inlineAt] at h
      split at h
      · rename_i body' hbody'
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨r', hr', rfl⟩ := h
        simp only [Branch.eval]
        have hf := funext fun v =>
          Term.rename_eval hT.1 (URen.Agree.id (Tuple.cons v ρ)) (JRen.Agree.id jκ) body hbody'
        rw [hf]
        exact Branch.inlineAt_eval hT main ρ _ hr'
      · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
        obtain ⟨r', hr', main', hmain', rfl⟩ := h
        simp only [Branch.eval]
        have hf := funext fun v => Term.inlineAt_eval hT body (Tuple.cons v ρ) jκ hr'
        rw [hf]
        exact Branch.rename_eval hT.1 (URen.Agree.id ρ) (JRen.Agree.id _) main hmain'
end

end LeanScript

end
