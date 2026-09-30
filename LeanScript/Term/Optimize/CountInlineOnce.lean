module

public import LeanScript.Term.Optimize.InlineOnce
public import LeanScript.Term.Optimize.CountInlineSubst

@[expose] public section

set_option autoImplicit false

/-!
# Inlining a closure at its only call moves its calls

`Term.numCalls_inlineAt`: when the body of the target has at most `C` calls, the result has at
most the calls of the statement, minus the call that was inlined, plus `C`.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-- The body of the target has at most `C` calls. -/
def InlTgt.Bound {Φ Φ' : KCtx ks} (T : InlTgt Δ Φ Φ') (C : Nat) : Prop :=
  ∀ {ty : Ty ks} {o : Lvl} (k : KVar Φ ty o) (f : BlockFn Δ Φ' ty), T.get k = some f →
    f.body.numCalls ≤ C

theorem InlTgt.Bound.lift {Φ Φ' : KCtx ks} {T : InlTgt Δ Φ Φ'} {C : Nat} (hT : T.Bound C)
    (b : KBinder ks) : (T.lift b).Bound C := by
  intro _ _ k g hg
  cases k with
  | head => simp [InlTgt.lift] at hg
  | tail k =>
      simp only [InlTgt.lift, Option.bind_eq_some_iff] at hg
      obtain ⟨f, hf, hr⟩ := hg
      obtain ⟨σ, τ, hty, u, D, o, body⟩ := f
      simp only [BlockFn.rename, Option.map_eq_some_iff] at hr
      obtain ⟨body', hb, rfl⟩ := hr
      simp only
      rw [Term.numCalls_rename body hb]
      exact hT k _ hf

theorem Comp.numCalls_tgtCall? {d : Nat} {Φ Φ' : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {ℓ : Nat}
    {js : JCtx ks} {T : InlTgt Δ Φ Φ'} {C : Nat} (hT : T.Bound C) (c : Comp Δ d Φ Γ σ ℓ)
    {r : (o : Lvl) × Term Δ d Φ' Γ σ js o} (h : c.tgtCall? T = some r) :
    r.2.numCalls ≤ C ∧ c.numCalls = 1 := by
  unfold Comp.tgtCall? at h
  split at h
  · rename_i k a _
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨f, hf, a', _, h⟩ := h
    exact ⟨Nat.le_trans (BlockFn.numCalls_applyP f a' h) (hT k f hf), rfl⟩
  · cases h

theorem Term.numCalls_tgtLetE {d : Nat} {Φ Φ' : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks}
    {js : JCtx ks} {ℓ : Nat} {o' : Lvl} {T : InlTgt Δ Φ Φ'} {C : Nat} (hT : T.Bound C)
    (u : Usage1ω) (c : Comp Δ d Φ Γ σ ℓ) (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o')
    {r : (o : Lvl) × Term Δ d Φ' Γ τ js o} (h : Term.tgtLetE T u c b = some r) :
    r.2.numCalls + 1 ≤ (Term.letE u c b).numCalls + C := by
  unfold Term.tgtLetE at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨b', hb', h⟩ := h
  simp only [Term.numCalls]
  split at h
  · rename_i hh _
    obtain ⟨hh⟩ := hh
    subst hh
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    have := Comp.numCalls_tgtCall? hT c hr'
    simp only
    omega
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨r', hr', h⟩ := h
    have := Comp.numCalls_tgtCall? hT c hr'
    have := Term.numCalls_bindRet r'.2 b' h
    rw [Term.numCalls_rename b hb'] at this
    omega

theorem Val.numCalls_blockFn? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {ty : Ty ks} {o : Lvl}
    (v : Val Δ d Φ Γ ty o) {f : BlockFn Δ Φ ty} (h : v.blockFn? = some f) :
    f.body.numCalls = v.numCalls := by
  unfold Val.blockFn? at h
  split at h
  · rename_i t
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨t', ht, rfl⟩ := h
    simp only [Val.numCalls, Body.numCalls]
    exact Term.numCalls_rename t ht
  · cases h

mutual
/-- **Inlining at the only call moves the calls of the body in place of the call.** -/
theorem Term.numCalls_inlineAt : {d : Nat} → {Φ Φ' : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → {T : InlTgt Δ Φ Φ'} → {C : Nat} → T.Bound C →
    (t : Term Δ d Φ Γ τ js o) → {r : (o' : Lvl) × Term Δ d Φ' Γ τ js o'} →
    t.inlineAt T = some r → r.2.numCalls + 1 ≤ t.numCalls + C
  | _, _, _, _, _, _, _, _, _, _, .ret _, _, h => by simp [Term.inlineAt] at h
  | _, _, _, _, _, _, _, _, _, _, .jump _ _, _, h => by simp [Term.inlineAt] at h
  | _, _, _, _, _, _, _, _, _, hT, .letV u v b, _, h => by
      simp only [Term.inlineAt, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨v', hv', r', hr', rfl⟩ := h
      have := Term.numCalls_inlineAt (hT.lift _) b hr'
      simp only [Term.numCalls, Val.numCalls_rename v hv']
      omega
  | _, _, _, _, _, _, _, _, _, hT, .letE u c b, _, h => by
      simp only [Term.inlineAt] at h
      split at h
      · rename_i r' hr'
        simp only [Option.some.injEq] at h
        subst h
        exact Term.numCalls_tgtLetE hT u c b hr'
      · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
        obtain ⟨c', hc', r', hr', rfl⟩ := h
        have := Term.numCalls_inlineAt hT b hr'
        simp only [Term.numCalls, Comp.numCalls_rename c hc']
        omega
  | _, _, _, _, _, _, _, _, _, hT, .record_casesOn us n b, _, h => by
      simp only [Term.inlineAt, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨n', hn', r', hr', rfl⟩ := h
      have := Term.numCalls_inlineAt hT b hr'
      simp only [Term.numCalls]
      omega
  | _, _, _, _, _, _, _, _, _, hT, .branch br, _, h => by
      simp only [Term.inlineAt, Option.map_eq_some_iff] at h
      obtain ⟨r', hr', rfl⟩ := h
      have := Branch.numCalls_inlineAt hT br hr'
      simp only [Term.numCalls]
      omega
theorem Branch.numCalls_inlineAt : {d : Nat} → {Φ Φ' : KCtx ks} → {Γ : UCtx ks} →
    {τ : Ty ks} → {js : JCtx ks} → {ℓ : Nat} → {T : InlTgt Δ Φ Φ'} → {C : Nat} → T.Bound C →
    (br : Branch Δ d Φ Γ τ js ℓ) → {r : (ℓ' : Nat) × Branch Δ d Φ' Γ τ js ℓ'} →
    br.inlineAt T = some r → r.2.numCalls + 1 ≤ br.numCalls + C
  | _, _, _, _, _, _, _, _, _, hT, .ite c t e, _, h => by
      simp only [Branch.inlineAt, Option.bind_eq_some_iff] at h
      obtain ⟨c', hc', h⟩ := h
      split at h
      · rename_i t' ht'
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨r', hr', rfl⟩ := h
        have := Term.numCalls_inlineAt hT e hr'
        simp only [Branch.numCalls, Term.numCalls_rename t ht']
        omega
      · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
        obtain ⟨r', hr', e', he', rfl⟩ := h
        have := Term.numCalls_inlineAt hT t hr'
        simp only [Branch.numCalls, Term.numCalls_rename e he']
        omega
  | _, _, _, _, _, _, _, _, _, _, .enum_casesOn _ _, _, h => by simp [Branch.inlineAt] at h
  | _, _, _, _, _, _, _, _, _, _, .union_casesOn _ _, _, h => by simp [Branch.inlineAt] at h
  | _, _, _, _, _, _, _, _, _, hT, .join σ u uₓ body main, _, h => by
      simp only [Branch.inlineAt] at h
      split at h
      · rename_i body' hbody'
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨r', hr', rfl⟩ := h
        have := Branch.numCalls_inlineAt hT main hr'
        simp only [Branch.numCalls, Term.numCalls_rename body hbody']
        omega
      · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
        obtain ⟨r', hr', main', hmain', rfl⟩ := h
        have := Term.numCalls_inlineAt hT body hr'
        simp only [Branch.numCalls, Branch.numCalls_rename main hmain']
        omega
end

end LeanScript

end
