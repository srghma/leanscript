module

public import LeanScript.Term.Optimize.InlineSubst
public import LeanScript.Term.Optimize.CountSubst

@[expose] public section

set_option autoImplicit false

/-!
# Inlining with arguments and answers that are not neutral adds no call

`BlockFn.numCalls_applyP` (the body at a call has the calls of the body),
`Term.numCalls_bindAns` and `Term.numCalls_bindRet` (binding an answer adds no call).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

theorem Term.numCalls_bindAns {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks}
    {o o' : Lvl} {u : Usage01ω} (e : PExpr Δ Φ Γ σ o) (b : Term Δ d Φ (⟨σ, u, d⟩ :: Γ) τ js o')
    {r : (o'' : Lvl) × Term Δ d Φ Γ τ js o''} (h : Term.bindAns e b = some r) :
    r.2.numCalls = b.numCalls := by
  unfold Term.bindAns at h
  split at h
  · exact Term.numCalls_subst b h
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, r', hr', rfl⟩ := h
    have hv0 : v.numCalls = 0 := by
      cases e <;> simp [PExpr.toVal?] at hv <;> (subst hv; rfl)
    simp only [Term.numCalls, hv0, Term.numCalls_subst b hr', Nat.zero_add]

theorem Term.numCalls_bindRet {d : Nat} {σ τ : Ty ks} {u : Usage1ω} :
    {Φ : KCtx ks} → {Γ : UCtx ks} → {js : JCtx ks} → {o o' : Lvl} →
    (t : Term Δ d Φ Γ σ [] o) → (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') →
    {r : (o'' : Lvl) × Term Δ d Φ Γ τ js o''} → Term.bindRet t b = some r →
    r.2.numCalls = t.numCalls + b.numCalls
  | _, _, _, _, _, .ret e, b, r, h => by
      simp only [Term.bindRet] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        simp only [Term.numCalls, Comp.numCalls]
      · rw [Term.numCalls_bindAns e b h]; simp only [Term.numCalls, Nat.zero_add]
  | _, _, _, _, _, .letE u' c t, b, r, h => by
      simp only [Term.bindRet, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b', hb', r', hr', rfl⟩ := h
      simp only [Term.numCalls]
      rw [Term.numCalls_bindRet t b' hr', Term.numCalls_rename b hb']
      omega
  | _, _, _, _, _, .letV u' v t, b, r, h => by
      simp only [Term.bindRet, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b', hb', r', hr', rfl⟩ := h
      simp only [Term.numCalls]
      rw [Term.numCalls_bindRet t b' hr', Term.numCalls_rename b hb']
      omega
  | _, _, _, _, _, .record_casesOn us n t, b, r, h => by
      simp only [Term.bindRet, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b', hb', r', hr', rfl⟩ := h
      simp only [Term.numCalls]
      rw [Term.numCalls_bindRet t b' hr', Term.numCalls_rename b hb']
  | _, _, _, _, _, .branch br, b, r, h => by
      simp only [Term.bindRet, Option.some.injEq] at h
      subst h
      simp only [Term.numCalls, Branch.numCalls, Branch.numCalls_retToJump]
      omega
  | _, _, _, _, _, .jump _ _, _, _, h => by simp [Term.bindRet] at h

theorem BlockFn.numCalls_applyP {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks}
    {js : JCtx ks} {oa : Lvl} (f : BlockFn Δ Φ (.fn σ τ)) (a : PExpr Δ Φ Γ σ oa)
    {r : (o' : Lvl) × Term Δ d Φ Γ τ js o'} (h : f.applyP a = some r) :
    r.2.numCalls = f.body.numCalls := by
  unfold BlockFn.applyP at h
  split at h
  · exact BlockFn.numCalls_applyNeu f _ h
  · obtain ⟨σ', τ', hty, u, D, o, body⟩ := f
    simp only at h
    split at h
    · rename_i hst
      obtain ⟨rfl, rfl⟩ := hst
      split at h
      · exact Term.numCalls_subst _ h
      · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
        obtain ⟨v, hv, r', hr', rfl⟩ := h
        have hv0 : v.numCalls = 0 := by
          cases a <;> simp [PExpr.toVal?] at hv <;> (subst hv; rfl)
        simp only [Term.numCalls, hv0, Term.numCalls_subst _ hr', Nat.zero_add]
    · cases h

end LeanScript

end
