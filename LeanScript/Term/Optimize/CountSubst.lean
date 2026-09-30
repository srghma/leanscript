module

public import LeanScript.Term.Optimize.Subst
public import LeanScript.Term.Optimize.CountRelevel

@[expose] public section

set_option autoImplicit false

/-!
# Substitution adds no call

`Term.numCalls_subst`: `Term.subst` replaces unknowns by pure expressions and recomputes
levels; a case analysis of a record literal that disappears has no call, and a case analysis of
an enum literal (or a join point whose branch becomes a jump) that is reduced keeps the calls of
one of its parts only.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

theorem Fin.le_sumNat : (n : Nat) → (f : Fin n → Nat) → (i : Fin n) → f i ≤ Fin.sumNat n f
  | 0, _, i => i.elim0
  | n + 1, f, i => by
      cases i using Fin.cases with
      | zero => show f 0 ≤ f 0 + Fin.sumNat n (fun i => f i.succ); omega
      | succ i =>
          show f i.succ ≤ f 0 + Fin.sumNat n (fun i => f i.succ)
          have := Fin.le_sumNat n (fun i => f i.succ) i; omega

theorem Term.numCalls_asBranch? {D : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} : {o : Lvl} → (t : Term Δ D Φ Γ τ js o) →
    {b : (ℓ : Nat) × Branch Δ D Φ Γ τ js ℓ} → t.asBranch? = some b → b.2.numCalls = t.numCalls
  | _, .branch _, _, h => by
      simp only [Term.asBranch?, Option.some.injEq] at h
      subst h; rfl
  | _, .ret _, _, h => by simp [Term.asBranch?] at h
  | _, .letV _ _ _, _, h => by simp [Term.asBranch?] at h
  | _, .letE _ _ _, _, h => by simp [Term.asBranch?] at h
  | _, .record_casesOn _ _ _, _, h => by simp [Term.asBranch?] at h
  | _, .jump _ _, _, h => by simp [Term.asBranch?] at h

mutual
theorem Val.numCalls_subst : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {rk : KLRen Φ Φ'} → {s : USub Δ Φ' Γ Γ'} → {τ : Ty ks} → {o : Lvl} →
    (v : Val Δ D Φ Γ τ o) → {p : (o' : Lvl) × Val Δ D' Φ' Γ' τ o'} → v.subst rk s = some p →
      p.2.numCalls ≤ v.numCalls
  | _, _, _, _, _, _, _, _, _, _, .lam b, _, h => by
      simp only [Val.subst, Option.map_eq_some_iff] at h
      obtain ⟨b', hb, rfl⟩ := h
      simp only [Val.numCalls]; exact Body.numCalls_subst b hb
  | _, _, _, _, _, _, _, _, _, _, .thunk_mk b, _, h => by
      simp only [Val.subst, Option.map_eq_some_iff] at h
      obtain ⟨b', hb, rfl⟩ := h
      simp only [Val.numCalls]; exact Body.numCalls_subst b hb
  | _, _, _, _, _, _, _, _, _, _, .lazy_mk b, _, h => by
      simp only [Val.subst, Option.map_eq_some_iff] at h
      obtain ⟨b', hb, rfl⟩ := h
      simp only [Val.numCalls]; exact Body.numCalls_subst b hb
  | _, _, _, _, _, _, _, _, _, _, .record_mk _, _, h => by
      simp only [Val.subst, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; exact Nat.le_refl _
  | _, _, _, _, _, _, _, _, _, _, .union_mk _ _, _, h => by
      simp only [Val.subst, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; exact Nat.le_refl _
  | _, _, _, _, _, _, _, _, _, _, .array_mk _, _, h => by
      simp only [Val.subst, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; exact Nat.le_refl _
  | _, _, _, _, _, _, _, _, _, _, .list_mk _, _, h => by
      simp only [Val.subst, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; exact Nat.le_refl _
  | _, _, _, _, _, _, _, _, _, _, .data_in _ _ _, _, h => by
      simp only [Val.subst, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; exact Nat.le_refl _
  termination_by structural _ _ _ _ _ _ _ _ _ _ x _ _ => x
theorem Body.numCalls_subst : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {rk : KLRen Φ Φ'} → {s : USub Δ Φ' Γ Γ'} → {bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    (b : Body Δ D Φ Γ bs τ o) →
    {p : (o' : Lvl) × Body Δ D' Φ' Γ' (UCtx.setLv (D' + 1) bs) τ o'} →
    b.subst rk s = some p → p.2.numCalls ≤ b.numCalls
  | _, _, _, _, _, _, _, _, _, _, _, .closed t, _, h => by
      simp only [Body.subst, Option.map_eq_some_iff] at h
      obtain ⟨t', ht, rfl⟩ := h
      simp only [Body.numCalls]; exact Nat.le_of_eq (Term.numCalls_relvl t ht)
  | _, _, _, _, _, _, _, _, _, _, _, .opened t _, _, h => by
      simp only [Body.subst, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨o', t'⟩, ht, ⟨m, hm⟩, _, h⟩ := h
      simp only at hm
      subst hm
      split at h
      · simp only [Option.pure_def, Option.some.injEq] at h
        subst h
        simp only [Body.numCalls]; exact Term.numCalls_subst t ht
      · cases h
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ x _ _ => x
theorem Comp.numCalls_subst : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {rk : KLRen Φ Φ'} → {s : USub Δ Φ' Γ Γ'} → {τ : Ty ks} → {ℓ : Nat} →
    (c : Comp Δ D Φ Γ τ ℓ) → {p : (ℓ' : Nat) × Comp Δ D' Φ' Γ' τ ℓ'} → c.subst rk s = some p →
      p.2.numCalls ≤ c.numCalls
  | _, _, _, _, _, _, _, _, _, _, .app f a _, _, h => by
      simp only [Comp.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, _, _, _, _, rfl⟩ := h; exact Nat.le_refl _
  | _, _, _, _, _, _, _, _, _, _, .share _, _, h => by
      simp only [Comp.subst, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; exact Nat.le_refl _
  | _, _, _, _, _, _, _, _, _, _, .nat_rec n z s _, _, h => by
      simp only [Comp.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, _, _, s', hs, _, _, rfl⟩ := h
      simp only [Comp.numCalls]; exact Body.numCalls_subst s hs
  | _, _, _, _, _, _, _, _, _, _, .array_foldl a z s _, _, h => by
      simp only [Comp.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, _, _, s', hs, _, _, rfl⟩ := h
      simp only [Comp.numCalls]; exact Body.numCalls_subst s hs
  | _, _, _, _, _, _, _, _, _, _, .data_rec b ρt us brs j e _, _, h => by
      simp only [Comp.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨brs', hbrs, _, _, _, _, rfl⟩ := h
      simp only [Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_subst (brs i) (Fin.optAll_eq_some hbrs i))
  | _, _, _, _, _, _, _, _, _, _, .data_brec b ρt k us brs j e _, _, h => by
      simp only [Comp.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨brs', hbrs, _, _, _, _, rfl⟩ := h
      simp only [Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_subst (brs i) (Fin.optAll_eq_some hbrs i))
  | _, _, _, _, _, _, _, _, _, _, .thunk_force _, _, h => by
      simp only [Comp.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, _, _, rfl⟩ := h; exact Nat.le_refl _
  | _, _, _, _, _, _, _, _, _, _, .lazy_force _, _, h => by
      simp only [Comp.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, _, _, rfl⟩ := h; exact Nat.le_refl _
  termination_by structural _ _ _ _ _ _ _ _ _ _ x _ _ => x
/-- **A substituted statement has at most the calls of the original.** -/
theorem Term.numCalls_subst : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {js js' : JCtx ks} → {rk : KLRen Φ Φ'} → {s : USub Δ Φ' Γ Γ'} → {rj : JRen js js'} →
    {τ : Ty ks} → {o : Lvl} → (t : Term Δ D Φ Γ τ js o) →
    {p : (o' : Lvl) × Term Δ D' Φ' Γ' τ js' o'} → t.subst rk s rj = some p →
    p.2.numCalls ≤ t.numCalls
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .ret _, _, h => by
      simp only [Term.subst, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; exact Nat.le_refl _
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .letV u v b, _, h => by
      simp only [Term.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨v', hv, b', hb, rfl⟩ := h
      have := Val.numCalls_subst v hv; have := Term.numCalls_subst b hb
      simp only [Term.numCalls]; omega
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .letE u c b, _, h => by
      simp only [Term.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨c', hc, b', hb, rfl⟩ := h
      have := Comp.numCalls_subst c hc; have := Term.numCalls_subst b hb
      simp only [Term.numCalls]; omega
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .record_casesOn us n b, _, h => by
      simp only [Term.subst, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨q, _, h⟩ := h
      split at h
      · simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
        obtain ⟨b', hb, rfl⟩ := h
        have := Term.numCalls_subst b hb
        simp only [Term.numCalls]; omega
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨_, _, hb⟩ := h
        have := Term.numCalls_subst b hb
        simp only [Term.numCalls]; omega
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .branch br, _, h => by
      simp only [Term.subst] at h
      simp only [Term.numCalls]; exact Branch.numCalls_subst br h
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .jump _ _, _, h => by
      simp only [Term.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, _, _, rfl⟩ := h; exact Nat.le_refl _
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ => x
theorem Branch.numCalls_subst : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {js js' : JCtx ks} → {rk : KLRen Φ Φ'} → {s : USub Δ Φ' Γ Γ'} → {rj : JRen js js'} →
    {τ : Ty ks} → {ℓ : Nat} → (br : Branch Δ D Φ Γ τ js ℓ) →
    {p : (o' : Lvl) × Term Δ D' Φ' Γ' τ js' o'} → br.subst rk s rj = some p →
    p.2.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .ite c t e, _, h => by
      simp only [Branch.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, t', ht, e', he, rfl⟩ := h
      have := Term.numCalls_subst t ht; have := Term.numCalls_subst e he
      simp only [Term.numCalls, Branch.numCalls]; omega
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .enum_casesOn e bs, _, h => by
      simp only [Branch.subst, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨q, _, h⟩ := h
      split at h
      · simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
        obtain ⟨bs', hbs, rfl⟩ := h
        simp only [Term.numCalls, Branch.numCalls]
        exact Fin.sumNat_le _ (fun i => Term.numCalls_subst (bs i) (Fin.optAll_eq_some hbs i))
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨i, _, h⟩ := h
        simp only [Branch.numCalls]
        exact Nat.le_trans (Term.numCalls_subst (bs i) h) (Fin.le_sumNat _ (fun i => (bs i).numCalls) i)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .union_casesOn e bs, _, h => by
      simp only [Branch.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, bs', hbs, rfl⟩ := h
      simp only [Term.numCalls, Branch.numCalls]; exact Branches.numCalls_subst bs hbs
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .join σ u uₓ body main, _, h => by
      simp only [Branch.subst, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨m, hm, h⟩ := h
      have hmain := Branch.numCalls_subst main hm
      split at h
      · rename_i b hb
        simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
        obtain ⟨body', hbody, rfl⟩ := h
        have := Term.numCalls_subst body hbody
        have hb' := Term.numCalls_asBranch? m.2 hb
        simp only [Term.numCalls, Branch.numCalls]; omega
      · split at h
        · split at h
          · split at h
            · have := Term.numCalls_subst body h
              simp only [Branch.numCalls]; omega
            · cases h
          · simp only [Option.pure_def, Option.some.injEq] at h
            subst h
            simp only [Term.numCalls]; omega
        · cases h
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ => x
theorem Branches.numCalls_subst : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {js js' : JCtx ks} → {rk : KLRen Φ Φ'} → {s : USub Δ Φ' Γ Γ'} → {rj : JRen js js'} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {o : Lvl} →
    (br : Branches Δ D Φ Γ cs τ js o) → {p : (o' : Lvl) × Branches Δ D' Φ' Γ' cs τ js' o'} →
    br.subst rk s rj = some p → p.2.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, _, h => by
      simp only [Branches.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨b₁', h₁, b₂', h₂, rfl⟩ := h
      have := Term.numCalls_subst b₁ h₁; have := Term.numCalls_subst b₂ h₂
      simp only [Branches.numCalls]; omega
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .cons us b bs, _, h => by
      simp only [Branches.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨b', hb, bs', hbs, rfl⟩ := h
      have := Term.numCalls_subst b hb; have := Branches.numCalls_subst bs hbs
      simp only [Branches.numCalls]; omega
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ => x
end

end LeanScript

end
