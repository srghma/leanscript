module

public import LeanScript.Term.Optimize.Count
public import LeanScript.Term.Rename.Basic

@[expose] public section

set_option autoImplicit false

/-!
# Renaming does not change the number of calls

A renaming (`Term.rename`) only changes the variables of a statement, never its computations,
so when it succeeds the renamed statement has as many calls (`Term.numCalls`) as the original.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

theorem Fin.sumNat_congr : (n : Nat) → {f g : Fin n → Nat} → (∀ i, f i = g i) →
    Fin.sumNat n f = Fin.sumNat n g
  | 0, _, _, _ => rfl
  | n + 1, f, g, h => by
      simp only [Fin.sumNat, h 0, Fin.sumNat_congr n (fun i => h i.succ)]

theorem Fin.sumNat_le : (n : Nat) → {f g : Fin n → Nat} → (∀ i, f i ≤ g i) →
    Fin.sumNat n f ≤ Fin.sumNat n g
  | 0, _, _, _ => Nat.le_refl _
  | n + 1, f, g, h => by
      simp only [Fin.sumNat]
      exact Nat.add_le_add (h 0) (Fin.sumNat_le n (fun i => h i.succ))

mutual
theorem Val.numCalls_rename : {d : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {rk : KRen Φ Φ'} → {ru : URen Γ Γ'} → {τ : Ty ks} → {o : Lvl} →
    (v : Val Δ d Φ Γ τ o) → {v' : Val Δ d Φ' Γ' τ o} → v.rename rk ru = some v' →
      v'.numCalls = v.numCalls
  | _, _, _, _, _, _, _, _, _, .lam b, _, h => by
      simp only [Val.rename, Option.map_eq_some_iff] at h
      obtain ⟨b', hb, rfl⟩ := h
      simp only [Val.numCalls]; exact Body.numCalls_rename b hb
  | _, _, _, _, _, _, _, _, _, .thunk_mk b, _, h => by
      simp only [Val.rename, Option.map_eq_some_iff] at h
      obtain ⟨b', hb, rfl⟩ := h
      simp only [Val.numCalls]; exact Body.numCalls_rename b hb
  | _, _, _, _, _, _, _, _, _, .lazy_mk b, _, h => by
      simp only [Val.rename, Option.map_eq_some_iff] at h
      obtain ⟨b', hb, rfl⟩ := h
      simp only [Val.numCalls]; exact Body.numCalls_rename b hb
  | _, _, _, _, _, _, _, _, _, .record_mk _, _, h => by
      simp only [Val.rename, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; rfl
  | _, _, _, _, _, _, _, _, _, .union_mk _ _, _, h => by
      simp only [Val.rename, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; rfl
  | _, _, _, _, _, _, _, _, _, .array_mk _, _, h => by
      simp only [Val.rename, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; rfl
  | _, _, _, _, _, _, _, _, _, .list_mk _, _, h => by
      simp only [Val.rename, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; rfl
  | _, _, _, _, _, _, _, _, _, .data_in _ _ _, _, h => by
      simp only [Val.rename, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; rfl
  termination_by structural _ _ _ _ _ _ _ _ _ x _ _ => x
theorem Body.numCalls_rename : {d : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {rk : KRen Φ Φ'} → {ru : URen Γ Γ'} → {bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    (b : Body Δ d Φ Γ bs τ o) → {b' : Body Δ d Φ' Γ' bs τ o} → b.rename rk ru = some b' →
      b'.numCalls = b.numCalls
  | _, _, _, _, _, _, _, _, _, _, .closed t, _, h => by
      simp only [Body.rename, Option.map_eq_some_iff] at h
      obtain ⟨t', ht, rfl⟩ := h
      simp only [Body.numCalls]; exact Term.numCalls_rename t ht
  | _, _, _, _, _, _, _, _, _, _, .opened t _, _, h => by
      simp only [Body.rename, Option.map_eq_some_iff] at h
      obtain ⟨t', ht, rfl⟩ := h
      simp only [Body.numCalls]; exact Term.numCalls_rename t ht
  termination_by structural _ _ _ _ _ _ _ _ _ _ x _ _ => x
theorem Comp.numCalls_rename : {d : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {rk : KRen Φ Φ'} → {ru : URen Γ Γ'} → {τ : Ty ks} → {ℓ : Nat} →
    (c : Comp Δ d Φ Γ τ ℓ) → {c' : Comp Δ d Φ' Γ' τ ℓ} → c.rename rk ru = some c' →
      c'.numCalls = c.numCalls
  | _, _, _, _, _, _, _, _, _, .app f a _, _, h => by
      simp only [Comp.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, _, _, rfl⟩ := h; rfl
  | _, _, _, _, _, _, _, _, _, .share _, _, h => by
      simp only [Comp.rename, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; rfl
  | _, _, _, _, _, _, _, _, _, .nat_rec n z s _, _, h => by
      simp only [Comp.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, _, _, s', hs, rfl⟩ := h
      simp only [Comp.numCalls]; exact Body.numCalls_rename s hs
  | _, _, _, _, _, _, _, _, _, .array_foldl a z s _, _, h => by
      simp only [Comp.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, _, _, s', hs, rfl⟩ := h
      simp only [Comp.numCalls]; exact Body.numCalls_rename s hs
  | _, _, _, _, _, _, _, _, _, .data_rec b ρt us brs j e _, _, h => by
      simp only [Comp.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨brs', hbrs, _, _, rfl⟩ := h
      simp only [Comp.numCalls]
      exact Fin.sumNat_congr _ (fun i => Body.numCalls_rename (brs i) (Fin.optAll_eq_some hbrs i))
  | _, _, _, _, _, _, _, _, _, .data_brec b ρt k us brs j e _, _, h => by
      simp only [Comp.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨brs', hbrs, _, _, rfl⟩ := h
      simp only [Comp.numCalls]
      exact Fin.sumNat_congr _ (fun i => Body.numCalls_rename (brs i) (Fin.optAll_eq_some hbrs i))
  | _, _, _, _, _, _, _, _, _, .thunk_force _, _, h => by
      simp only [Comp.rename, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; rfl
  | _, _, _, _, _, _, _, _, _, .lazy_force _, _, h => by
      simp only [Comp.rename, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; rfl
  termination_by structural _ _ _ _ _ _ _ _ _ x _ _ => x
/-- **A renamed statement has as many calls as the original.** -/
theorem Term.numCalls_rename : {d : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {js js' : JCtx ks} → {rk : KRen Φ Φ'} → {ru : URen Γ Γ'} → {rj : JRen js js'} →
    {τ : Ty ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → {t' : Term Δ d Φ' Γ' τ js' o} →
    t.rename rk ru rj = some t' → t'.numCalls = t.numCalls
  | _, _, _, _, _, _, _, _, _, _, _, _, .ret _, _, h => by
      simp only [Term.rename, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, .letV u v b, _, h => by
      simp only [Term.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨v', hv, b', hb, rfl⟩ := h
      simp only [Term.numCalls, Val.numCalls_rename v hv, Term.numCalls_rename b hb]
  | _, _, _, _, _, _, _, _, _, _, _, _, .letE u c b, _, h => by
      simp only [Term.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨c', hc, b', hb, rfl⟩ := h
      simp only [Term.numCalls, Comp.numCalls_rename c hc, Term.numCalls_rename b hb]
  | _, _, _, _, _, _, _, _, _, _, _, _, .record_casesOn us n b, _, h => by
      simp only [Term.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, b', hb, rfl⟩ := h
      simp only [Term.numCalls, Term.numCalls_rename b hb]
  | _, _, _, _, _, _, _, _, _, _, _, _, .branch br, _, h => by
      simp only [Term.rename, Option.map_eq_some_iff] at h
      obtain ⟨br', hbr, rfl⟩ := h
      simp only [Term.numCalls]; exact Branch.numCalls_rename br hbr
  | _, _, _, _, _, _, _, _, _, _, _, _, .jump _ _, _, h => by
      simp only [Term.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, _, _, rfl⟩ := h; rfl
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ x _ _ => x
theorem Branch.numCalls_rename : {d : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {js js' : JCtx ks} → {rk : KRen Φ Φ'} → {ru : URen Γ Γ'} → {rj : JRen js js'} →
    {τ : Ty ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → {br' : Branch Δ d Φ' Γ' τ js' ℓ} →
    br.rename rk ru rj = some br' → br'.numCalls = br.numCalls
  | _, _, _, _, _, _, _, _, _, _, _, _, .ite c t e, _, h => by
      simp only [Branch.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, t', ht, e', he, rfl⟩ := h
      simp only [Branch.numCalls, Term.numCalls_rename t ht, Term.numCalls_rename e he]
  | _, _, _, _, _, _, _, _, _, _, _, _, .enum_casesOn e bs, _, h => by
      simp only [Branch.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, bs', hbs, rfl⟩ := h
      simp only [Branch.numCalls]
      exact Fin.sumNat_congr _ (fun i => Term.numCalls_rename (bs i) (Fin.optAll_eq_some hbs i))
  | _, _, _, _, _, _, _, _, _, _, _, _, .union_casesOn e bs, _, h => by
      simp only [Branch.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, bs', hbs, rfl⟩ := h
      simp only [Branch.numCalls]; exact Branches.numCalls_rename bs hbs
  | _, _, _, _, _, _, _, _, _, _, _, _, .join σ u uₓ body main, _, h => by
      simp only [Branch.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨body', hbody, main', hmain, rfl⟩ := h
      simp only [Branch.numCalls, Term.numCalls_rename body hbody, Branch.numCalls_rename main hmain]
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ x _ _ => x
theorem Branches.numCalls_rename : {d : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {js js' : JCtx ks} → {rk : KRen Φ Φ'} → {ru : URen Γ Γ'} → {rj : JRen js js'} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → {br' : Branches Δ d Φ' Γ' cs τ js' o} →
    br.rename rk ru rj = some br' → br'.numCalls = br.numCalls
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, _, h => by
      simp only [Branches.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨b₁', h₁, b₂', h₂, rfl⟩ := h
      simp only [Branches.numCalls, Term.numCalls_rename b₁ h₁, Term.numCalls_rename b₂ h₂]
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, .cons us b bs, _, h => by
      simp only [Branches.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨b', hb, bs', hbs, rfl⟩ := h
      simp only [Branches.numCalls, Term.numCalls_rename b hb, Branches.numCalls_rename bs hbs]
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ => x
end

end LeanScript

end
