module

public import LeanScript.Term.Optimize.CountRename
public import LeanScript.Term.Optimize.InlineBlock

@[expose] public section

set_option autoImplicit false

/-!
# Moving a statement to another depth does not change its number of calls

`Term.numCalls_relvl`: `Term.relvl` only renames variables and recomputes levels.  Hence the
body of a closure inlined at a call has as many calls as the body
(`BlockFn.numCalls_applyNeu`); splicing a straight-line body in front of the rest adds
nothing (`Term.numCalls_bindRet`, in `LeanScript.Term.Optimize.CountInlineSubst`).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

mutual
theorem Val.numCalls_relvl : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {rk : KLRen Φ Φ'} → {ru : ULRen Γ Γ'} → {τ : Ty ks} → {o : Lvl} →
    (v : Val Δ D Φ Γ τ o) → {p : (o' : Lvl) × Val Δ D' Φ' Γ' τ o'} → v.relvl rk ru = some p →
      p.2.numCalls = v.numCalls
  | _, _, _, _, _, _, _, _, _, _, .lam b, _, h => by
      simp only [Val.relvl, Option.map_eq_some_iff] at h
      obtain ⟨b', hb, rfl⟩ := h
      simp only [Val.numCalls]; exact Body.numCalls_relvl b hb
  | _, _, _, _, _, _, _, _, _, _, .thunk_mk b, _, h => by
      simp only [Val.relvl, Option.map_eq_some_iff] at h
      obtain ⟨b', hb, rfl⟩ := h
      simp only [Val.numCalls]; exact Body.numCalls_relvl b hb
  | _, _, _, _, _, _, _, _, _, _, .lazy_mk b, _, h => by
      simp only [Val.relvl, Option.map_eq_some_iff] at h
      obtain ⟨b', hb, rfl⟩ := h
      simp only [Val.numCalls]; exact Body.numCalls_relvl b hb
  | _, _, _, _, _, _, _, _, _, _, .record_mk _, _, h => by
      simp only [Val.relvl, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; rfl
  | _, _, _, _, _, _, _, _, _, _, .union_mk _ _, _, h => by
      simp only [Val.relvl, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; rfl
  | _, _, _, _, _, _, _, _, _, _, .array_mk _, _, h => by
      simp only [Val.relvl, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; rfl
  | _, _, _, _, _, _, _, _, _, _, .list_mk _, _, h => by
      simp only [Val.relvl, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; rfl
  | _, _, _, _, _, _, _, _, _, _, .data_in _ _ _, _, h => by
      simp only [Val.relvl, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; rfl
  termination_by structural _ _ _ _ _ _ _ _ _ _ x _ _ => x
theorem Body.numCalls_relvl : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {rk : KLRen Φ Φ'} → {ru : ULRen Γ Γ'} → {bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    (b : Body Δ D Φ Γ bs τ o) →
    {p : (o' : Lvl) × Body Δ D' Φ' Γ' (UCtx.setLv (D' + 1) bs) τ o'} →
    b.relvl rk ru = some p → p.2.numCalls = b.numCalls
  | _, _, _, _, _, _, _, _, _, _, _, .closed t, _, h => by
      simp only [Body.relvl, Option.map_eq_some_iff] at h
      obtain ⟨t', ht, rfl⟩ := h
      simp only [Body.numCalls]; exact Term.numCalls_relvl t ht
  | _, _, _, _, _, _, _, _, _, _, _, .opened t _, _, h => by
      simp only [Body.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨o', t'⟩, ht, ⟨m, hm⟩, _, h⟩ := h
      simp only at hm
      subst hm
      split at h
      · simp only [Option.pure_def, Option.some.injEq] at h
        subst h
        simp only [Body.numCalls]; exact Term.numCalls_relvl t ht
      · cases h
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ x _ _ => x
theorem Comp.numCalls_relvl : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {rk : KLRen Φ Φ'} → {ru : ULRen Γ Γ'} → {τ : Ty ks} → {ℓ : Nat} →
    (c : Comp Δ D Φ Γ τ ℓ) → {p : (ℓ' : Nat) × Comp Δ D' Φ' Γ' τ ℓ'} → c.relvl rk ru = some p →
      p.2.numCalls = c.numCalls
  | _, _, _, _, _, _, _, _, _, _, .app f a _, _, h => by
      simp only [Comp.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, _, _, _, _, rfl⟩ := h; rfl
  | _, _, _, _, _, _, _, _, _, _, .share _, _, h => by
      simp only [Comp.relvl, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; rfl
  | _, _, _, _, _, _, _, _, _, _, .nat_rec n z s _, _, h => by
      simp only [Comp.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, _, _, s', hs, _, _, rfl⟩ := h
      simp only [Comp.numCalls]; exact Body.numCalls_relvl s hs
  | _, _, _, _, _, _, _, _, _, _, .array_foldl a z s _, _, h => by
      simp only [Comp.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, _, _, s', hs, _, _, rfl⟩ := h
      simp only [Comp.numCalls]; exact Body.numCalls_relvl s hs
  | _, _, _, _, _, _, _, _, _, _, .data_rec b ρt us brs j e _, _, h => by
      simp only [Comp.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨brs', hbrs, _, _, _, _, rfl⟩ := h
      simp only [Comp.numCalls]
      exact Fin.sumNat_congr _ (fun i => Body.numCalls_relvl (brs i) (Fin.optAll_eq_some hbrs i))
  | _, _, _, _, _, _, _, _, _, _, .data_brec b ρt k us brs j e _, _, h => by
      simp only [Comp.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨brs', hbrs, _, _, _, _, rfl⟩ := h
      simp only [Comp.numCalls]
      exact Fin.sumNat_congr _ (fun i => Body.numCalls_relvl (brs i) (Fin.optAll_eq_some hbrs i))
  | _, _, _, _, _, _, _, _, _, _, .thunk_force _, _, h => by
      simp only [Comp.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, _, _, rfl⟩ := h; rfl
  | _, _, _, _, _, _, _, _, _, _, .lazy_force _, _, h => by
      simp only [Comp.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, _, _, rfl⟩ := h; rfl
  termination_by structural _ _ _ _ _ _ _ _ _ _ x _ _ => x
/-- **A statement moved to another depth has as many calls as the original.** -/
theorem Term.numCalls_relvl : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {js js' : JCtx ks} → {rk : KLRen Φ Φ'} → {ru : ULRen Γ Γ'} → {rj : JRen js js'} →
    {τ : Ty ks} → {o : Lvl} → (t : Term Δ D Φ Γ τ js o) →
    {p : (o' : Lvl) × Term Δ D' Φ' Γ' τ js' o'} → t.relvl rk ru rj = some p →
    p.2.numCalls = t.numCalls
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .ret _, _, h => by
      simp only [Term.relvl, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .letV u v b, _, h => by
      simp only [Term.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨v', hv, b', hb, rfl⟩ := h
      simp only [Term.numCalls, Val.numCalls_relvl v hv, Term.numCalls_relvl b hb]
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .letE u c b, _, h => by
      simp only [Term.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨c', hc, b', hb, rfl⟩ := h
      simp only [Term.numCalls, Comp.numCalls_relvl c hc, Term.numCalls_relvl b hb]
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .record_casesOn us n b, _, h => by
      simp only [Term.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, b', hb, rfl⟩ := h
      simp only [Term.numCalls, Term.numCalls_relvl b hb]
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .branch br, _, h => by
      simp only [Term.relvl, Option.map_eq_some_iff] at h
      obtain ⟨br', hbr, rfl⟩ := h
      simp only [Term.numCalls]; exact Branch.numCalls_relvl br hbr
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .jump _ _, _, h => by
      simp only [Term.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, _, _, rfl⟩ := h; rfl
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ => x
theorem Branch.numCalls_relvl : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {js js' : JCtx ks} → {rk : KLRen Φ Φ'} → {ru : ULRen Γ Γ'} → {rj : JRen js js'} →
    {τ : Ty ks} → {ℓ : Nat} → (br : Branch Δ D Φ Γ τ js ℓ) →
    {p : (ℓ' : Nat) × Branch Δ D' Φ' Γ' τ js' ℓ'} → br.relvl rk ru rj = some p →
    p.2.numCalls = br.numCalls
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .ite c t e, _, h => by
      simp only [Branch.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, t', ht, e', he, rfl⟩ := h
      simp only [Branch.numCalls, Term.numCalls_relvl t ht, Term.numCalls_relvl e he]
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .enum_casesOn e bs, _, h => by
      simp only [Branch.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, bs', hbs, rfl⟩ := h
      simp only [Branch.numCalls]
      exact Fin.sumNat_congr _ (fun i => Term.numCalls_relvl (bs i) (Fin.optAll_eq_some hbs i))
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .union_casesOn e bs, _, h => by
      simp only [Branch.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨_, _, bs', hbs, rfl⟩ := h
      simp only [Branch.numCalls]; exact Branches.numCalls_relvl bs hbs
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .join σ u uₓ body main, _, h => by
      simp only [Branch.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨body', hbody, main', hmain, rfl⟩ := h
      simp only [Branch.numCalls, Term.numCalls_relvl body hbody, Branch.numCalls_relvl main hmain]
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ => x
theorem Branches.numCalls_relvl : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {js js' : JCtx ks} → {rk : KLRen Φ Φ'} → {ru : ULRen Γ Γ'} → {rj : JRen js js'} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {o : Lvl} →
    (br : Branches Δ D Φ Γ cs τ js o) → {p : (o' : Lvl) × Branches Δ D' Φ' Γ' cs τ js' o'} →
    br.relvl rk ru rj = some p → p.2.numCalls = br.numCalls
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, _, h => by
      simp only [Branches.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨b₁', h₁, b₂', h₂, rfl⟩ := h
      simp only [Branches.numCalls, Term.numCalls_relvl b₁ h₁, Term.numCalls_relvl b₂ h₂]
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .cons us b bs, _, h => by
      simp only [Branches.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨b', hb, bs', hbs, rfl⟩ := h
      simp only [Branches.numCalls, Term.numCalls_relvl b hb, Branches.numCalls_relvl bs hbs]
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ => x
end

theorem BlockFn.numCalls_applyVar {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks}
    {js : JCtx ks} {ℓx : Nat} (f : BlockFn Δ Φ (.fn σ τ)) (x : UVar Γ σ ℓx)
    {r : (o' : Lvl) × Term Δ d Φ Γ τ js o'} (h : f.applyVar x = some r) :
    r.2.numCalls = f.body.numCalls := by
  obtain ⟨σ', τ', hty, u, D, o, body⟩ := f
  simp only [BlockFn.applyVar] at h
  split at h
  · rename_i hst
    obtain ⟨rfl, rfl⟩ := hst
    exact Term.numCalls_relvl _ h
  · cases h

theorem BlockFn.numCalls_applyNeu {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks}
    {js : JCtx ks} {ℓn : Nat} (f : BlockFn Δ Φ (.fn σ τ)) (n : Neu Δ Φ Γ σ ℓn)
    {r : (o' : Lvl) × Term Δ d Φ Γ τ js o'} (h : f.applyNeu n = some r) :
    r.2.numCalls = f.body.numCalls := by
  unfold BlockFn.applyNeu at h
  split at h
  · rename_i x
    exact BlockFn.numCalls_applyVar f x h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    simp only [Term.numCalls, Comp.numCalls]
    rw [BlockFn.numCalls_applyVar f _ hr']
    omega

mutual
theorem Term.numCalls_retToJump {σ τ : Ty ks} : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {js js' : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ σ js o) → (m : JMap js js') →
    (j : JVar js' σ) → (t.retToJump (τ := τ) m j).numCalls = t.numCalls
  | _, _, _, _, _, _, .ret _, _, _ => rfl
  | _, _, _, _, _, _, .letV _ _ b, m, j => by
      simp only [Term.retToJump, Term.numCalls, Term.numCalls_retToJump b m j]
  | _, _, _, _, _, _, .letE _ _ b, m, j => by
      simp only [Term.retToJump, Term.numCalls, Term.numCalls_retToJump b m j]
  | _, _, _, _, _, _, .record_casesOn _ _ b, m, j => by
      simp only [Term.retToJump, Term.numCalls, Term.numCalls_retToJump b m j]
  | _, _, _, _, _, _, .branch br, m, j => by
      simp only [Term.retToJump, Term.numCalls, Branch.numCalls_retToJump br m j]
  | _, _, _, _, _, _, .jump _ _, _, _ => rfl
  termination_by structural _ _ _ _ _ _ t => t
theorem Branch.numCalls_retToJump {σ τ : Ty ks} : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {js js' : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ σ js ℓ) → (m : JMap js js') →
    (j : JVar js' σ) → (br.retToJump (τ := τ) m j).numCalls = br.numCalls
  | _, _, _, _, _, _, .ite _ t e, m, j => by
      simp only [Branch.retToJump, Branch.numCalls, Term.numCalls_retToJump t m j,
        Term.numCalls_retToJump e m j]
  | _, _, _, _, _, _, .enum_casesOn _ bs, m, j => by
      simp only [Branch.retToJump, Branch.numCalls]
      congr 1; funext i; exact Term.numCalls_retToJump (bs i) m j
  | _, _, _, _, _, _, .union_casesOn _ bs, m, j => by
      simp only [Branch.retToJump, Branch.numCalls, Branches.numCalls_retToJump bs m j]
  | _, _, _, _, _, _, .join _ _ _ body main, m, j => by
      simp only [Branch.retToJump, Branch.numCalls, Term.numCalls_retToJump body m j,
        Branch.numCalls_retToJump main (m.lift _) (.tail j)]
  termination_by structural _ _ _ _ _ _ br => br
theorem Branches.numCalls_retToJump {σ τ : Ty ks} : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {js js' : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs σ js o) → (m : JMap js js') → (j : JVar js' σ) →
    (br.retToJump (τ := τ) m j).numCalls = br.numCalls
  | _, _, _, _, _, _, _, _, .two _ _ b₁ b₂, m, j => by
      simp only [Branches.retToJump, Branches.numCalls, Term.numCalls_retToJump b₁ m j,
        Term.numCalls_retToJump b₂ m j]
  | _, _, _, _, _, _, _, _, .cons _ b bs, m, j => by
      simp only [Branches.retToJump, Branches.numCalls, Term.numCalls_retToJump b m j,
        Branches.numCalls_retToJump bs m j]
  termination_by structural _ _ _ _ _ _ _ _ br => br
end

end LeanScript

end
