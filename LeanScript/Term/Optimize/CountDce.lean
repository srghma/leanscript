module

public import LeanScript.Term.Optimize.CountRename
public import LeanScript.Term.Optimize.Dce

@[expose] public section

set_option autoImplicit false

/-!
# Dead-code elimination does not add calls

`Term.dce` only drops bindings and join points and re-annotates usages (by renamings), so the
result has at most as many calls (`Term.numCalls`) as the original.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

@[simp] theorem Term.numCalls_castLvl {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} {o o' : Lvl} (h : o = o') (t : Term Δ d Φ Γ τ js o) :
    (t.castLvl h).numCalls = t.numCalls := by
  subst h; rfl

@[simp] theorem Branch.numCalls_castLvl {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} {ℓ ℓ' : Nat} (h : ℓ = ℓ') (br : Branch Δ d Φ Γ τ js ℓ) :
    (br.castLvl h).numCalls = br.numCalls := by
  subst h; rfl

theorem Body.numCalls_reuse1 {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks}
    {u : Usage01ω} {ℓ : Nat} {o : Lvl} {u' : Usage01ω} {b : Body Δ d Φ Γ [⟨σ, u, ℓ⟩] τ o}
    {b' : Body Δ d Φ Γ [⟨σ, u', ℓ⟩] τ o} (h : b.reuse1 u' = some b') :
    b'.numCalls = b.numCalls := by
  cases b with
  | closed t =>
      simp only [Body.reuse1, Option.map_eq_some_iff] at h
      obtain ⟨t', ht, rfl⟩ := h
      simp only [Body.numCalls]; exact Term.numCalls_rename t ht
  | opened t =>
      simp only [Body.reuse1, Option.map_eq_some_iff] at h
      obtain ⟨t', ht, rfl⟩ := h
      simp only [Body.numCalls]; exact Term.numCalls_rename t ht

mutual
theorem Val.numCalls_dce : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → v.dce.numCalls ≤ v.numCalls
  | _, _, _, _, _, .lam b => by
      simp only [Val.dce]
      split
      · rename_i b' hb
        simp only [Val.numCalls]
        rw [Body.numCalls_reuse1 hb]; exact Body.numCalls_dce b
      · simp only [Val.numCalls]; exact Body.numCalls_dce b
  | _, _, _, _, _, .thunk_mk b => by
      simp only [Val.dce, Val.numCalls]; exact Body.numCalls_dce b
  | _, _, _, _, _, .lazy_mk b => by
      simp only [Val.dce, Val.numCalls]; exact Body.numCalls_dce b
  | _, _, _, _, _, .record_mk _ => Nat.le_refl _
  | _, _, _, _, _, .union_mk _ _ => Nat.le_refl _
  | _, _, _, _, _, .array_mk _ => Nat.le_refl _
  | _, _, _, _, _, .list_mk _ => Nat.le_refl _
  | _, _, _, _, _, .data_in _ _ _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
theorem Body.numCalls_dce : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → b.dce.numCalls ≤ b.numCalls
  | _, _, _, _, _, _, .closed t => by
      simp only [Body.dce, Body.numCalls]; exact Term.numCalls_dce t
  | _, _, _, _, _, _, .opened t _ => by
      simp only [Body.dce, Body.numCalls]; exact Term.numCalls_dce t
  termination_by structural _ _ _ _ _ _ x => x
theorem Comp.numCalls_dce : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → c.dce.numCalls ≤ c.numCalls
  | _, _, _, _, _, .app _ _ _ => Nat.le_refl _
  | _, _, _, _, _, .share _ => Nat.le_refl _
  | _, _, _, _, _, .nat_rec n z s _ => by
      simp only [Comp.dce, Comp.numCalls]; exact Body.numCalls_dce s
  | _, _, _, _, _, .array_foldl a z s _ => by
      simp only [Comp.dce, Comp.numCalls]; exact Body.numCalls_dce s
  | _, _, _, _, _, .data_rec b ρt us brs j e _ => by
      simp only [Comp.dce, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_dce (brs i))
  | _, _, _, _, _, .data_brec b ρt k us brs j e _ => by
      simp only [Comp.dce, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_dce (brs i))
  | _, _, _, _, _, .thunk_force _ => Nat.le_refl _
  | _, _, _, _, _, .lazy_force _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
/-- **Dead-code elimination does not add calls.** -/
theorem Term.numCalls_dce : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → t.dce.numCalls ≤ t.numCalls
  | _, _, _, _, _, _, .ret _ => Nat.le_refl _
  | _, _, _, _, _, _, .letV u v b => by
      have hv := Val.numCalls_dce v
      have hb := Term.numCalls_dce b
      simp only [Term.dce]
      split
      · split
        · split
          · rename_i b' hb'
            simp only [Term.numCalls_castLvl, Term.numCalls_rename _ hb', Term.numCalls]
            omega
          · simp only [Term.numCalls]; omega
        · simp only [Term.numCalls]; omega
      · split
        · rename_i b' hb'
          simp only [Term.numCalls, Term.numCalls_rename _ hb']; omega
        · simp only [Term.numCalls]; omega
  | _, _, _, _, _, _, .letE u c b => by
      have hc := Comp.numCalls_dce c
      have hb := Term.numCalls_dce b
      simp only [Term.dce]
      split
      · split
        · split
          · rename_i b' hb'
            simp only [Term.numCalls_castLvl, Term.numCalls_rename _ hb', Term.numCalls]
            omega
          · simp only [Term.numCalls]; omega
        · simp only [Term.numCalls]; omega
      · split
        · rename_i b' hb'
          simp only [Term.numCalls, Term.numCalls_rename _ hb']; omega
        · simp only [Term.numCalls]; omega
  | _, _, _, _, _, _, .record_casesOn us n b => by
      simp only [Term.dce, Term.numCalls]; exact Term.numCalls_dce b
  | _, _, _, _, _, _, .branch br => by
      simp only [Term.dce, Term.numCalls]; exact Branch.numCalls_dce br
  | _, _, _, _, _, _, .jump _ _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ _ x => x
theorem Branch.numCalls_dce : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → br.dce.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, .ite c t e => by
      have ht := Term.numCalls_dce t
      have he := Term.numCalls_dce e
      simp only [Branch.dce, Branch.numCalls]; omega
  | _, _, _, _, _, _, .enum_casesOn e bs => by
      simp only [Branch.dce, Branch.numCalls]
      exact Fin.sumNat_le _ (fun i => Term.numCalls_dce (bs i))
  | _, _, _, _, _, _, .union_casesOn e bs => by
      simp only [Branch.dce, Branch.numCalls]; exact Branches.numCalls_dce bs
  | _, _, _, _, _, _, .join σ u uₓ body main => by
      have hb := Term.numCalls_dce body
      have hm := Branch.numCalls_dce main
      simp only [Branch.dce]
      split
      · split
        · split
          · rename_i main' hm'
            simp only [Branch.numCalls_castLvl, Branch.numCalls_rename _ hm', Branch.numCalls]
            omega
          · simp only [Branch.numCalls]; omega
        · simp only [Branch.numCalls]; omega
      · split
        · rename_i main' body' hm' hb'
          simp only [Branch.numCalls, Branch.numCalls_rename _ hm', Term.numCalls_rename _ hb']
          omega
        · rename_i main' hm' _
          simp only [Branch.numCalls, Branch.numCalls_rename _ hm']; omega
        · simp only [Branch.numCalls]; omega
  termination_by structural _ _ _ _ _ _ x => x
theorem Branches.numCalls_dce : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → br.dce.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ => by
      have h₁ := Term.numCalls_dce b₁
      have h₂ := Term.numCalls_dce b₂
      simp only [Branches.dce, Branches.numCalls]; omega
  | _, _, _, _, _, _, _, _, .cons us b bs => by
      have h₁ := Term.numCalls_dce b
      have h₂ := Branches.numCalls_dce bs
      simp only [Branches.dce, Branches.numCalls]; omega
  termination_by structural _ _ _ _ _ _ _ _ x => x
end

end LeanScript

end
