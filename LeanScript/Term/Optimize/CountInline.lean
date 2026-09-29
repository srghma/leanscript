module

public import LeanScript.Term.Optimize.Inline
public import LeanScript.Term.Optimize.CountRename

@[expose] public section

set_option autoImplicit false

/-!
# Inlining known closures never adds calls

`Term.numCalls_inlineKnown`: a call is either kept or replaced by a shared neutral
expression, which is not a call.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

theorem PExpr.numCalls_asShare {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} :
    {o' : Lvl} → (p : PExpr Δ Φ Γ τ o') → {c : Comp Δ d Φ Γ τ ℓ} → p.asShare = some c →
    c.numCalls = 0
  | _, .neu _, c, h => by
      simp only [PExpr.asShare] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h; rfl
      · cases h
  | _, .kvar _, _, h => by simp [PExpr.asShare] at h
  | _, .lit _ _, _, h => by simp [PExpr.asShare] at h
  | _, .enum_mk _ _, _, h => by simp [PExpr.asShare] at h
  | _, .record_mk _, _, h => by simp [PExpr.asShare] at h
  | _, .union_mk _ _, _, h => by simp [PExpr.asShare] at h
  | _, .array_mk _, _, h => by simp [PExpr.asShare] at h
  | _, .list_mk _, _, h => by simp [PExpr.asShare] at h
  | _, .data_in _ _ _, _, h => by simp [PExpr.asShare] at h

theorem Comp.numCalls_inlApp {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {of oa : Lvl}
    {ℓ : Nat} (I : KInfo Δ Φ) (f : PExpr Δ Φ Γ (.fn σ τ) of) (a : PExpr Δ Φ Γ σ oa)
    (h : Lvl.meet of oa = some ℓ) : (Comp.inlApp (d := d) I f a h).numCalls ≤ 1 := by
  cases f with
  | neu n => exact Nat.le_refl _
  | kvar k =>
      simp only [Comp.inlApp]
      cases hk : I.get k with
      | none => exact Nat.le_refl _
      | some e =>
          simp only [Option.bind_some]
          cases he : e.apply a with
          | none => exact Nat.le_refl _
          | some r =>
              simp only [Option.bind_some]
              cases hc : r.2.asShare (d := d) (ℓ := ℓ) with
              | none => exact Nat.le_refl _
              | some c =>
                  simp only [Option.getD_some]
                  rw [PExpr.numCalls_asShare _ hc]; exact Nat.zero_le _

mutual
theorem Val.numCalls_inlWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → (I : KInfo Δ Φ) → (v.inlWalk I).numCalls ≤ v.numCalls
  | _, _, _, _, _, .lam b, I => by
      simp only [Val.inlWalk, Val.numCalls]; exact Body.numCalls_inlWalk b I
  | _, _, _, _, _, .thunk_mk b, I => by
      simp only [Val.inlWalk, Val.numCalls]; exact Body.numCalls_inlWalk b I
  | _, _, _, _, _, .lazy_mk b, I => by
      simp only [Val.inlWalk, Val.numCalls]; exact Body.numCalls_inlWalk b I
  | _, _, _, _, _, .record_mk _, _ => Nat.le_refl _
  | _, _, _, _, _, .union_mk _ _, _ => Nat.le_refl _
  | _, _, _, _, _, .array_mk _, _ => Nat.le_refl _
  | _, _, _, _, _, .list_mk _, _ => Nat.le_refl _
  | _, _, _, _, _, .data_in _ _ _, _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
theorem Body.numCalls_inlWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (I : KInfo Δ Φ) → (b.inlWalk I).numCalls ≤ b.numCalls
  | _, _, _, _, _, _, .closed t, I => by
      simp only [Body.inlWalk, Body.numCalls]; exact Term.numCalls_inlWalk t _
  | _, _, _, _, _, _, .opened t _, I => by
      simp only [Body.inlWalk, Body.numCalls]; exact Term.numCalls_inlWalk t _
  termination_by structural _ _ _ _ _ _ x => x
theorem Comp.numCalls_inlWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (I : KInfo Δ Φ) → (c.inlWalk I).numCalls ≤ c.numCalls
  | _, _, _, _, _, .app f a h, I => by
      simp only [Comp.inlWalk, Comp.numCalls]; exact Comp.numCalls_inlApp I f a h
  | _, _, _, _, _, .share _, _ => Nat.le_refl _
  | _, _, _, _, _, .nat_rec n z s _, I => by
      simp only [Comp.inlWalk, Comp.numCalls]; exact Body.numCalls_inlWalk s I
  | _, _, _, _, _, .array_foldl a z s _, I => by
      simp only [Comp.inlWalk, Comp.numCalls]; exact Body.numCalls_inlWalk s I
  | _, _, _, _, _, .data_rec b ρt us brs j e _, I => by
      simp only [Comp.inlWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_inlWalk (brs i) I)
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, I => by
      simp only [Comp.inlWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_inlWalk (brs i) I)
  | _, _, _, _, _, .thunk_force _, _ => Nat.le_refl _
  | _, _, _, _, _, .lazy_force _, _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
theorem Term.numCalls_inlWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → (I : KInfo Δ Φ) →
    (t.inlWalk I).numCalls ≤ t.numCalls
  | _, _, _, _, _, _, .ret _, _ => Nat.le_refl _
  | _, _, _, _, _, _, .letV u v b, I => by
      have hv := Val.numCalls_inlWalk v I
      have hb := Term.numCalls_inlWalk b (KInfo.cons (v.inlWalk I).exprFn? I)
      simp only [Term.inlWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .letE u c b, I => by
      have hc := Comp.numCalls_inlWalk c I
      have hb := Term.numCalls_inlWalk b I
      simp only [Term.inlWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .record_casesOn us n b, I => by
      simp only [Term.inlWalk, Term.numCalls]; exact Term.numCalls_inlWalk b I
  | _, _, _, _, _, _, .branch br, I => by
      simp only [Term.inlWalk, Term.numCalls]; exact Branch.numCalls_inlWalk br I
  | _, _, _, _, _, _, .jump _ _, _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ _ x => x
theorem Branch.numCalls_inlWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → (I : KInfo Δ Φ) →
    (br.inlWalk I).numCalls ≤ br.numCalls
  | _, _, _, _, _, _, .ite c t e, I => by
      have h₁ := Term.numCalls_inlWalk t I
      have h₂ := Term.numCalls_inlWalk e I
      simp only [Branch.inlWalk, Branch.numCalls]; omega
  | _, _, _, _, _, _, .enum_casesOn e bs, I => by
      simp only [Branch.inlWalk, Branch.numCalls]
      exact Fin.sumNat_le _ (fun i => Term.numCalls_inlWalk (bs i) I)
  | _, _, _, _, _, _, .union_casesOn e bs, I => by
      simp only [Branch.inlWalk, Branch.numCalls]; exact Branches.numCalls_inlWalk bs I
  | _, _, _, _, _, _, .join σ u uₓ body main, I => by
      have h₁ := Term.numCalls_inlWalk body I
      have h₂ := Branch.numCalls_inlWalk main I
      simp only [Branch.inlWalk, Branch.numCalls]; omega
  termination_by structural _ _ _ _ _ _ x => x
theorem Branches.numCalls_inlWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (I : KInfo Δ Φ) → (br.inlWalk I).numCalls ≤ br.numCalls
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, I => by
      have h₁ := Term.numCalls_inlWalk b₁ I
      have h₂ := Term.numCalls_inlWalk b₂ I
      simp only [Branches.inlWalk, Branches.numCalls]; omega
  | _, _, _, _, _, _, _, _, .cons us b bs, I => by
      have h₁ := Term.numCalls_inlWalk b I
      have h₂ := Branches.numCalls_inlWalk bs I
      simp only [Branches.inlWalk, Branches.numCalls]; omega
  termination_by structural _ _ _ _ _ _ _ _ x => x
end

/-- **Inlining known closures never adds calls.** -/
theorem Term.numCalls_inlineKnown {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} {o : Lvl} (t : Term Δ d Φ Γ τ js o) :
    t.inlineKnown.numCalls ≤ t.numCalls :=
  Term.numCalls_inlWalk t _

end LeanScript

end
