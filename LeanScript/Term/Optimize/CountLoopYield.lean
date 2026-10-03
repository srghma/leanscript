module

public import LeanScript.Term.Optimize.LoopYield
public import LeanScript.Term.Optimize.CountJoinCtor

@[expose] public section

set_option autoImplicit false

/-!
# Writing a loop over the field of its state adds no call

`Term.numCalls_loopYield`: `Term.loopYield` (`LeanScript.Term.Optimize.LoopYield`) never adds
a call (the rewrite of a loop is only kept when it adds none).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

theorem Term.numCalls_loopYieldLet {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ τ' : Ty ks}
    {js : JCtx ks} {ℓ : Nat} {o' : Lvl} (u : Usage1ω) (c : Comp Δ d Φ Γ τ ℓ)
    (b : Term Δ d Φ (⟨τ, u.toUsage01ω, d⟩ :: Γ) τ' js o') :
    (Term.loopYieldLet u c b).2.numCalls ≤ c.numCalls + b.numCalls := by
  cases c with
  | nat_rec n z s hl0 =>
      simp only [Term.loopYieldLet]
      split
      · exact Nat.le_refl _
      · rename_i Y _
        dsimp only
        split
        · exact Nat.le_refl _
        · rename_i a _
          dsimp only
          split
          · exact Nat.le_refl _
          · rename_i ℓ' hl
            dsimp only
            split
            · exact Nat.le_refl _
            · rename_i b' hb
              dsimp only
              by_cases hc : (Comp.nat_rec n a.snd Y.body hl).numCalls + b'.snd.numCalls ≤
                (Comp.nat_rec n z s hl0).numCalls + b.numCalls
              · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
                exact hc
              · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
                exact Nat.le_refl _
  | _ => exact Nat.le_refl _

theorem Term.numCalls_recordEta {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks}
    {fs : Fields ks} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat} {o' : Lvl} (us : List Usage01ω)
    (n : Neu Δ Φ Γ (.record t fs) ℓ)
    (b : Term Δ d Φ (UCtx.annot d (t :: fs.toList) us ++ Γ) τ js o') :
    (Term.recordEta us n b).2.numCalls ≤ (Term.record_casesOn us n b).numCalls := by
  unfold Term.recordEta
  by_cases h : τ = Ty.record t fs
  · subst h
    rw [dite_eq_left_of_eq_true (eq_true rfl)]
    cases b with
    | ret e =>
        dsimp only
        rcases e.recordLit? with _ | ⟨o₂, args⟩
        · exact Nat.le_refl _
        · dsimp only
          by_cases hv : args.areVars (FieldVars.ofAnnot Γ d (t :: fs.toList) us) = true
          · rw [ite_eq_left_of_eq_true _ _ (eq_true hv)]
            simp [Term.numCalls]
          · rw [ite_eq_right_of_eq_false _ _ (eq_false hv)]
            exact Nat.le_refl _
    | _ => exact Nat.le_refl _
  · rw [dite_eq_right_of_eq_false (eq_false h)]
    exact Nat.le_refl _

mutual
theorem Val.numCalls_yieldWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → v.yieldWalk.numCalls ≤ v.numCalls
  | _, _, _, _, _, .lam b => by simp only [Val.yieldWalk, Val.numCalls]; exact Body.numCalls_yieldWalk b
  | _, _, _, _, _, .thunk_mk b => by
      simp only [Val.yieldWalk, Val.numCalls]; exact Body.numCalls_yieldWalk b
  | _, _, _, _, _, .lazy_mk b => by
      simp only [Val.yieldWalk, Val.numCalls]; exact Body.numCalls_yieldWalk b
  | _, _, _, _, _, .record_mk _ => Nat.le_refl _
  | _, _, _, _, _, .union_mk _ _ => Nat.le_refl _
  | _, _, _, _, _, .array_mk _ => Nat.le_refl _
  | _, _, _, _, _, .list_mk _ => Nat.le_refl _
  | _, _, _, _, _, .data_in _ _ _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
theorem Body.numCalls_yieldWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → b.yieldWalk.numCalls ≤ b.numCalls
  | _, _, _, _, _, _, .closed t => by
      simp only [Body.yieldWalk, Body.numCalls]; exact Term.numCalls_yieldWalk t
  | _, _, _, _, _, _, .opened t _ => by
      simp only [Body.yieldWalk, Body.numCalls]
      exact Term.numCalls_keepLvl t _ (Term.numCalls_yieldWalk t)
  termination_by structural _ _ _ _ _ _ x => x
theorem Comp.numCalls_yieldWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → c.yieldWalk.numCalls ≤ c.numCalls
  | _, _, _, _, _, .app _ _ _ => Nat.le_refl _
  | _, _, _, _, _, .share _ => Nat.le_refl _
  | _, _, _, _, _, .nat_rec n z s _ => by
      simp only [Comp.yieldWalk, Comp.numCalls]; exact Body.numCalls_yieldWalk s
  | _, _, _, _, _, .array_foldl a z s _ => by
      simp only [Comp.yieldWalk, Comp.numCalls]; exact Body.numCalls_yieldWalk s
  | _, _, _, _, _, .data_rec b ρt us brs j e _ => by
      simp only [Comp.yieldWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_yieldWalk (brs i))
  | _, _, _, _, _, .data_brec b ρt k us brs j e _ => by
      simp only [Comp.yieldWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_yieldWalk (brs i))
  | _, _, _, _, _, .thunk_force _ => Nat.le_refl _
  | _, _, _, _, _, .lazy_force _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
theorem Term.numCalls_yieldWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → t.yieldWalk.2.numCalls ≤ t.numCalls
  | _, _, _, _, _, _, .ret _ => Nat.le_refl _
  | _, _, _, _, _, _, .letV u v b => by
      have hv := Val.numCalls_yieldWalk v
      have hb := Term.numCalls_yieldWalk b
      simp only [Term.yieldWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .letE u c b => by
      have hc := Comp.numCalls_yieldWalk c
      have hb := Term.numCalls_yieldWalk b
      have h := Term.numCalls_loopYieldLet u c.yieldWalk b.yieldWalk.2
      simp only [Term.yieldWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .record_casesOn us n b => by
      have h := Term.numCalls_recordEta us n b.yieldWalk.2
      have hb := Term.numCalls_yieldWalk b
      simp only [Term.yieldWalk, Term.numCalls] at h ⊢; omega
  | _, _, _, _, _, _, .branch br => by
      simp only [Term.yieldWalk, Term.numCalls]; exact Branch.numCalls_yieldWalk br
  | _, _, _, _, _, _, .jump _ _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ _ x => x
theorem Branch.numCalls_yieldWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) →
    br.yieldWalk.2.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, .ite c t e => by
      have h₁ := Term.numCalls_yieldWalk t
      have h₂ := Term.numCalls_yieldWalk e
      simp only [Branch.yieldWalk, Branch.numCalls]; omega
  | _, _, _, _, _, _, .enum_casesOn e bs => by
      simp only [Branch.yieldWalk, Branch.numCalls]
      exact Fin.sumNat_le _ (fun i => Term.numCalls_yieldWalk (bs i))
  | _, _, _, _, _, _, .union_casesOn e bs => by
      simp only [Branch.yieldWalk, Branch.numCalls]
      exact Branches.numCalls_yieldWalk bs
  | _, _, _, _, _, _, .join σ u uₓ body main => by
      have h₁ := Term.numCalls_yieldWalk body
      have h₂ := Branch.numCalls_yieldWalk main
      simp only [Branch.yieldWalk, Branch.numCalls]; omega
  termination_by structural _ _ _ _ _ _ x => x
theorem Branches.numCalls_yieldWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → br.yieldWalk.2.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ => by
      have h₁ := Term.numCalls_yieldWalk b₁
      have h₂ := Term.numCalls_yieldWalk b₂
      simp only [Branches.yieldWalk, Branches.numCalls]; omega
  | _, _, _, _, _, _, _, _, .cons us b bs => by
      have h₁ := Term.numCalls_yieldWalk b
      have h₂ := Branches.numCalls_yieldWalk bs
      simp only [Branches.yieldWalk, Branches.numCalls]; omega
  termination_by structural _ _ _ _ _ _ _ _ x => x
end

/-- **Writing the loops whose state is always the same constructor over its field never adds
    calls.** -/
theorem Term.numCalls_loopYield {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} {o : Lvl} (t : Term Δ d Φ Γ τ js o) : t.loopYield.numCalls ≤ t.numCalls :=
  Term.numCalls_keepLvl t _ (Term.numCalls_yieldWalk t)

end LeanScript

end
