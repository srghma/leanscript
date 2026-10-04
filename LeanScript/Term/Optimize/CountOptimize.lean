module

public import LeanScript.Term.Optimize.CountDce
public import LeanScript.Term.Optimize.Basic
public import LeanScript.Term.Optimize.CountInline
public import LeanScript.Term.Optimize.CountInlineRet
public import LeanScript.Term.Optimize.CountJoinCtor
public import LeanScript.Term.Optimize.CountLoopYield
public import LeanScript.Term.Optimize.CountCondJump

@[expose] public section

set_option autoImplicit false

/-!
# The optimiser never adds calls

Every rewrite of `Term.optimize` (copy propagation, shared answers, dead case analysis, common
subexpression elimination, identical branches, trivial join points, dead-code elimination)
only removes work: the optimised statement has at most as many calls (`Term.numCalls`: calls
`f a`, `t.get`, `t ()`, counted syntactically) as the original — `Term.numCalls_optimize`,
`Term.numCalls_optimizeN`.  Together with `Term.optimize_eval` (the value does not change),
this says the optimiser is a correct and non-pessimising transformation.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## The first walk (`Term.simp`) -/

theorem Term.numCalls_shareTail {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks}
    {js : JCtx ks} {ℓ : Nat} {o' : Lvl} (u : Usage1ω) (n : Neu Δ Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') :
    (Term.shareTail u n b).numCalls ≤ b.numCalls := by
  unfold Term.shareTail
  split
  · split
    · split
      · split <;> simp [Term.numCalls, Comp.numCalls]
      · simp [Term.numCalls, Comp.numCalls]
    · split
      · split <;> simp [Term.numCalls, Comp.numCalls]
      · simp [Term.numCalls, Comp.numCalls]
    all_goals simp [Term.numCalls, Comp.numCalls]
  · simp [Term.numCalls, Comp.numCalls]

theorem Term.numCalls_shareLet {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks}
    {js : JCtx ks} {ℓ : Nat} {o' : Lvl} (u : Usage1ω) (n : Neu Δ Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') :
    (Term.shareLet u n b).numCalls ≤ b.numCalls := by
  unfold Term.shareLet
  split
  · split
    · split
      · rename_i b' hb'
        split
        · simp [Term.numCalls_rename _ hb']
        · exact Term.numCalls_shareTail u _ b
      · exact Term.numCalls_shareTail u _ b
    · exact Term.numCalls_shareTail u _ b
  · exact Term.numCalls_shareTail u _ b

theorem Term.numCalls_mkLetE {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks}
    {js : JCtx ks} {ℓ : Nat} {o' : Lvl} (u : Usage1ω) (c : Comp Δ d Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') :
    (Term.mkLetE u c b).numCalls ≤ c.numCalls + b.numCalls := by
  unfold Term.mkLetE
  split
  · rename_i n
    have := Term.numCalls_shareLet u n b
    simp only [Comp.numCalls]; omega
  · simp [Term.numCalls]

theorem Term.numCalls_mkRecordCasesOn {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks}
    {fs : Fields ks} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat} {o' : Lvl} (us : List Usage01ω)
    (n : Neu Δ Φ Γ (.record t fs) ℓ)
    (b : Term Δ d Φ (UCtx.annot d (t :: fs.toList) us ++ Γ) τ js o') :
    (Term.mkRecordCasesOn us n b).numCalls ≤ b.numCalls := by
  unfold Term.mkRecordCasesOn
  split
  · rename_i b' hb'
    split
    · simp [Term.numCalls_rename _ hb']
    · simp [Term.numCalls]
  · simp [Term.numCalls]

mutual
theorem Val.numCalls_simp : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → v.simp.numCalls ≤ v.numCalls
  | _, _, _, _, _, .lam b => by simp only [Val.simp, Val.numCalls]; exact Body.numCalls_simp b
  | _, _, _, _, _, .thunk_mk b => by
      simp only [Val.simp, Val.numCalls]; exact Body.numCalls_simp b
  | _, _, _, _, _, .lazy_mk b => by
      simp only [Val.simp, Val.numCalls]; exact Body.numCalls_simp b
  | _, _, _, _, _, .record_mk _ => Nat.le_refl _
  | _, _, _, _, _, .union_mk _ _ => Nat.le_refl _
  | _, _, _, _, _, .array_mk _ => Nat.le_refl _
  | _, _, _, _, _, .list_mk _ => Nat.le_refl _
  | _, _, _, _, _, .data_in _ _ _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
theorem Body.numCalls_simp : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → b.simp.numCalls ≤ b.numCalls
  | _, _, _, _, _, _, .closed t => by
      simp only [Body.simp, Body.numCalls]; exact Term.numCalls_simp t
  | _, _, _, _, _, _, .opened t _ => by
      simp only [Body.simp, Body.numCalls]; exact Term.numCalls_simp t
  termination_by structural _ _ _ _ _ _ x => x
theorem Comp.numCalls_simp : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → c.simp.numCalls ≤ c.numCalls
  | _, _, _, _, _, .app _ _ _ => Nat.le_refl _
  | _, _, _, _, _, .share _ => Nat.le_refl _
  | _, _, _, _, _, .nat_rec n z s _ => by
      simp only [Comp.simp, Comp.numCalls]; exact Body.numCalls_simp s
  | _, _, _, _, _, .array_foldl a z s _ => by
      simp only [Comp.simp, Comp.numCalls]; exact Body.numCalls_simp s
  | _, _, _, _, _, .data_rec b ρt us brs j e _ => by
      simp only [Comp.simp, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_simp (brs i))
  | _, _, _, _, _, .data_brec b ρt k us brs j e _ => by
      simp only [Comp.simp, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_simp (brs i))
  | _, _, _, _, _, .thunk_force _ => Nat.le_refl _
  | _, _, _, _, _, .lazy_force _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
/-- **The first walk of the optimiser does not add calls.** -/
theorem Term.numCalls_simp : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → t.simp.numCalls ≤ t.numCalls
  | _, _, _, _, _, _, .ret _ => Nat.le_refl _
  | _, _, _, _, _, _, .letV u v b => by
      have hv := Val.numCalls_simp v
      have hb := Term.numCalls_simp b
      simp only [Term.simp, Term.numCalls]; omega
  | _, _, _, _, _, _, .letE u c b => by
      have hc := Comp.numCalls_simp c
      have hb := Term.numCalls_simp b
      have := Term.numCalls_mkLetE u c.simp b.simp
      simp only [Term.simp, Term.numCalls]; omega
  | _, _, _, _, _, _, .record_casesOn us n b => by
      have hb := Term.numCalls_simp b
      have := Term.numCalls_mkRecordCasesOn us n b.simp
      simp only [Term.simp, Term.numCalls]; omega
  | _, _, _, _, _, _, .branch br => by
      simp only [Term.simp, Term.numCalls]; exact Branch.numCalls_simp br
  | _, _, _, _, _, _, .jump _ _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ _ x => x
theorem Branch.numCalls_simp : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → br.simp.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, .ite c t e => by
      have ht := Term.numCalls_simp t
      have he := Term.numCalls_simp e
      simp only [Branch.simp, Branch.numCalls]; omega
  | _, _, _, _, _, _, .enum_casesOn e bs => by
      simp only [Branch.simp, Branch.numCalls]
      exact Fin.sumNat_le _ (fun i => Term.numCalls_simp (bs i))
  | _, _, _, _, _, _, .union_casesOn e bs => by
      simp only [Branch.simp, Branch.numCalls]; exact Branches.numCalls_simp bs
  | _, _, _, _, _, _, .join σ u uₓ body main => by
      have hb := Term.numCalls_simp body
      have hm := Branch.numCalls_simp main
      simp only [Branch.simp, Branch.numCalls]; omega
  termination_by structural _ _ _ _ _ _ x => x
theorem Branches.numCalls_simp : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → br.simp.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ => by
      have h₁ := Term.numCalls_simp b₁
      have h₂ := Term.numCalls_simp b₂
      simp only [Branches.simp, Branches.numCalls]; omega
  | _, _, _, _, _, _, _, _, .cons us b bs => by
      have h₁ := Term.numCalls_simp b
      have h₂ := Branches.numCalls_simp bs
      simp only [Branches.simp, Branches.numCalls]; omega
  termination_by structural _ _ _ _ _ _ _ _ x => x
end

/-! ## Common subexpressions -/

section Cse
variable {σ : Ty ks}

mutual
theorem Term.numCalls_cse : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (x : UVar Γ σ d) → (s : SimpleComp Φ Γ σ) →
    (t : Term Δ d Φ Γ τ js o) → (Term.cse x s t).2.numCalls ≤ t.numCalls
  | _, _, _, _, _, _, _, _, .ret _ => Nat.le_refl _
  | _, _, _, _, _, _, x, s, .letV u v b => by
      have := Term.numCalls_cse x (s.wkK _) b
      simp only [Term.cse, Term.numCalls]; omega
  | _, _, _, _, _, _, x, s, .letE (σ := σ') u c b => by
      have hb := Term.numCalls_cse x.tail (s.wkU _) b
      simp only [Term.cse]
      cases hs' : SimpleComp.ofComp? c with
      | none => simp only [Term.numCalls]; omega
      | some s' =>
        simp only
        by_cases h : σ' = σ ∧ s'.key = s.key
        · rw [dite_eq_left h]
          split
          · rename_i b' hb'
            rw [Term.numCalls_rename _ hb']; simp only [Term.numCalls]; omega
          · simp only [Term.numCalls]; omega
        · rw [dite_eq_right h]; simp only [Term.numCalls]; omega
  | _, _, _, _, _, _, x, s, .record_casesOn us n b => by
      have := Term.numCalls_cse (x.wkN _) (s.wkUN _) b
      simp only [Term.cse, Term.numCalls]; omega
  | _, _, _, _, _, _, x, s, .branch br => by
      simp only [Term.cse, Term.numCalls]; exact Branch.numCalls_cse x s br
  | _, _, _, _, _, _, _, _, .jump _ _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ _ _ _ t => t
theorem Branch.numCalls_cse : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (x : UVar Γ σ d) → (s : SimpleComp Φ Γ σ) →
    (br : Branch Δ d Φ Γ τ js ℓ) → (Branch.cse x s br).2.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, x, s, .ite c t e => by
      have ht := Term.numCalls_cse x s t
      have he := Term.numCalls_cse x s e
      simp only [Branch.cse, Branch.numCalls]; omega
  | _, _, _, _, _, _, x, s, .enum_casesOn e bs => by
      simp only [Branch.cse, Branch.numCalls]
      exact Fin.sumNat_le _ (fun i => Term.numCalls_cse x s (bs i))
  | _, _, _, _, _, _, x, s, .union_casesOn e bs => by
      simp only [Branch.cse, Branch.numCalls]; exact Branches.numCalls_cse x s bs
  | _, _, _, _, _, _, x, s, .join σ' u uₓ body main => by
      have hb := Term.numCalls_cse x.tail (s.wkU _) body
      have hm := Branch.numCalls_cse x s main
      simp only [Branch.cse, Branch.numCalls]; omega
  termination_by structural _ _ _ _ _ _ _ _ br => br
theorem Branches.numCalls_cse : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (x : UVar Γ σ d) → (s : SimpleComp Φ Γ σ) → (br : Branches Δ d Φ Γ cs τ js o) →
    (Branches.cse x s br).2.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, _, _, x, s, .two us₁ us₂ b₁ b₂ => by
      have h₁ := Term.numCalls_cse (x.wkN _) (s.wkUN _) b₁
      have h₂ := Term.numCalls_cse (x.wkN _) (s.wkUN _) b₂
      simp only [Branches.cse, Branches.numCalls]; omega
  | _, _, _, _, _, _, _, _, x, s, .cons us b bs => by
      have h₁ := Term.numCalls_cse (x.wkN _) (s.wkUN _) b
      have h₂ := Branches.numCalls_cse x s bs
      simp only [Branches.cse, Branches.numCalls]; omega
  termination_by structural _ _ _ _ _ _ _ _ _ _ br => br
end

end Cse

theorem Term.numCalls_cseLetE {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks}
    {js : JCtx ks} {ℓ : Nat} {o' : Lvl} (u : Usage1ω) (c : Comp Δ d Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') :
    (Term.cseLetE u c b).numCalls ≤ c.numCalls + b.numCalls := by
  unfold Term.cseLetE
  cases hs : SimpleComp.ofComp? c with
  | none => simp [Term.numCalls]
  | some s =>
    simp only
    have := Term.numCalls_cse (.head (Usage1ω.toUsage01ω_ne_zero u)) (s.wkU _) b
    split
    · simp only [Term.numCalls_castLvl, Term.numCalls]; omega
    · simp [Term.numCalls]

/-! ## Identical branches and trivial join points -/

theorem Term.numCalls_mkIte {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {ℓ : Nat} {o₁ o₂ : Lvl} (c : Neu Δ Φ Γ .bool ℓ) (t : Term Δ d Φ Γ τ js o₁)
    (e : Term Δ d Φ Γ τ js o₂) :
    (Term.mkIte c t e).numCalls ≤ t.numCalls + e.numCalls := by
  unfold Term.mkIte
  split
  · split
    · split
      · simp [Term.numCalls]
      · unfold Term.condRet; split <;> simp [Term.numCalls, Branch.numCalls]
    · unfold Term.condRet; split <;> simp [Term.numCalls, Branch.numCalls]
  · simp [Term.numCalls, Branch.numCalls]

theorem Term.numCalls_mkBranch {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} {ℓ : Nat} (br : Branch Δ d Φ Γ τ js ℓ) :
    (Term.mkBranch br).numCalls ≤ br.numCalls := by
  cases br with
  | ite c t e => simpa [Term.mkBranch, Branch.numCalls] using Term.numCalls_mkIte c t e
  | _ => simp [Term.mkBranch, Term.numCalls]

section Inline
variable {σ τ : Ty ks}

theorem Repl.numCalls_term {Φ : KCtx ks} {Γ : UCtx ks} {d : Nat} {js : JCtx ks} {o : Lvl}
    (r : Repl Φ Γ σ τ) (e : PExpr Δ Φ Γ σ o) : (r.term (d := d) (js := js) e).2.numCalls = 0 := by
  cases r <;> rfl

mutual
theorem Term.numCalls_inl : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {js : JCtx ks} →
    {o : Lvl} → (jt : JVar js σ) → (r : Repl Φ Γ σ τ) → (t : Term Δ d Φ Γ τ js o) →
    (Term.inl jt r t).2.numCalls ≤ t.numCalls
  | _, _, _, _, _, _, _, .ret _ => Nat.le_refl _
  | _, _, _, _, _, jt, r, .letV u v b => by
      have := Term.numCalls_inl jt (r.wkK _) b
      simp only [Term.inl, Term.numCalls]; omega
  | _, _, _, _, _, jt, r, .letE u c b => by
      have := Term.numCalls_inl jt (r.wkU _) b
      simp only [Term.inl, Term.numCalls]; omega
  | _, _, _, _, _, jt, r, .record_casesOn us n b => by
      have := Term.numCalls_inl jt (r.wkUN _) b
      simp only [Term.inl, Term.numCalls]; omega
  | _, _, _, _, _, jt, r, .branch br => by
      simp only [Term.inl, Term.numCalls]; exact Branch.numCalls_inl jt r br
  | _, _, _, _, _, jt, r, .jump (σ := σ') j e => by
      simp only [Term.inl]
      by_cases h : σ' = σ ∧ j.index = jt.index
      · rw [dite_eq_left h, Repl.numCalls_term]; exact Nat.zero_le _
      · rw [dite_eq_right h]; exact Nat.le_refl _
  termination_by structural _ _ _ _ _ _ _ t => t
theorem Branch.numCalls_inl : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {js : JCtx ks} →
    {ℓ : Nat} → (jt : JVar js σ) → (r : Repl Φ Γ σ τ) → (br : Branch Δ d Φ Γ τ js ℓ) →
    (Branch.inl jt r br).2.numCalls ≤ br.numCalls
  | _, _, _, _, _, jt, r, .ite c t e => by
      have ht := Term.numCalls_inl jt r t
      have he := Term.numCalls_inl jt r e
      simp only [Branch.inl, Branch.numCalls]; omega
  | _, _, _, _, _, jt, r, .enum_casesOn e bs => by
      simp only [Branch.inl, Branch.numCalls]
      exact Fin.sumNat_le _ (fun i => Term.numCalls_inl jt r (bs i))
  | _, _, _, _, _, jt, r, .union_casesOn e bs => by
      simp only [Branch.inl, Branch.numCalls]; exact Branches.numCalls_inl jt r bs
  | _, _, _, _, _, jt, r, .join σ' u uₓ body main => by
      have hb := Term.numCalls_inl jt (r.wkU _) body
      have hm := Branch.numCalls_inl jt.tail r main
      simp only [Branch.inl, Branch.numCalls]; omega
  termination_by structural _ _ _ _ _ _ _ br => br
theorem Branches.numCalls_inl : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {js : JCtx ks} → {o : Lvl} →
    (jt : JVar js σ) → (r : Repl Φ Γ σ τ) → (br : Branches Δ d Φ Γ cs τ js o) →
    (Branches.inl jt r br).2.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, _, jt, r, .two us₁ us₂ b₁ b₂ => by
      have h₁ := Term.numCalls_inl jt (r.wkUN _) b₁
      have h₂ := Term.numCalls_inl jt (r.wkUN _) b₂
      simp only [Branches.inl, Branches.numCalls]; omega
  | _, _, _, _, _, _, _, jt, r, .cons us b bs => by
      have h₁ := Term.numCalls_inl jt (r.wkUN _) b
      have h₂ := Branches.numCalls_inl jt r bs
      simp only [Branches.inl, Branches.numCalls]; omega
  termination_by structural _ _ _ _ _ _ _ _ _ br => br
end

end Inline

theorem Branch.numCalls_mkJoin {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} {o : Lvl} {ℓ : Nat} (σ : Ty ks) (u : Usage1ω) (uₓ : Usage01ω)
    (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o) (main : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ) :
    (Branch.mkJoin σ u uₓ body main).numCalls ≤ body.numCalls + main.numCalls := by
  unfold Branch.mkJoin
  split
  · rename_i r _
    dsimp only
    split
    · have h1 := Branch.numCalls_dce
        ((Branch.join σ u uₓ body (Branch.inl .head r main).2).castLvl (by assumption))
      have h2 := Branch.numCalls_inl .head r main
      simp only [Branch.numCalls_castLvl, Branch.numCalls] at h1
      omega
    · simp [Branch.numCalls]
  · simp [Branch.numCalls]

/-! ## The second walk (`Term.cseWalk`) -/

mutual
theorem Val.numCalls_cseWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → v.cseWalk.numCalls ≤ v.numCalls
  | _, _, _, _, _, .lam b => by
      simp only [Val.cseWalk, Val.numCalls]; exact Body.numCalls_cseWalk b
  | _, _, _, _, _, .thunk_mk b => by
      simp only [Val.cseWalk, Val.numCalls]; exact Body.numCalls_cseWalk b
  | _, _, _, _, _, .lazy_mk b => by
      simp only [Val.cseWalk, Val.numCalls]; exact Body.numCalls_cseWalk b
  | _, _, _, _, _, .record_mk _ => Nat.le_refl _
  | _, _, _, _, _, .union_mk _ _ => Nat.le_refl _
  | _, _, _, _, _, .array_mk _ => Nat.le_refl _
  | _, _, _, _, _, .list_mk _ => Nat.le_refl _
  | _, _, _, _, _, .data_in _ _ _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
theorem Body.numCalls_cseWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → b.cseWalk.numCalls ≤ b.numCalls
  | _, _, _, _, _, _, .closed t => by
      simp only [Body.cseWalk, Body.numCalls]; exact Term.numCalls_cseWalk t
  | _, _, _, _, _, _, .opened t _ => by
      simp only [Body.cseWalk, Body.numCalls]; exact Term.numCalls_cseWalk t
  termination_by structural _ _ _ _ _ _ x => x
theorem Comp.numCalls_cseWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → c.cseWalk.numCalls ≤ c.numCalls
  | _, _, _, _, _, .app _ _ _ => Nat.le_refl _
  | _, _, _, _, _, .share _ => Nat.le_refl _
  | _, _, _, _, _, .nat_rec n z s _ => by
      simp only [Comp.cseWalk, Comp.numCalls]; exact Body.numCalls_cseWalk s
  | _, _, _, _, _, .array_foldl a z s _ => by
      simp only [Comp.cseWalk, Comp.numCalls]; exact Body.numCalls_cseWalk s
  | _, _, _, _, _, .data_rec b ρt us brs j e _ => by
      simp only [Comp.cseWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_cseWalk (brs i))
  | _, _, _, _, _, .data_brec b ρt k us brs j e _ => by
      simp only [Comp.cseWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_cseWalk (brs i))
  | _, _, _, _, _, .thunk_force _ => Nat.le_refl _
  | _, _, _, _, _, .lazy_force _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
/-- **The second walk of the optimiser does not add calls.** -/
theorem Term.numCalls_cseWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → t.cseWalk.numCalls ≤ t.numCalls
  | _, _, _, _, _, _, .ret _ => Nat.le_refl _
  | _, _, _, _, _, _, .letV u v b => by
      have hv := Val.numCalls_cseWalk v
      have hb := Term.numCalls_cseWalk b
      simp only [Term.cseWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .letE u c b => by
      have hc := Comp.numCalls_cseWalk c
      have hb := Term.numCalls_cseWalk b
      have := Term.numCalls_cseLetE u c.cseWalk b.cseWalk
      simp only [Term.cseWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .record_casesOn us n b => by
      have hb := Term.numCalls_cseWalk b
      simp only [Term.cseWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .branch br => by
      have hb := Branch.numCalls_cseWalk br
      have := Term.numCalls_mkBranch br.cseWalk
      simp only [Term.cseWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .jump _ _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ _ x => x
theorem Branch.numCalls_cseWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) →
    br.cseWalk.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, .ite c t e => by
      have ht := Term.numCalls_cseWalk t
      have he := Term.numCalls_cseWalk e
      simp only [Branch.cseWalk, Branch.numCalls]; omega
  | _, _, _, _, _, _, .enum_casesOn e bs => by
      simp only [Branch.cseWalk, Branch.numCalls]
      exact Fin.sumNat_le _ (fun i => Term.numCalls_cseWalk (bs i))
  | _, _, _, _, _, _, .union_casesOn e bs => by
      simp only [Branch.cseWalk, Branch.numCalls]; exact Branches.numCalls_cseWalk bs
  | _, _, _, _, _, _, .join σ u uₓ body main => by
      have hb := Term.numCalls_cseWalk body
      have hm := Branch.numCalls_cseWalk main
      have := Branch.numCalls_mkJoin σ u uₓ body.cseWalk main.cseWalk
      simp only [Branch.cseWalk, Branch.numCalls]; omega
  termination_by structural _ _ _ _ _ _ x => x
theorem Branches.numCalls_cseWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → br.cseWalk.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ => by
      have h₁ := Term.numCalls_cseWalk b₁
      have h₂ := Term.numCalls_cseWalk b₂
      simp only [Branches.cseWalk, Branches.numCalls]; omega
  | _, _, _, _, _, _, _, _, .cons us b bs => by
      have h₁ := Term.numCalls_cseWalk b
      have h₂ := Branches.numCalls_cseWalk bs
      simp only [Branches.cseWalk, Branches.numCalls]; omega
  termination_by structural _ _ _ _ _ _ _ _ x => x
end

/-! ## The optimiser -/

/-- **The optimiser never adds calls**: the optimised statement has at most as many calls
    `f a`, `t.get`, `t ()` as the original. -/
theorem Term.numCalls_optimize {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} {o : Lvl} (t : Term Δ d Φ Γ τ js o) :
    t.optimize.numCalls ≤ t.numCalls := by
  have h0 := Term.numCalls_inlineKnown t
  have h1 := Term.numCalls_simp t.inlineKnown
  have h2 := Term.numCalls_widenFields t.inlineKnown.simp
  have h3 := Term.numCalls_reuseFields t.inlineKnown.simp.widenFields []
  have h3k := Term.numCalls_knownTests (t.inlineKnown.simp.widenFields.reuseFields [])
  have h3s := Term.numCalls_knownSizes (t.inlineKnown.simp.widenFields.reuseFields []).knownTests
  have h3' := Term.numCalls_shareTestWalk (t.inlineKnown.simp.widenFields.reuseFields []).knownTests.knownSizes
  have h3'' := Term.numCalls_zipTestWalk (t.inlineKnown.simp.widenFields.reuseFields []).knownTests.knownSizes.shareTestWalk
  have h3d := Term.numCalls_dce (t.inlineKnown.simp.widenFields.reuseFields []).knownTests.knownSizes.shareTestWalk.zipTestWalk
  have h4 := Term.numCalls_cseWalk (t.inlineKnown.simp.widenFields.reuseFields []).knownTests.knownSizes.shareTestWalk.zipTestWalk.dce
  have h4' := Term.numCalls_hoistWalk (t.inlineKnown.simp.widenFields.reuseFields []).knownTests.knownSizes.shareTestWalk.zipTestWalk.dce.cseWalk
  have h5 := Term.numCalls_condWalk
    (t.inlineKnown.simp.widenFields.reuseFields []).knownTests.knownSizes.shareTestWalk.zipTestWalk.dce.cseWalk.hoistWalk
  have h5m := Term.numCalls_mergeTestWalk
    (t.inlineKnown.simp.widenFields.reuseFields []).knownTests.knownSizes.shareTestWalk.zipTestWalk.dce.cseWalk.hoistWalk.condWalk
  have h5k := Term.numCalls_knownLits
    (t.inlineKnown.simp.widenFields.reuseFields []).knownTests.knownSizes.shareTestWalk.zipTestWalk.dce.cseWalk.hoistWalk.condWalk.mergeTestWalk
  have h5' := Term.numCalls_appendWalk
    (t.inlineKnown.simp.widenFields.reuseFields []).knownTests.knownSizes.shareTestWalk.zipTestWalk.dce.cseWalk.hoistWalk.condWalk.mergeTestWalk.knownLits
  have h5c := Term.numCalls_condJump
    (t.inlineKnown.simp.widenFields.reuseFields []).knownTests.knownSizes.shareTestWalk.zipTestWalk.dce.cseWalk.hoistWalk.condWalk.mergeTestWalk.knownLits.appendWalk
  have h5j := Term.numCalls_joinCtor
    (t.inlineKnown.simp.widenFields.reuseFields []).knownTests.knownSizes.shareTestWalk.zipTestWalk.dce.cseWalk.hoistWalk.condWalk.mergeTestWalk.knownLits.appendWalk.condJump
  have h5c' := Term.numCalls_condJump
    (t.inlineKnown.simp.widenFields.reuseFields []).knownTests.knownSizes.shareTestWalk.zipTestWalk.dce.cseWalk.hoistWalk.condWalk.mergeTestWalk.knownLits.appendWalk.condJump.joinCtor
  have h5y := Term.numCalls_loopYield
    (t.inlineKnown.simp.widenFields.reuseFields []).knownTests.knownSizes.shareTestWalk.zipTestWalk.dce.cseWalk.hoistWalk.condWalk.mergeTestWalk.knownLits.appendWalk.condJump.joinCtor.condJump
  have h5o := Term.numCalls_openCall
    (t.inlineKnown.simp.widenFields.reuseFields []).knownTests.knownSizes.shareTestWalk.zipTestWalk.dce.cseWalk.hoistWalk.condWalk.mergeTestWalk.knownLits.appendWalk.condJump.joinCtor.condJump.loopYield
  have h5d := Term.numCalls_delayEta
    (t.inlineKnown.simp.widenFields.reuseFields []).knownTests.knownSizes.shareTestWalk.zipTestWalk.dce.cseWalk.hoistWalk.condWalk.mergeTestWalk.knownLits.appendWalk.condJump.joinCtor.condJump.loopYield.openCall
  have h6 := Term.numCalls_inlineRet
    (t.inlineKnown.simp.widenFields.reuseFields []).knownTests.knownSizes.shareTestWalk.zipTestWalk.dce.cseWalk.hoistWalk.condWalk.mergeTestWalk.knownLits.appendWalk.condJump.joinCtor.condJump.loopYield.openCall.delayEta
  have h6' := Term.numCalls_arithWalk
    (t.inlineKnown.simp.widenFields.reuseFields []).knownTests.knownSizes.shareTestWalk.zipTestWalk.dce.cseWalk.hoistWalk.condWalk.mergeTestWalk.knownLits.appendWalk.condJump.joinCtor.condJump.loopYield.openCall.delayEta.inlineRet
  have h6f := Term.numCalls_factorWalk
    (t.inlineKnown.simp.widenFields.reuseFields []).knownTests.knownSizes.shareTestWalk.zipTestWalk.dce.cseWalk.hoistWalk.condWalk.mergeTestWalk.knownLits.appendWalk.condJump.joinCtor.condJump.loopYield.openCall.delayEta.inlineRet.arithWalk
  have h7 := Term.numCalls_dce
    (t.inlineKnown.simp.widenFields.reuseFields []).knownTests.knownSizes.shareTestWalk.zipTestWalk.dce.cseWalk.hoistWalk.condWalk.mergeTestWalk.knownLits.appendWalk.condJump.joinCtor.condJump.loopYield.openCall.delayEta.inlineRet.arithWalk.factorWalk
  have h8 := Term.numCalls_sinkWalk
    (t.inlineKnown.simp.widenFields.reuseFields []).knownTests.knownSizes.shareTestWalk.zipTestWalk.dce.cseWalk.hoistWalk.condWalk.mergeTestWalk.knownLits.appendWalk.condJump.joinCtor.condJump.loopYield.openCall.delayEta.inlineRet.arithWalk.factorWalk.dce
  simp only [Term.optimize]; omega

/-- Running the optimiser any number of times never adds calls either. -/
theorem Term.numCalls_optimizeN {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} {o : Lvl} : (k : Nat) → (t : Term Δ d Φ Γ τ js o) →
    (t.optimizeN k).numCalls ≤ t.numCalls
  | 0, _ => Nat.le_refl _
  | k + 1, t => by
      have := Term.numCalls_optimizeN k t.optimize
      have := Term.numCalls_optimize t
      simp only [Term.optimizeN]; omega

end LeanScript

end
