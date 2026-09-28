module

public import LeanScript.Term.Rewrite.ChurchRosser

@[expose] public section

set_option autoImplicit false

/-!
# The rewrites of the optimiser are rewrite sequences

`Term.simp_star`: the rewriting pass of the optimiser (`Term.simp`, `LeanScript.Term.Optimize.Basic`)
takes a statement to one it rewrites to by `Term.Step`: each rewrite it does (copy propagation,
a shared answer, a dead case analysis) is a step.  With the Church–Rosser property, whatever
other rewrites are done to a statement, the result and `t.simp` still rewrite to a common
statement (`Term.simp_joinable`).
-/

namespace LeanScript

open Rewriting

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Rewriting the members of a family one at a time -/

theorem Fin.FamStep.star {n : Nat} {β : Fin n → Sort _} {R : ∀ i, β i → β i → Prop}
    {f g : (i : Fin n) → β i} (h : ∀ i, Star (R i) (f i) (g i)) : Star (Fin.FamStep R) f g := by
  have key : ∀ k, k ≤ n → ∀ f' : (i : Fin n) → β i, (∀ i, Star (R i) (f' i) (g i)) →
      (∀ i : Fin n, k ≤ i.val → f' i = g i) → Star (Fin.FamStep R) f' g := by
    intro k
    induction k with
    | zero =>
        intro _ f' _ hf'
        have : f' = g := funext fun i => hf' i (Nat.zero_le _)
        subst this; exact .refl _
    | succ k ih =>
        intro hk f' hs hf'
        let i : Fin n := ⟨k, hk⟩
        have step : Star (Fin.FamStep R) f' (Fin.upd f' i (g i)) := by
          have := Star.map (r := R i) (s := Fin.FamStep R) (fun x => Fin.upd f' i x)
            (fun x y hxy => ⟨i, by simpa [Fin.upd_self] using hxy, fun j hj => by
              rw [Fin.upd_ne _ _ _ hj, Fin.upd_ne _ _ _ hj]⟩) (hs i)
          have e : Fin.upd f' i (f' i) = f' := by
            funext j
            by_cases hj : j = i
            · subst hj; rw [Fin.upd_self]
            · rw [Fin.upd_ne _ _ _ hj]
          rw [e] at this; exact this
        refine step.trans (ih (Nat.le_of_succ_le hk) _ ?_ ?_)
        · intro j
          by_cases hj : j = i
          · subst hj; rw [Fin.upd_self]; exact .refl _
          · rw [Fin.upd_ne _ _ _ hj]; exact hs j
        · intro j hj
          by_cases hji : j = i
          · subst hji; rw [Fin.upd_self]
          · rw [Fin.upd_ne _ _ _ hji]
            apply hf'
            have : j.val ≠ k := fun h' => hji (Fin.ext h')
            omega
  exact key n (Nat.le_refl n) f h (fun i hi => absurd i.isLt (Nat.not_lt.mpr hi))

/-! ## Each rewrite of the optimiser is at most one step -/

theorem Term.shareTail_step {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks}
    {ℓ : Nat} {o' : Lvl} (u : Usage1ω) (n : Neu Δ Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') :
    ReflGen Term.Step (Term.letE u (.share n) b) (Term.shareTail u n b) := by
  unfold Term.shareTail
  split
  · rename_i hl
    split
    · rename_i e
      split
      · rename_i e' he
        split
        · rename_i ho
          exact .inr (Term.Step.share_ret u n hl he ho)
        · exact .inl rfl
      · exact .inl rfl
    · rename_i j e
      split
      · rename_i e' he
        split
        · rename_i ho
          exact .inr (Term.Step.share_jump u n hl j he ho)
        · exact .inl rfl
      · exact .inl rfl
    all_goals exact .inl rfl
  · exact .inl rfl

theorem Term.shareLet_step {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks}
    {ℓ : Nat} {o' : Lvl} (u : Usage1ω) (n : Neu Δ Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') :
    ReflGen Term.Step (Term.letE u (.share n) b) (Term.shareLet u n b) := by
  unfold Term.shareLet
  split
  · split
    · rename_i x hl
      split
      · rename_i b' hb
        split
        · rename_i ho
          exact .inr (Term.Step.copy u x hl hb ho)
        · exact Term.shareTail_step u _ b
      · exact Term.shareTail_step u _ b
    · exact Term.shareTail_step u _ b
  · exact Term.shareTail_step u _ b

theorem Term.mkLetE_step {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks}
    {ℓ : Nat} {o' : Lvl} (u : Usage1ω) (c : Comp Δ d Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') :
    ReflGen Term.Step (Term.letE u c b) (Term.mkLetE u c b) := by
  unfold Term.mkLetE
  split
  · exact Term.shareLet_step u _ b
  · exact .inl rfl

theorem Term.mkRecordCasesOn_step {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks}
    {fs : Fields ks} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat} {o' : Lvl} (us : List Usage01ω)
    (n : Neu Δ Φ Γ (.record t fs) ℓ)
    (b : Term Δ d Φ (UCtx.annot d (t :: fs.toList) us ++ Γ) τ js o') :
    ReflGen Term.Step (Term.record_casesOn us n b) (Term.mkRecordCasesOn us n b) := by
  unfold Term.mkRecordCasesOn
  split
  · rename_i b' hb
    split
    · rename_i ho
      exact .inr (Term.Step.casesOn_drop us n hb ho)
    · exact .inl rfl
  · exact .inl rfl

/-! ## The rewriting pass is a rewrite sequence -/

mutual
theorem Val.simp_star : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    (v : Val Δ d Φ Γ τ o) → Star Val.Step v v.simp
  | _, _, _, _, _, .lam b => (Body.simp_star b).map _ (fun _ _ h => Val.Step.lam h)
  | _, _, _, _, _, .thunk_mk b => (Body.simp_star b).map _ (fun _ _ h => Val.Step.thunk_mk h)
  | _, _, _, _, _, .lazy_mk b => (Body.simp_star b).map _ (fun _ _ h => Val.Step.lazy_mk h)
  | _, _, _, _, _, .record_mk _ => .refl _
  | _, _, _, _, _, .union_mk _ _ => .refl _
  | _, _, _, _, _, .array_mk _ => .refl _
  | _, _, _, _, _, .list_mk _ => .refl _
  | _, _, _, _, _, .data_in _ _ _ => .refl _
theorem Body.simp_star : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → Star Body.Step b b.simp
  | _, _, _, _, _, _, .closed t => (Term.simp_star t).map _ (fun _ _ h => Body.Step.closed h)
  | _, _, _, _, _, _, .opened t hm =>
      (Term.simp_star t).map (fun x => Body.opened x hm) (fun _ _ h => Body.Step.opened hm h)
theorem Comp.simp_star : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    (c : Comp Δ d Φ Γ τ ℓ) → Star Comp.Step c c.simp
  | _, _, _, _, _, .app _ _ _ => .refl _
  | _, _, _, _, _, .share _ => .refl _
  | _, _, _, _, _, .nat_rec n z s h =>
      (Body.simp_star s).map (fun x => Comp.nat_rec n z x h)
        (fun _ _ hs => Comp.Step.nat_rec n z h hs)
  | _, _, _, _, _, .array_foldl a z s h =>
      (Body.simp_star s).map (fun x => Comp.array_foldl a z x h)
        (fun _ _ hs => Comp.Step.array_foldl a z h hs)
  | _, _, _, _, _, .data_rec b ρ us brs j e h =>
      (Fin.FamStep.star (R := fun _ => Body.Step) (fun i => Body.simp_star (brs i))).map
        (fun g => Comp.data_rec b ρ us g j e h)
        (fun _ _ hh => by obtain ⟨i, hi, hne⟩ := hh; exact Comp.Step.data_rec b ρ us j e h i hi hne)
  | _, _, _, _, _, .data_brec b ρ k us brs j e h =>
      (Fin.FamStep.star (R := fun _ => Body.Step) (fun i => Body.simp_star (brs i))).map
        (fun g => Comp.data_brec b ρ k us g j e h)
        (fun _ _ hh => by
          obtain ⟨i, hi, hne⟩ := hh; exact Comp.Step.data_brec b ρ k us j e h i hi hne)
  | _, _, _, _, _, .thunk_force _ => .refl _
  | _, _, _, _, _, .lazy_force _ => .refl _
theorem Term.simp_star : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → Star Term.Step t t.simp
  | _, _, _, _, _, _, .ret _ => .refl _
  | _, _, _, _, _, _, .letV u v b =>
      ((Val.simp_star v).map (fun x => Term.letV u x b) (fun _ _ h => Term.Step.letV_val u b h)).trans
        ((Term.simp_star b).map (fun x => Term.letV u v.simp x)
          (fun _ _ h => Term.Step.letV_body u v.simp h))
  | _, _, _, _, _, _, .letE u c b =>
      (((Comp.simp_star c).map (fun x => Term.letE u x b)
          (fun _ _ h => Term.Step.letE_comp u b h)).trans
        ((Term.simp_star b).map (fun x => Term.letE u c.simp x)
          (fun _ _ h => Term.Step.letE_body u c.simp h))).trans
        (Term.mkLetE_step u c.simp b.simp).star
  | _, _, _, _, _, _, .record_casesOn us n b =>
      ((Term.simp_star b).map (fun x => Term.record_casesOn us n x)
          (fun _ _ h => Term.Step.casesOn_body us n h)).trans
        (Term.mkRecordCasesOn_step us n b.simp).star
  | _, _, _, _, _, _, .branch br =>
      (Branch.simp_star br).map (fun x => Term.branch x) (fun _ _ h => Term.Step.branch h)
  | _, _, _, _, _, _, .jump _ _ => .refl _
theorem Branch.simp_star : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → Star Branch.Step br br.simp
  | _, _, _, _, _, _, .ite c t e =>
      ((Term.simp_star t).map (fun x => Branch.ite c x e)
          (fun _ _ h => Branch.Step.ite_then c e h)).trans
        ((Term.simp_star e).map (fun x => Branch.ite c t.simp x)
          (fun _ _ h => Branch.Step.ite_else c t.simp h))
  | _, _, _, _, _, _, .enum_casesOn e bs =>
      (Fin.FamStep.star (R := fun _ => Term.Step) (fun i => Term.simp_star (bs i))).map
        (fun g => Branch.enum_casesOn e g)
        (fun _ _ hh => by obtain ⟨i, hi, hne⟩ := hh; exact Branch.Step.enum_casesOn e i hi hne)
  | _, _, _, _, _, _, .union_casesOn e bs =>
      (Branches.simp_star bs).map (fun x => Branch.union_casesOn e x)
        (fun _ _ h => Branch.Step.union_casesOn e h)
  | _, _, _, _, _, _, .join σ u uₓ body main =>
      ((Term.simp_star body).map (fun x => Branch.join σ u uₓ x main)
          (fun _ _ h => Branch.Step.join_body σ u uₓ main h)).trans
        ((Branch.simp_star main).map (fun x => Branch.join σ u uₓ body.simp x)
          (fun _ _ h => Branch.Step.join_main σ u uₓ body.simp h))
theorem Branches.simp_star : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → Star Branches.Step br br.simp
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ =>
      ((Term.simp_star b₁).map (fun x => Branches.two us₁ us₂ x b₂)
          (fun _ _ h => Branches.Step.two_left us₁ us₂ b₂ h)).trans
        ((Term.simp_star b₂).map (fun x => Branches.two us₁ us₂ b₁.simp x)
          (fun _ _ h => Branches.Step.two_right us₁ us₂ b₁.simp h))
  | _, _, _, _, _, _, _, _, .cons us b bs =>
      ((Term.simp_star b).map (fun x => Branches.cons us x bs)
          (fun _ _ h => Branches.Step.cons_head us bs h)).trans
        ((Branches.simp_star bs).map (fun x => Branches.cons us b.simp x)
          (fun _ _ h => Branches.Step.cons_tail us b.simp h))
end

/-- Whatever rewrites are done to a statement, the result and the output of the optimiser's
    rewriting pass rewrite to a common statement (with the value of the original). -/
theorem Term.simp_joinable {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {o : Lvl} {t t' : Term Δ d Φ Γ τ js o} (h : Star Term.Step t t') :
    ∃ t₃, Star Term.Step t' t₃ ∧ Star Term.Step t.simp t₃ ∧
      ∀ (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js), t₃.eval κ ρ jκ = t.eval κ ρ jκ :=
  Term.eval_confluent h (Term.simp_star t)

end LeanScript

end
