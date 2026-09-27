module

public import LeanScript.Term.StepInv
public import LeanScript.Term.Rewriting

@[expose] public section

set_option autoImplicit false

/-!
# The Church–Rosser property of the rewrites of normal-form terms

`Term.Step` (`LeanScript.Term.Step`) is the one-step rewriting of normal-form terms by the
rewrites of the optimiser and of dead-code elimination, anywhere in a term.  This file proves:

* `Term.Step.diamond`: two steps out of the same statement can be closed by at most one step
  each (**strong confluence**), and the same for every other layer;
* `Term.Step.confluent`: two rewrite sequences out of the same statement can be continued to a
  common statement (**confluence**);
* `Term.Step.churchRosser`: two statements related by steps taken in either direction rewrite
  to a common statement (**Church–Rosser**);
* `Term.Step.normal_unique`: a statement has at most one normal form;
* `Term.Step.conv_eval`: statements related by steps have the same value under `Term.eval`, in
  every environment, and `Term.Step.star_eval` for rewrite sequences.
-/

namespace LeanScript

open Rewriting

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Helpers -/

theorem Term.Step.castLvl {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {o o' : Lvl} {t t' : Term Δ d Φ Γ τ js o} (h : Term.Step t t') (ho : o = o') :
    Term.Step (t.castLvl ho) (t'.castLvl ho) := by
  subst ho; exact h

theorem Branch.Step.castLvl {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {ℓ ℓ' : Nat} {t t' : Branch Δ d Φ Γ τ js ℓ} (h : Branch.Step t t') (ho : ℓ = ℓ') :
    Branch.Step (t.castLvl ho) (t'.castLvl ho) := by
  subst ho; exact h

/-- The expression recognised by `PExpr.substHead` uses the innermost unknown. -/
theorem PExpr.substHead_drop {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {u : Usage01ω}
    {d ℓ : Nat} {o : Lvl} (n : Neu Δ Φ Γ σ ℓ) (hl : ℓ = d) (e : PExpr Δ Φ (⟨σ, u, d⟩ :: Γ) τ o)
    {e' : PExpr Δ Φ Γ τ o} (he : PExpr.substHead n hl e = some e') :
    e.rename KRen.id URen.drop = none := by
  subst hl
  cases e with
  | neu m =>
      cases m with
      | var x =>
          cases x with
          | head h => simp [PExpr.rename, Neu.rename, URen.drop]
          | tail => simp [PExpr.substHead, Neu.substHead] at he
      | _ => simp [PExpr.substHead, Neu.substHead] at he
  | _ => simp [PExpr.substHead] at he

/-- Copy propagation on the expression recognised by `PExpr.substHead`. -/
theorem PExpr.substHead_var {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {u : Usage01ω}
    {d ℓ : Nat} {o : Lvl} (x : UVar Γ σ ℓ) (hl hl' : ℓ = d) (e : PExpr Δ Φ (⟨σ, u, d⟩ :: Γ) τ o)
    {e' : PExpr Δ Φ Γ τ o} (he : PExpr.substHead (.var x) hl e = some e') :
    e.rename KRen.id (URen.subst x hl') = some e' := by
  subst hl
  cases e with
  | neu m =>
      cases m with
      | var y =>
          cases y with
          | head h =>
              simp only [PExpr.substHead, Neu.substHead, Option.map_some, Option.some.injEq] at he
              subst he
              simp [PExpr.rename, Neu.rename, URen.subst]
          | tail => simp [PExpr.substHead, Neu.substHead] at he
      | _ => simp [PExpr.substHead, Neu.substHead] at he
  | _ => simp [PExpr.substHead] at he

/-- Dropping an unused unknown is copy propagation for it. -/
theorem Term.rename_drop_subst {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks}
    {js : JCtx ks} {u : Usage01ω} {ℓ : Nat} {o : Lvl} {b : Term Δ d Φ (⟨σ, u, d⟩ :: Γ) τ js o}
    {b₁ : Term Δ d Φ Γ τ js o} (x : UVar Γ σ ℓ) (hl : ℓ = d)
    (h : b.rename KRen.id URen.drop JRen.id = some b₁) :
    b.rename KRen.id (URen.subst x hl) JRen.id = some b₁ :=
  Term.rename_mono h (fun _ _ h => h)
    (by intro _ _ y z h; cases y <;> simp_all [URen.drop, URen.subst]) (fun _ _ h => h)

/-- A step that changes one member of a family. -/
def Fin.FamStep {n : Nat} {β : Fin n → Sort _} (R : ∀ i, β i → β i → Prop)
    (f g : (i : Fin n) → β i) : Prop :=
  ∃ i, R i (f i) (g i) ∧ ∀ i', i' ≠ i → g i' = f i'

/-- Replace one member of a family. -/
def Fin.upd {n : Nat} {β : Fin n → Sort _} (f : (i : Fin n) → β i) (i : Fin n) (x : β i) :
    (j : Fin n) → β j :=
  fun j => if h : j = i then h ▸ x else f j

theorem Fin.upd_self {n : Nat} {β : Fin n → Sort _} (f : (i : Fin n) → β i) (i : Fin n)
    (x : β i) : Fin.upd f i x i = x := by
  simp [Fin.upd]

theorem Fin.upd_ne {n : Nat} {β : Fin n → Sort _} (f : (i : Fin n) → β i) (i : Fin n)
    (x : β i) {j : Fin n} (h : j ≠ i) : Fin.upd f i x j = f j := by
  simp [Fin.upd, h]

/-- Two steps in a family close in at most one step each, given that two steps in the same
    member do. -/
theorem Fin.FamStep.diamond {n : Nat} {β : Fin n → Sort _} {R : ∀ i, β i → β i → Prop}
    {f g₁ g₂ : (i : Fin n) → β i} {i₁ i₂ : Fin n} (h₁ : R i₁ (f i₁) (g₁ i₁))
    (e₁ : ∀ i', i' ≠ i₁ → g₁ i' = f i') (h₂ : R i₂ (f i₂) (g₂ i₂))
    (e₂ : ∀ i', i' ≠ i₂ → g₂ i' = f i')
    (ih : (hi : i₁ = i₂) → ∃ x, ReflGen (R i₁) (g₁ i₁) x ∧ ReflGen (R i₁) (g₂ i₁) x) :
    ∃ g₃, ReflGen (Fin.FamStep R) g₁ g₃ ∧ ReflGen (Fin.FamStep R) g₂ g₃ := by
  by_cases hi : i₁ = i₂
  · obtain ⟨x, hx₁, hx₂⟩ := ih hi
    subst hi
    have side : ∀ (g : (i : Fin n) → β i), (∀ i', i' ≠ i₁ → g i' = f i') →
        ReflGen (R i₁) (g i₁) x → ReflGen (Fin.FamStep R) g (Fin.upd f i₁ x) := by
      intro g eg hx
      rcases hx with hx | hx
      · left
        funext j
        by_cases hj : j = i₁
        · subst hj; rw [Fin.upd_self, hx]
        · rw [Fin.upd_ne _ _ _ hj, eg j hj]
      · right
        refine ⟨i₁, ?_, ?_⟩
        · rw [Fin.upd_self]; exact hx
        · intro j hj; rw [Fin.upd_ne _ _ _ hj, eg j hj]
    exact ⟨_, side g₁ e₁ hx₁, side g₂ e₂ hx₂⟩
  · refine ⟨fun j => if j = i₁ then g₁ j else g₂ j, .inr ⟨i₂, ?_, ?_⟩, .inr ⟨i₁, ?_, ?_⟩⟩
    · have hne : i₂ ≠ i₁ := fun h => hi h.symm
      simp only [hne, ite_false]
      rw [e₁ i₂ hne]; exact h₂
    · intro j hj
      by_cases hj' : j = i₁
      · subst hj'; simp
      · simp only [hj', ite_false]; rw [e₂ j hj, e₁ j hj']
    · simp only [eq_self, ite_true]
      rw [e₂ i₁ hi]; exact h₁
    · intro j hj; simp [hj]

/-! ## Strong confluence -/

mutual
theorem Val.Step.diamond : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → {v v₁ : Val Δ d Φ Γ τ o} → Val.Step v v₁ → ∀ {v₂}, Val.Step v v₂ →
    ∃ v₃, ReflGen Val.Step v₁ v₃ ∧ ReflGen Val.Step v₂ v₃
  | _, _, _, _, _, _, _, .lam hs => by
      intro h₂
      obtain ⟨b₂, hs₂, rfl⟩ := h₂.inv
      obtain ⟨b₃, h1, h2⟩ := Body.Step.diamond hs hs₂
      exact ⟨_, h1.map (fun x => Val.lam x) (fun _ _ h => Val.Step.lam h), h2.map (fun x => Val.lam x) (fun _ _ h => Val.Step.lam h)⟩
  | _, _, _, _, _, _, _, .thunk_mk hs => by
      intro h₂
      obtain ⟨b₂, hs₂, rfl⟩ := h₂.inv
      obtain ⟨b₃, h1, h2⟩ := Body.Step.diamond hs hs₂
      exact ⟨_, h1.map (fun x => Val.thunk_mk x) (fun _ _ h => Val.Step.thunk_mk h), h2.map (fun x => Val.thunk_mk x) (fun _ _ h => Val.Step.thunk_mk h)⟩
  | _, _, _, _, _, _, _, .lazy_mk hs => by
      intro h₂
      obtain ⟨b₂, hs₂, rfl⟩ := h₂.inv
      obtain ⟨b₃, h1, h2⟩ := Body.Step.diamond hs hs₂
      exact ⟨_, h1.map (fun x => Val.lazy_mk x) (fun _ _ h => Val.Step.lazy_mk h), h2.map (fun x => Val.lazy_mk x) (fun _ _ h => Val.Step.lazy_mk h)⟩
  termination_by structural _ _ _ _ _ _ _ x => x
theorem Body.Step.diamond : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → {b b₁ : Body Δ d Φ Γ bs τ o} → Body.Step b b₁ → ∀ {b₂}, Body.Step b b₂ →
    ∃ b₃, ReflGen Body.Step b₁ b₃ ∧ ReflGen Body.Step b₂ b₃
  | _, _, _, _, _, _, _, _, .closed hs => by
      intro h₂
      obtain ⟨t₂, hs₂, rfl⟩ := h₂.inv
      obtain ⟨t₃, h1, h2⟩ := Term.Step.diamond hs hs₂
      exact ⟨_, h1.map (fun x => Body.closed x) (fun _ _ h => Body.Step.closed h), h2.map (fun x => Body.closed x) (fun _ _ h => Body.Step.closed h)⟩
  | _, _, _, _, _, _, _, _, .opened hm hs => by
      intro h₂
      obtain ⟨t₂, hs₂, rfl⟩ := h₂.inv
      obtain ⟨t₃, h1, h2⟩ := Term.Step.diamond hs hs₂
      exact ⟨_, h1.map (fun x => Body.opened x hm) (fun _ _ h => Body.Step.opened hm h), h2.map (fun x => Body.opened x hm) (fun _ _ h => Body.Step.opened hm h)⟩
  termination_by structural _ _ _ _ _ _ _ _ x => x
theorem Comp.Step.diamond : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → {c c₁ : Comp Δ d Φ Γ τ ℓ} → Comp.Step c c₁ → ∀ {c₂}, Comp.Step c c₂ →
    ∃ c₃, ReflGen Comp.Step c₁ c₃ ∧ ReflGen Comp.Step c₂ c₃
  | _, _, _, _, _, _, _, .nat_rec n z hℓ hs => by
      intro h₂
      obtain ⟨s₂, hs₂, rfl⟩ := h₂.inv
      obtain ⟨s₃, h1, h2⟩ := Body.Step.diamond hs hs₂
      exact ⟨_, h1.map (fun x => Comp.nat_rec n z x hℓ) (fun _ _ h => Comp.Step.nat_rec n z hℓ h),
        h2.map (fun x => Comp.nat_rec n z x hℓ) (fun _ _ h => Comp.Step.nat_rec n z hℓ h)⟩
  | _, _, _, _, _, _, _, .array_foldl a z hℓ hs => by
      intro h₂
      obtain ⟨s₂, hs₂, rfl⟩ := h₂.inv
      obtain ⟨s₃, h1, h2⟩ := Body.Step.diamond hs hs₂
      exact ⟨_, h1.map (fun x => Comp.array_foldl a z x hℓ) (fun _ _ h => Comp.Step.array_foldl a z hℓ h),
        h2.map (fun x => Comp.array_foldl a z x hℓ) (fun _ _ h => Comp.Step.array_foldl a z hℓ h)⟩
  | _, _, _, _, _, _, _, .data_rec b ρt us j e hℓ i hs hbs => by
      intro h₂
      obtain ⟨brs₂, i₂, hs₂, hbs₂, rfl⟩ := h₂.inv
      have ih : (hi : i = i₂) → _ := fun hi => by
        subst hi; exact Body.Step.diamond hs hs₂
      obtain ⟨g₃, h1, h2⟩ := Fin.FamStep.diamond (R := fun _ => Body.Step) hs hbs hs₂ hbs₂ ih
      exact ⟨_, ReflGen.map (fun g => Comp.data_rec b ρt us g j e hℓ)
          (fun _ _ hh => by obtain ⟨i, h, hne⟩ := hh; exact Comp.Step.data_rec b ρt us j e hℓ i h hne) h1,
        ReflGen.map (fun g => Comp.data_rec b ρt us g j e hℓ)
          (fun _ _ hh => by obtain ⟨i, h, hne⟩ := hh; exact Comp.Step.data_rec b ρt us j e hℓ i h hne) h2⟩
  | _, _, _, _, _, _, _, .data_brec b ρt k us j e hℓ i hs hbs => by
      intro h₂
      obtain ⟨brs₂, i₂, hs₂, hbs₂, rfl⟩ := h₂.inv
      have ih : (hi : i = i₂) → _ := fun hi => by
        subst hi; exact Body.Step.diamond hs hs₂
      obtain ⟨g₃, h1, h2⟩ := Fin.FamStep.diamond (R := fun _ => Body.Step) hs hbs hs₂ hbs₂ ih
      exact ⟨_, ReflGen.map (fun g => Comp.data_brec b ρt k us g j e hℓ)
          (fun _ _ hh => by obtain ⟨i, h, hne⟩ := hh; exact Comp.Step.data_brec b ρt k us j e hℓ i h hne) h1,
        ReflGen.map (fun g => Comp.data_brec b ρt k us g j e hℓ)
          (fun _ _ hh => by obtain ⟨i, h, hne⟩ := hh; exact Comp.Step.data_brec b ρt k us j e hℓ i h hne) h2⟩
  termination_by structural _ _ _ _ _ _ _ x => x
theorem Term.Step.diamond : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → {t t₁ : Term Δ d Φ Γ τ js o} → Term.Step t t₁ →
    ∀ {t₂}, Term.Step t t₂ → ∃ t₃, ReflGen Term.Step t₁ t₃ ∧ ReflGen Term.Step t₂ t₃
  | _, _, _, _, _, _, _, _, .letV_drop u v hb ho => by
      intro h₂
      have h := h₂.inv
      simp only [Term.StepInv] at h
      rcases h with ⟨b₂, hb₂, ho₂, rfl⟩ | ⟨v', hv, rfl⟩ | ⟨b₂, hs, rfl⟩
      · rw [hb] at hb₂; cases hb₂
        exact ⟨_, .inl rfl, .inl rfl⟩
      · exact ⟨_, .inl rfl, .inr (.letV_drop u v' hb ho)⟩
      · obtain ⟨b₂', hb₂', hs'⟩ := hs.rename KRen.drop URen.id JRen.id hb
        exact ⟨_, .inr (hs'.castLvl ho), .inr (.letV_drop u v hb₂' ho)⟩
  | _, _, _, _, _, _, _, _, .letV_val u b hs => by
      intro h₂
      have h := h₂.inv
      simp only [Term.StepInv] at h
      rcases h with ⟨b₂, hb₂, ho₂, rfl⟩ | ⟨v', hv, rfl⟩ | ⟨b₂, hs₂, rfl⟩
      · exact ⟨_, .inr (.letV_drop u _ hb₂ ho₂), .inl rfl⟩
      · obtain ⟨v₃, h1, h2⟩ := Val.Step.diamond hs hv
        exact ⟨_, h1.map (fun x => Term.letV u x b) (fun _ _ h => Term.Step.letV_val u b h), h2.map (fun x => Term.letV u x b) (fun _ _ h => Term.Step.letV_val u b h)⟩
      · exact ⟨_, .inr (.letV_body u _ hs₂), .inr (.letV_val u _ hs)⟩
  | _, _, _, _, _, _, _, _, .letV_body u v hs => by
      intro h₂
      have h := h₂.inv
      simp only [Term.StepInv] at h
      rcases h with ⟨b₂, hb₂, ho₂, rfl⟩ | ⟨v', hv, rfl⟩ | ⟨b₂, hs₂, rfl⟩
      · obtain ⟨b₁', hb₁', hs'⟩ := hs.rename KRen.drop URen.id JRen.id hb₂
        exact ⟨_, .inr (.letV_drop u v hb₁' ho₂), .inr (hs'.castLvl ho₂)⟩
      · exact ⟨_, .inr (.letV_val u _ hv), .inr (.letV_body u _ hs)⟩
      · obtain ⟨b₃, h1, h2⟩ := Term.Step.diamond hs hs₂
        exact ⟨_, h1.map (fun x => Term.letV u v x) (fun _ _ h => Term.Step.letV_body u v h), h2.map (fun x => Term.letV u v x) (fun _ _ h => Term.Step.letV_body u v h)⟩
  | _, _, _, _, _, _, _, _, .letE_drop u c hb ho => by
      intro h₂
      have h := h₂.inv
      simp only [Term.StepInv] at h
      rcases h with ⟨b₂, hb₂, ho₂, rfl⟩ | ⟨x, hl, rfl, b₂, hb₂, ho₂, rfl⟩ |
        ⟨n, hl, e, rfl, rfl, e', he, ho₂, rfl⟩ | ⟨n, hl, σ', j, e, rfl, rfl, e', he, ho₂, rfl⟩ |
        ⟨c', hc, rfl⟩ | ⟨b₂, hs, rfl⟩
      · rw [hb] at hb₂; cases hb₂
        exact ⟨_, .inl rfl, .inl rfl⟩
      · rw [Term.rename_drop_subst x hl hb] at hb₂; cases hb₂
        exact ⟨_, .inl rfl, .inl rfl⟩
      · simp [Term.rename, PExpr.substHead_drop n hl e he] at hb
      · simp [Term.rename, PExpr.substHead_drop n hl e he] at hb
      · exact ⟨_, .inl rfl, .inr (.letE_drop u c' hb ho)⟩
      · obtain ⟨b₂', hb₂', hs'⟩ := hs.rename KRen.id URen.drop JRen.id hb
        exact ⟨_, .inr (hs'.castLvl ho), .inr (.letE_drop u c hb₂' ho)⟩
  | _, _, _, _, _, _, _, _, .copy u x hl hb ho => by
      intro h₂
      have h := h₂.inv
      simp only [Term.StepInv] at h
      rcases h with ⟨b₂, hb₂, ho₂, rfl⟩ | ⟨x₂, hl₂, hc, b₂, hb₂, ho₂, rfl⟩ |
        ⟨n, hl₂, e, hc, rfl, e', he, ho₂, rfl⟩ | ⟨n, hl₂, σ', j, e, hc, rfl, e', he, ho₂, rfl⟩ |
        ⟨c', hc, rfl⟩ | ⟨b₂, hs, rfl⟩
      · rw [Term.rename_drop_subst x hl hb₂] at hb; cases hb
        exact ⟨_, .inl rfl, .inl rfl⟩
      · cases hc
        rw [hb] at hb₂; cases hb₂
        exact ⟨_, .inl rfl, .inl rfl⟩
      · cases hc
        have := PExpr.substHead_var x hl₂ hl e he
        simp only [Term.rename, this, Option.map_some, Option.some.injEq] at hb
        subst hb
        exact ⟨_, .inl rfl, .inl rfl⟩
      · cases hc
        have := PExpr.substHead_var x hl₂ hl e he
        simp only [Term.rename, this, JRen.id, Option.bind_eq_bind, Option.bind_some,
          Option.pure_def, Option.some.injEq] at hb
        subst hb
        exact ⟨_, .inl rfl, .inl rfl⟩
      · exact absurd hc.inv (by simp [Comp.StepInv])
      · obtain ⟨b₂', hb₂', hs'⟩ := hs.rename KRen.id (URen.subst x hl) JRen.id hb
        exact ⟨_, .inr (hs'.castLvl ho), .inr (.copy u x hl hb₂' ho)⟩
  | _, _, _, _, _, _, _, _, .share_ret u n hl he ho => by
      intro h₂
      have h := h₂.inv
      simp only [Term.StepInv] at h
      rcases h with ⟨b₂, hb₂, ho₂, rfl⟩ | ⟨x₂, hl₂, hc, b₂, hb₂, ho₂, rfl⟩ |
        ⟨n₂, hl₂, e₂, hc, hb, e₂', he₂, ho₂, rfl⟩ | ⟨n₂, hl₂, σ', j, e₂, hc, hb, e₂', he₂, ho₂, rfl⟩ |
        ⟨c', hc, rfl⟩ | ⟨b₂, hs, rfl⟩
      · simp [Term.rename, PExpr.substHead_drop n hl _ he] at hb₂
      · cases hc
        have := PExpr.substHead_var x₂ hl hl₂ _ he
        simp only [Term.rename, this, Option.map_some, Option.some.injEq] at hb₂
        subst hb₂
        exact ⟨_, .inl rfl, .inl rfl⟩
      · cases hc; cases hb
        rw [he] at he₂; cases he₂
        exact ⟨_, .inl rfl, .inl rfl⟩
      · cases hb
      · exact absurd hc.inv (by simp [Comp.StepInv])
      · exact absurd hs.inv (by simp [Term.StepInv])
  | _, _, _, _, _, _, _, _, .share_jump u n hl j he ho => by
      intro h₂
      have h := h₂.inv
      simp only [Term.StepInv] at h
      rcases h with ⟨b₂, hb₂, ho₂, rfl⟩ | ⟨x₂, hl₂, hc, b₂, hb₂, ho₂, rfl⟩ |
        ⟨n₂, hl₂, e₂, hc, hb, e₂', he₂, ho₂, rfl⟩ | ⟨n₂, hl₂, σ', j₂, e₂, hc, hb, e₂', he₂, ho₂, rfl⟩ |
        ⟨c', hc, rfl⟩ | ⟨b₂, hs, rfl⟩
      · simp [Term.rename, PExpr.substHead_drop n hl _ he] at hb₂
      · cases hc
        have := PExpr.substHead_var x₂ hl hl₂ _ he
        simp only [Term.rename, this, JRen.id, Option.bind_eq_bind, Option.bind_some,
          Option.pure_def, Option.some.injEq] at hb₂
        subst hb₂
        exact ⟨_, .inl rfl, .inl rfl⟩
      · cases hb
      · cases hc; cases hb
        rw [he] at he₂; cases he₂
        exact ⟨_, .inl rfl, .inl rfl⟩
      · exact absurd hc.inv (by simp [Comp.StepInv])
      · exact absurd hs.inv (by simp [Term.StepInv])
  | _, _, _, _, _, _, _, _, .letE_comp u b hs => by
      intro h₂
      have h := h₂.inv
      simp only [Term.StepInv] at h
      rcases h with ⟨b₂, hb₂, ho₂, rfl⟩ | ⟨x, hl, rfl, b₂, hb₂, ho₂, rfl⟩ |
        ⟨n, hl, e, rfl, rfl, e', he, ho₂, rfl⟩ | ⟨n, hl, σ', j, e, rfl, rfl, e', he, ho₂, rfl⟩ |
        ⟨c', hc, rfl⟩ | ⟨b₂, hs₂, rfl⟩
      · exact ⟨_, .inr (.letE_drop u _ hb₂ ho₂), .inl rfl⟩
      · exact absurd hs.inv (by simp [Comp.StepInv])
      · exact absurd hs.inv (by simp [Comp.StepInv])
      · exact absurd hs.inv (by simp [Comp.StepInv])
      · obtain ⟨c₃, h1, h2⟩ := Comp.Step.diamond hs hc
        exact ⟨_, h1.map (fun x => Term.letE u x b) (fun _ _ h => Term.Step.letE_comp u b h), h2.map (fun x => Term.letE u x b) (fun _ _ h => Term.Step.letE_comp u b h)⟩
      · exact ⟨_, .inr (.letE_body u _ hs₂), .inr (.letE_comp u _ hs)⟩
  | _, _, _, _, _, _, _, _, .letE_body u c hs => by
      intro h₂
      have h := h₂.inv
      simp only [Term.StepInv] at h
      rcases h with ⟨b₂, hb₂, ho₂, rfl⟩ | ⟨x, hl, rfl, b₂, hb₂, ho₂, rfl⟩ |
        ⟨n, hl, e, rfl, rfl, e', he, ho₂, rfl⟩ | ⟨n, hl, σ', j, e, rfl, rfl, e', he, ho₂, rfl⟩ |
        ⟨c', hc, rfl⟩ | ⟨b₂, hs₂, rfl⟩
      · obtain ⟨b₁', hb₁', hs'⟩ := hs.rename KRen.id URen.drop JRen.id hb₂
        exact ⟨_, .inr (.letE_drop u c hb₁' ho₂), .inr (hs'.castLvl ho₂)⟩
      · obtain ⟨b₁', hb₁', hs'⟩ := hs.rename KRen.id (URen.subst x hl) JRen.id hb₂
        exact ⟨_, .inr (.copy u x hl hb₁' ho₂), .inr (hs'.castLvl ho₂)⟩
      · exact absurd hs.inv (by simp [Term.StepInv])
      · exact absurd hs.inv (by simp [Term.StepInv])
      · exact ⟨_, .inr (.letE_comp u _ hc), .inr (.letE_body u _ hs)⟩
      · obtain ⟨b₃, h1, h2⟩ := Term.Step.diamond hs hs₂
        exact ⟨_, h1.map (fun x => Term.letE u c x) (fun _ _ h => Term.Step.letE_body u c h), h2.map (fun x => Term.letE u c x) (fun _ _ h => Term.Step.letE_body u c h)⟩
  | _, _, _, _, _, _, _, _, .casesOn_drop us n hb ho => by
      intro h₂
      have h := h₂.inv
      simp only [Term.StepInv] at h
      rcases h with ⟨b₂, hb₂, ho₂, rfl⟩ | ⟨b₂, hs, rfl⟩
      · rw [hb] at hb₂; cases hb₂
        exact ⟨_, .inl rfl, .inl rfl⟩
      · obtain ⟨b₂', hb₂', hs'⟩ := hs.rename KRen.id (URen.dropN _) JRen.id hb
        exact ⟨_, .inr (hs'.castLvl ho), .inr (.casesOn_drop us n hb₂' ho)⟩
  | _, _, _, _, _, _, _, _, .casesOn_body us n hs => by
      intro h₂
      have h := h₂.inv
      simp only [Term.StepInv] at h
      rcases h with ⟨b₂, hb₂, ho₂, rfl⟩ | ⟨b₂, hs₂, rfl⟩
      · obtain ⟨b₁', hb₁', hs'⟩ := hs.rename KRen.id (URen.dropN _) JRen.id hb₂
        exact ⟨_, .inr (.casesOn_drop us n hb₁' ho₂), .inr (hs'.castLvl ho₂)⟩
      · obtain ⟨b₃, h1, h2⟩ := Term.Step.diamond hs hs₂
        exact ⟨_, h1.map (fun x => Term.record_casesOn us n x) (fun _ _ h => Term.Step.casesOn_body us n h),
          h2.map (fun x => Term.record_casesOn us n x) (fun _ _ h => Term.Step.casesOn_body us n h)⟩
  | _, _, _, _, _, _, _, _, .branch hs => by
      intro h₂
      have h := h₂.inv
      simp only [Term.StepInv] at h
      obtain ⟨br₂, hs₂, rfl⟩ := h
      obtain ⟨br₃, h1, h2⟩ := Branch.Step.diamond hs hs₂
      exact ⟨_, h1.map (fun x => Term.branch x) (fun _ _ h => Term.Step.branch h), h2.map (fun x => Term.branch x) (fun _ _ h => Term.Step.branch h)⟩
  termination_by structural _ _ _ _ _ _ _ _ x => x
theorem Branch.Step.diamond : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → {t t₁ : Branch Δ d Φ Γ τ js ℓ} → Branch.Step t t₁ →
    ∀ {t₂}, Branch.Step t t₂ → ∃ t₃, ReflGen Branch.Step t₁ t₃ ∧ ReflGen Branch.Step t₂ t₃
  | _, _, _, _, _, _, _, _, .join_drop σ u uₓ body hm ho => by
      intro h₂
      have h := h₂.inv
      simp only [Branch.StepInv] at h
      rcases h with ⟨m₂, hm₂, ho₂, rfl⟩ | ⟨body', hs, rfl⟩ | ⟨m₂, hs, rfl⟩
      · rw [hm] at hm₂; cases hm₂
        exact ⟨_, .inl rfl, .inl rfl⟩
      · exact ⟨_, .inl rfl, .inr (.join_drop σ u uₓ body' hm ho)⟩
      · obtain ⟨m₂', hm₂', hs'⟩ := hs.rename KRen.id URen.id JRen.drop hm
        exact ⟨_, .inr (hs'.castLvl ho), .inr (.join_drop σ u uₓ body hm₂' ho)⟩
  | _, _, _, _, _, _, _, _, .join_body σ u uₓ main hs => by
      intro h₂
      have h := h₂.inv
      simp only [Branch.StepInv] at h
      rcases h with ⟨m₂, hm₂, ho₂, rfl⟩ | ⟨body', hs₂, rfl⟩ | ⟨m₂, hs₂, rfl⟩
      · exact ⟨_, .inr (.join_drop σ u uₓ _ hm₂ ho₂), .inl rfl⟩
      · obtain ⟨b₃, h1, h2⟩ := Term.Step.diamond hs hs₂
        exact ⟨_, h1.map (fun x => Branch.join σ u uₓ x main) (fun _ _ h => Branch.Step.join_body σ u uₓ main h),
          h2.map (fun x => Branch.join σ u uₓ x main) (fun _ _ h => Branch.Step.join_body σ u uₓ main h)⟩
      · exact ⟨_, .inr (.join_main σ u uₓ _ hs₂), .inr (.join_body σ u uₓ _ hs)⟩
  | _, _, _, _, _, _, _, _, .join_main σ u uₓ body hs => by
      intro h₂
      have h := h₂.inv
      simp only [Branch.StepInv] at h
      rcases h with ⟨m₂, hm₂, ho₂, rfl⟩ | ⟨body', hs₂, rfl⟩ | ⟨m₂, hs₂, rfl⟩
      · obtain ⟨m₁', hm₁', hs'⟩ := hs.rename KRen.id URen.id JRen.drop hm₂
        exact ⟨_, .inr (.join_drop σ u uₓ body hm₁' ho₂), .inr (hs'.castLvl ho₂)⟩
      · exact ⟨_, .inr (.join_body σ u uₓ _ hs₂), .inr (.join_main σ u uₓ _ hs)⟩
      · obtain ⟨m₃, h1, h2⟩ := Branch.Step.diamond hs hs₂
        exact ⟨_, h1.map (fun x => Branch.join σ u uₓ body x) (fun _ _ h => Branch.Step.join_main σ u uₓ body h),
          h2.map (fun x => Branch.join σ u uₓ body x) (fun _ _ h => Branch.Step.join_main σ u uₓ body h)⟩
  | _, _, _, _, _, _, _, _, .ite_then c e hs => by
      intro h₂
      have h := h₂.inv
      simp only [Branch.StepInv] at h
      rcases h with ⟨t', hs₂, rfl⟩ | ⟨e', hs₂, rfl⟩
      · obtain ⟨t₃, h1, h2⟩ := Term.Step.diamond hs hs₂
        exact ⟨_, h1.map (fun x => Branch.ite c x e) (fun _ _ h => Branch.Step.ite_then c e h), h2.map (fun x => Branch.ite c x e) (fun _ _ h => Branch.Step.ite_then c e h)⟩
      · exact ⟨_, .inr (.ite_else c _ hs₂), .inr (.ite_then c _ hs)⟩
  | _, _, _, _, _, _, _, _, .ite_else c t hs => by
      intro h₂
      have h := h₂.inv
      simp only [Branch.StepInv] at h
      rcases h with ⟨t', hs₂, rfl⟩ | ⟨e', hs₂, rfl⟩
      · exact ⟨_, .inr (.ite_then c _ hs₂), .inr (.ite_else c _ hs)⟩
      · obtain ⟨e₃, h1, h2⟩ := Term.Step.diamond hs hs₂
        exact ⟨_, h1.map (fun x => Branch.ite c t x) (fun _ _ h => Branch.Step.ite_else c t h), h2.map (fun x => Branch.ite c t x) (fun _ _ h => Branch.Step.ite_else c t h)⟩
  | _, _, _, _, _, _, _, _, .enum_casesOn e i hs hbs => by
      intro h₂
      have h := h₂.inv
      simp only [Branch.StepInv] at h
      obtain ⟨bs₂, i₂, hs₂, hbs₂, rfl⟩ := h
      have ih : (hi : i = i₂) → _ := fun hi => by
        subst hi; exact Term.Step.diamond hs hs₂
      obtain ⟨g₃, h1, h2⟩ := Fin.FamStep.diamond (R := fun _ => Term.Step) hs hbs hs₂ hbs₂ ih
      exact ⟨_, ReflGen.map (fun g => Branch.enum_casesOn e g)
          (fun _ _ hh => by obtain ⟨i, h, hne⟩ := hh; exact Branch.Step.enum_casesOn e i h hne) h1,
        ReflGen.map (fun g => Branch.enum_casesOn e g)
          (fun _ _ hh => by obtain ⟨i, h, hne⟩ := hh; exact Branch.Step.enum_casesOn e i h hne) h2⟩
  | _, _, _, _, _, _, _, _, .union_casesOn e hs => by
      intro h₂
      have h := h₂.inv
      simp only [Branch.StepInv] at h
      obtain ⟨brs₂, hs₂, rfl⟩ := h
      obtain ⟨brs₃, h1, h2⟩ := Branches.Step.diamond hs hs₂
      exact ⟨_, h1.map (fun x => Branch.union_casesOn e x) (fun _ _ h => Branch.Step.union_casesOn e h),
        h2.map (fun x => Branch.union_casesOn e x) (fun _ _ h => Branch.Step.union_casesOn e h)⟩
  termination_by structural _ _ _ _ _ _ _ _ x => x
theorem Branches.Step.diamond : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    {t t₁ : Branches Δ d Φ Γ cs τ js o} → Branches.Step t t₁ →
    ∀ {t₂}, Branches.Step t t₂ → ∃ t₃, ReflGen Branches.Step t₁ t₃ ∧ ReflGen Branches.Step t₂ t₃
  | _, _, _, _, _, _, _, _, _, _, .two_left us₁ us₂ b₂ hs => by
      intro h₂
      have h := h₂.inv
      simp only [Branches.StepInv] at h
      rcases h with ⟨b₁', hs₂, rfl⟩ | ⟨b₂', hs₂, rfl⟩
      · obtain ⟨b₃, h1, h2⟩ := Term.Step.diamond hs hs₂
        exact ⟨_, h1.map (fun x => Branches.two us₁ us₂ x b₂) (fun _ _ h => Branches.Step.two_left us₁ us₂ b₂ h),
          h2.map (fun x => Branches.two us₁ us₂ x b₂) (fun _ _ h => Branches.Step.two_left us₁ us₂ b₂ h)⟩
      · exact ⟨_, .inr (.two_right us₁ us₂ _ hs₂), .inr (.two_left us₁ us₂ _ hs)⟩
  | _, _, _, _, _, _, _, _, _, _, .two_right us₁ us₂ b₁ hs => by
      intro h₂
      have h := h₂.inv
      simp only [Branches.StepInv] at h
      rcases h with ⟨b₁', hs₂, rfl⟩ | ⟨b₂', hs₂, rfl⟩
      · exact ⟨_, .inr (.two_left us₁ us₂ _ hs₂), .inr (.two_right us₁ us₂ _ hs)⟩
      · obtain ⟨b₃, h1, h2⟩ := Term.Step.diamond hs hs₂
        exact ⟨_, h1.map (fun x => Branches.two us₁ us₂ b₁ x) (fun _ _ h => Branches.Step.two_right us₁ us₂ b₁ h),
          h2.map (fun x => Branches.two us₁ us₂ b₁ x) (fun _ _ h => Branches.Step.two_right us₁ us₂ b₁ h)⟩
  | _, _, _, _, _, _, _, _, _, _, .cons_head us brs hs => by
      intro h₂
      have h := h₂.inv
      simp only [Branches.StepInv] at h
      rcases h with ⟨b', hs₂, rfl⟩ | ⟨brs', hs₂, rfl⟩
      · obtain ⟨b₃, h1, h2⟩ := Term.Step.diamond hs hs₂
        exact ⟨_, h1.map (fun x => Branches.cons us x brs) (fun _ _ h => Branches.Step.cons_head us brs h),
          h2.map (fun x => Branches.cons us x brs) (fun _ _ h => Branches.Step.cons_head us brs h)⟩
      · exact ⟨_, .inr (.cons_tail us _ hs₂), .inr (.cons_head us _ hs)⟩
  | _, _, _, _, _, _, _, _, _, _, .cons_tail us b hs => by
      intro h₂
      have h := h₂.inv
      simp only [Branches.StepInv] at h
      rcases h with ⟨b', hs₂, rfl⟩ | ⟨brs', hs₂, rfl⟩
      · exact ⟨_, .inr (.cons_head us _ hs₂), .inr (.cons_tail us _ hs)⟩
      · obtain ⟨brs₃, h1, h2⟩ := Branches.Step.diamond hs hs₂
        exact ⟨_, h1.map (fun x => Branches.cons us b x) (fun _ _ h => Branches.Step.cons_tail us b h),
          h2.map (fun x => Branches.cons us b x) (fun _ _ h => Branches.Step.cons_tail us b h)⟩
  termination_by structural _ _ _ _ _ _ _ _ _ _ x => x
end

/-! ## Church–Rosser -/

section ChurchRosser
variable {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}

/-- **Strong confluence** of the rewrites of a statement. -/
theorem Term.Step.stronglyConfluent : StronglyConfluent (@Term.Step ks Δ d Φ Γ τ js o) :=
  fun h₁ h₂ => Term.Step.diamond h₁ h₂

/-- **Confluence**: two rewrite sequences out of the same statement can be continued to a common
    statement. -/
theorem Term.Step.confluent : Confluent (@Term.Step ks Δ d Φ Γ τ js o) :=
  confluent_of_strongly Term.Step.stronglyConfluent

/-- **Church–Rosser**: two statements related by rewrites taken in either direction rewrite to a
    common statement. -/
theorem Term.Step.churchRosser : ChurchRosser (@Term.Step ks Δ d Φ Γ τ js o) :=
  churchRosser_of_confluent Term.Step.confluent

/-- A statement has at most one normal form. -/
theorem Term.Step.normal_unique {t n₁ n₂ : Term Δ d Φ Γ τ js o} (h₁ : Star Term.Step t n₁)
    (h₂ : Star Term.Step t n₂) (hn₁ : Normal Term.Step n₁) (hn₂ : Normal Term.Step n₂) :
    n₁ = n₂ :=
  Term.Step.confluent.normal_unique h₁ h₂ hn₁ hn₂

/-- Rewriting does not change the value. -/
theorem Term.Step.star_eval {t t' : Term Δ d Φ Γ τ js o} (h : Star Term.Step t t')
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) : t'.eval κ ρ jκ = t.eval κ ρ jκ := by
  induction h with
  | refl => rfl
  | tail _ h ih => rw [h.eval, ih]

/-- Statements related by rewrites (in either direction) have the same value. -/
theorem Term.Step.conv_eval {t t' : Term Δ d Φ Γ τ js o} (h : Conv Term.Step t t')
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) : t.eval κ ρ jκ = t'.eval κ ρ jκ := by
  induction h with
  | refl => rfl
  | fwd h => exact (h.eval κ ρ jκ).symm
  | bwd h => exact h.eval κ ρ jκ
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Church–Rosser for `Term.eval`**: two statements related by rewrites rewrite to a common
    statement, which has the value of both, in every environment. -/
theorem Term.eval_churchRosser {t₁ t₂ : Term Δ d Φ Γ τ js o} (h : Conv Term.Step t₁ t₂) :
    ∃ t₃, Star Term.Step t₁ t₃ ∧ Star Term.Step t₂ t₃ ∧
      ∀ (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js),
        t₃.eval κ ρ jκ = t₁.eval κ ρ jκ ∧ t₃.eval κ ρ jκ = t₂.eval κ ρ jκ := by
  obtain ⟨t₃, h₁, h₂⟩ := Term.Step.churchRosser h
  exact ⟨t₃, h₁, h₂, fun κ ρ jκ => ⟨Term.Step.star_eval h₁ κ ρ jκ, Term.Step.star_eval h₂ κ ρ jκ⟩⟩

/-- **Confluence for `Term.eval`**: two rewrite sequences out of the same statement can be
    continued to a common statement, and every statement on the way has the value of the first. -/
theorem Term.eval_confluent {t t₁ t₂ : Term Δ d Φ Γ τ js o} (h₁ : Star Term.Step t t₁)
    (h₂ : Star Term.Step t t₂) :
    ∃ t₃, Star Term.Step t₁ t₃ ∧ Star Term.Step t₂ t₃ ∧
      ∀ (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js), t₃.eval κ ρ jκ = t.eval κ ρ jκ := by
  obtain ⟨t₃, h₁₃, h₂₃⟩ := Term.Step.confluent h₁ h₂
  exact ⟨t₃, h₁₃, h₂₃, fun κ ρ jκ => Term.Step.star_eval (h₁.trans h₁₃) κ ρ jκ⟩

end ChurchRosser

/-- For whole programs: two programs related by rewrites rewrite to a common program, with the
    same result as both. -/
theorem Term.run_churchRosser {τ : Ty ks} {o : Lvl} {t₁ t₂ : Term Δ 0 [] [] τ [] o}
    (h : Conv Term.Step t₁ t₂) :
    ∃ t₃, Star Term.Step t₁ t₃ ∧ Star Term.Step t₂ t₃ ∧ t₃.run = t₁.run ∧ t₃.run = t₂.run := by
  obtain ⟨t₃, h₁, h₂, hv⟩ := Term.eval_churchRosser h
  exact ⟨t₃, h₁, h₂, hv _ _ _⟩

end LeanScript

end
