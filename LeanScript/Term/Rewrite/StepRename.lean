module

public import LeanScript.Term.Rewrite.Step

@[expose] public section

set_option autoImplicit false

/-!
# Steps commute with renamings

`Term.Step.rename`: if `t` steps to `t₁` and renaming `t` succeeds (giving `t'`), then renaming
`t₁` succeeds too (a step never makes a statement use a variable it did not use), giving
`t₁'`, and `t'` steps to `t₁'`.  The same holds for every other layer.  This is what lets a
step inside the body of a dropped or copy-propagated binding be replayed after the drop.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-- Changing one entry of a family whose options were all `some`. -/
theorem Fin.optAll_update {n : Nat} {γ β : Fin n → Type} {as as' : (i : Fin n) → γ i} {i : Fin n}
    (hg : ∀ i', i' ≠ i → as' i' = as i') (F : (i : Fin n) → γ i → Option (β i))
    {xs : (i : Fin n) → β i} {X : β i} (hX : F i (as' i) = some X)
    (hf : Fin.optAll (fun i => F i (as i)) = some xs) :
    ∃ ys, Fin.optAll (fun i => F i (as' i)) = some ys ∧ ys i = X ∧
      ∀ i', i' ≠ i → ys i' = xs i' := by
  have hall : ∀ i', (F i' (as' i')).isSome = true := by
    intro i'
    by_cases hi : i' = i
    · subst hi; simp [hX]
    · rw [hg i' hi, Fin.optAll_eq_some hf i']; rfl
  obtain ⟨ys, hys⟩ := Option.isSome_iff_exists.mp (Fin.optAll_isSome hall)
  refine ⟨ys, hys, ?_, ?_⟩
  · have h1 := Fin.optAll_eq_some hys i
    rw [hX] at h1
    exact (Option.some.inj h1).symm
  · intro i' hi
    have h1 := Fin.optAll_eq_some hys i'
    simp only [hg i' hi, Fin.optAll_eq_some hf i'] at h1
    exact (Option.some.inj h1).symm

/-- `PExpr.substHead` commutes with renamings. -/
theorem PExpr.substHead_rename {Φ Φ' : KCtx ks} {Γ Γ' : UCtx ks} {σ τ : Ty ks} {u : Usage01ω}
    {d ℓ : Nat} {o : Lvl} (n : Neu Δ Φ Γ σ ℓ) (hl : ℓ = d) (e : PExpr Δ Φ (⟨σ, u, d⟩ :: Γ) τ o)
    {e' : PExpr Δ Φ Γ τ o} (he : PExpr.substHead n hl e = some e') (rk : KRen Φ Φ')
    (ru : URen Γ Γ') {n' : Neu Δ Φ' Γ' σ ℓ} (hn : n.rename rk ru = some n')
    {er : PExpr Δ Φ' (⟨σ, u, d⟩ :: Γ') τ o} (hr : e.rename rk (URen.lift ru _) = some er) :
    ∃ er', e'.rename rk ru = some er' ∧ PExpr.substHead n' hl er = some er' := by
  subst hl
  cases e with
  | neu m =>
      cases m with
      | var x =>
          cases x with
          | head h =>
              simp only [PExpr.substHead, Neu.substHead, Option.map_some, Option.some.injEq] at he
              subst he
              simp only [PExpr.rename, Neu.rename, URen.lift, Option.map_some,
                Option.some.injEq] at hr
              subst hr
              exact ⟨.neu n', by simp [PExpr.rename, hn], by simp [PExpr.substHead, Neu.substHead]⟩
          | tail => simp [PExpr.substHead, Neu.substHead] at he
      | _ => simp [PExpr.substHead, Neu.substHead] at he
  | _ => simp [PExpr.substHead] at he

mutual
theorem Val.Step.rename : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    {v v₁ : Val Δ d Φ Γ τ o} → Val.Step v v₁ →
    ∀ {Φ' : KCtx ks} {Γ' : UCtx ks} (rk : KRen Φ Φ') (ru : URen Γ Γ') {v' : Val Δ d Φ' Γ' τ o},
    v.rename rk ru = some v' → ∃ v₁', v₁.rename rk ru = some v₁' ∧ Val.Step v' v₁'
  | _, _, _, _, _, _, _, .lam hs => by
      intro rk ru _ h
      simp only [Val.rename, Option.map_eq_some_iff] at h
      obtain ⟨b', hb, rfl⟩ := h
      obtain ⟨b₁', hb₁, hs'⟩ := Body.Step.rename hs rk ru hb
      exact ⟨_, by simp [Val.rename, hb₁], .lam hs'⟩
  | _, _, _, _, _, _, _, .thunk_mk hs => by
      intro rk ru _ h
      simp only [Val.rename, Option.map_eq_some_iff] at h
      obtain ⟨b', hb, rfl⟩ := h
      obtain ⟨b₁', hb₁, hs'⟩ := Body.Step.rename hs rk ru hb
      exact ⟨_, by simp [Val.rename, hb₁], .thunk_mk hs'⟩
  | _, _, _, _, _, _, _, .lazy_mk hs => by
      intro rk ru _ h
      simp only [Val.rename, Option.map_eq_some_iff] at h
      obtain ⟨b', hb, rfl⟩ := h
      obtain ⟨b₁', hb₁, hs'⟩ := Body.Step.rename hs rk ru hb
      exact ⟨_, by simp [Val.rename, hb₁], .lazy_mk hs'⟩
  termination_by structural _ _ _ _ _ _ _ x => x
theorem Body.Step.rename : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → {b b₁ : Body Δ d Φ Γ bs τ o} → Body.Step b b₁ →
    ∀ {Φ' : KCtx ks} {Γ' : UCtx ks} (rk : KRen Φ Φ') (ru : URen Γ Γ')
      {b' : Body Δ d Φ' Γ' bs τ o},
    b.rename rk ru = some b' → ∃ b₁', b₁.rename rk ru = some b₁' ∧ Body.Step b' b₁'
  | _, _, _, _, _, _, _, _, .closed hs => by
      intro rk ru _ h
      simp only [Body.rename, Option.map_eq_some_iff] at h
      obtain ⟨t', ht, rfl⟩ := h
      obtain ⟨t₁', ht₁, hs'⟩ := Term.Step.rename hs (KRen.closedOnly rk) URen.id JRen.nil ht
      exact ⟨_, by simp [Body.rename, ht₁], .closed hs'⟩
  | _, _, _, bs, _, _, _, _, .opened hm hs => by
      intro rk ru _ h
      simp only [Body.rename, Option.map_eq_some_iff] at h
      obtain ⟨t', ht, rfl⟩ := h
      obtain ⟨t₁', ht₁, hs'⟩ := Term.Step.rename hs rk (URen.liftN ru bs) JRen.nil ht
      exact ⟨_, by simp [Body.rename, ht₁], .opened hm hs'⟩
  termination_by structural _ _ _ _ _ _ _ _ x => x
theorem Comp.Step.rename : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    {c c₁ : Comp Δ d Φ Γ τ ℓ} → Comp.Step c c₁ →
    ∀ {Φ' : KCtx ks} {Γ' : UCtx ks} (rk : KRen Φ Φ') (ru : URen Γ Γ') {c' : Comp Δ d Φ' Γ' τ ℓ},
    c.rename rk ru = some c' → ∃ c₁', c₁.rename rk ru = some c₁' ∧ Comp.Step c' c₁'
  | _, _, _, _, _, _, _, .nat_rec n z hℓ hs => by
      intro rk ru _ h
      simp only [Comp.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨n', hn, z', hz, s', hs₀, rfl⟩ := h
      obtain ⟨s₁', hs₁, hs'⟩ := Body.Step.rename hs rk ru hs₀
      exact ⟨_, by simp [Comp.rename, hn, hz, hs₁], .nat_rec n' z' hℓ hs'⟩
  | _, _, _, _, _, _, _, .array_foldl a z hℓ hs => by
      intro rk ru _ h
      simp only [Comp.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨a', ha, z', hz, s', hs₀, rfl⟩ := h
      obtain ⟨s₁', hs₁, hs'⟩ := Body.Step.rename hs rk ru hs₀
      exact ⟨_, by simp [Comp.rename, ha, hz, hs₁], .array_foldl a' z' hℓ hs'⟩
  | _, _, _, _, _, _, _, .data_rec b ρt us j e hℓ i hs hbs => by
      intro rk ru _ h
      simp only [Comp.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨bsr, hbsr, e', he, rfl⟩ := h
      obtain ⟨X, hX, hsX⟩ := Body.Step.rename hs rk ru (Fin.optAll_eq_some hbsr i)
      obtain ⟨bsr', hbsr', hi₁, hi₂⟩ :=
        Fin.optAll_update hbs (fun _ b => b.rename rk ru) hX hbsr
      refine ⟨.data_rec b ρt us bsr' j e' hℓ, by simp [Comp.rename, he, hbsr'],
        .data_rec b ρt us j e' hℓ i (hi₁ ▸ hsX) hi₂⟩
  | _, _, _, _, _, _, _, .data_brec b ρt k us j e hℓ i hs hbs => by
      intro rk ru _ h
      simp only [Comp.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨bsr, hbsr, e', he, rfl⟩ := h
      obtain ⟨X, hX, hsX⟩ := Body.Step.rename hs rk ru (Fin.optAll_eq_some hbsr i)
      obtain ⟨bsr', hbsr', hi₁, hi₂⟩ :=
        Fin.optAll_update hbs (fun _ b => b.rename rk ru) hX hbsr
      refine ⟨.data_brec b ρt k us bsr' j e' hℓ, by simp [Comp.rename, he, hbsr'],
        .data_brec b ρt k us j e' hℓ i (hi₁ ▸ hsX) hi₂⟩
  termination_by structural _ _ _ _ _ _ _ x => x
theorem Term.Step.rename : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → {t t₁ : Term Δ d Φ Γ τ js o} → Term.Step t t₁ →
    ∀ {Φ' : KCtx ks} {Γ' : UCtx ks} {js' : JCtx ks} (rk : KRen Φ Φ') (ru : URen Γ Γ')
      (rj : JRen js js') {t' : Term Δ d Φ' Γ' τ js' o},
    t.rename rk ru rj = some t' → ∃ t₁', t₁.rename rk ru rj = some t₁' ∧ Term.Step t' t₁'
  | _, _, _, _, _, _, _, _, .letV_drop u v hb ho => by
      intro rk ru rj _ h
      simp only [Term.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨v', hv, br, hbr, rfl⟩ := h
      have e₁ := Term.rename_comp (KRen.CompOn.comp KRen.drop rk) (URen.CompOn.id_left ru)
        (JRen.CompOn.id_left rj) _ hb
      have e₂ := Term.rename_comp (KRen.CompOn.lift_drop rk _) (URen.CompOn.id_right ru)
        (JRen.CompOn.id_right rj) _ hbr
      obtain ⟨Y, hY⟩ := Option.isSome_iff_exists.mp (Term.rename_meet (KRen.Meet.drop_lift rk _)
        (URen.Meet.id_left ru) (JRen.Meet.id_left rj) _ hb hbr)
      refine ⟨Y.castLvl ho, ?_, .letV_drop u v' (e₂.trans hY) ho⟩
      rw [Term.rename_castLvl, e₁, hY]; rfl
  | _, _, _, _, _, _, _, _, .letE_drop u c hb ho => by
      intro rk ru rj _ h
      simp only [Term.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨c', hc, br, hbr, rfl⟩ := h
      have e₁ := Term.rename_comp (KRen.CompOn.id_left rk) (URen.CompOn.comp URen.drop ru)
        (JRen.CompOn.id_left rj) _ hb
      have e₂ := Term.rename_comp (KRen.CompOn.id_right rk) (URen.CompOn.lift_drop ru _ _ _)
        (JRen.CompOn.id_right rj) _ hbr
      obtain ⟨Y, hY⟩ := Option.isSome_iff_exists.mp (Term.rename_meet (KRen.Meet.id_left rk)
        (URen.Meet.drop_lift ru _ _ _) (JRen.Meet.id_left rj) _ hb hbr)
      refine ⟨Y.castLvl ho, ?_, .letE_drop u c' (e₂.trans hY) ho⟩
      rw [Term.rename_castLvl, e₁, hY]; rfl
  | _, _, _, _, _, _, _, _, .copy u x hl hb ho => by
      intro rk ru rj _ h
      subst hl
      simp only [Term.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨c', hc, br, hbr, rfl⟩ := h
      simp only [Comp.rename, Neu.rename, Option.map_map, Option.map_eq_some_iff] at hc
      obtain ⟨x', hx', rfl⟩ := hc
      have e₁ := Term.rename_comp (KRen.CompOn.id_left rk) (URen.CompOn.comp (URen.subst x rfl) ru)
        (JRen.CompOn.id_left rj) _ hb
      have e₂ := Term.rename_comp (KRen.CompOn.id_right rk) (URen.CompOn.lift_subst ru x x' hx')
        (JRen.CompOn.id_right rj) _ hbr
      obtain ⟨Y, hY⟩ := Option.isSome_iff_exists.mp (Term.rename_meet (KRen.Meet.id_left rk)
        (URen.Meet.subst_lift ru x x' hx') (JRen.Meet.id_left rj) _ hb hbr)
      refine ⟨Y.castLvl ho, ?_, .copy u x' rfl (e₂.trans hY) ho⟩
      rw [Term.rename_castLvl, e₁, hY]; rfl
  | _, _, _, _, _, _, _, _, .share_ret u n hl he ho => by
      intro rk ru rj _ h
      simp only [Term.rename, Comp.rename, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq, Option.map_eq_some_iff] at h
      obtain ⟨_, ⟨n', hn, rfl⟩, _, ⟨er, hr, rfl⟩, rfl⟩ := h
      obtain ⟨er', her', hsub⟩ := PExpr.substHead_rename n hl _ he rk ru hn hr
      exact ⟨(Term.ret er').castLvl ho, by simp [Term.rename_castLvl, Term.rename, her'],
        .share_ret u n' hl hsub ho⟩
  | _, _, _, _, _, _, _, _, .share_jump u n hl j he ho => by
      intro rk ru rj _ h
      simp only [Term.rename, Comp.rename, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq, Option.map_eq_some_iff] at h
      obtain ⟨_, ⟨n', hn, rfl⟩, _, ⟨j', hj, er, hr, rfl⟩, rfl⟩ := h
      obtain ⟨er', her', hsub⟩ := PExpr.substHead_rename n hl _ he rk ru hn hr
      exact ⟨(Term.jump j' er').castLvl ho, by simp [Term.rename_castLvl, Term.rename, her', hj],
        .share_jump u n' hl j' hsub ho⟩
  | _, _, _, _, _, _, _, _, .casesOn_drop us n hb ho => by
      intro rk ru rj _ h
      simp only [Term.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨n', hn, br, hbr, rfl⟩ := h
      have e₁ := Term.rename_comp (KRen.CompOn.id_left rk) (URen.CompOn.comp (URen.dropN _) ru)
        (JRen.CompOn.id_left rj) _ hb
      have e₂ := Term.rename_comp (KRen.CompOn.id_right rk) (URen.CompOn.liftN_dropN ru _)
        (JRen.CompOn.id_right rj) _ hbr
      obtain ⟨Y, hY⟩ := Option.isSome_iff_exists.mp (Term.rename_meet (KRen.Meet.id_left rk)
        (URen.Meet.dropN_liftN ru _) (JRen.Meet.id_left rj) _ hb hbr)
      refine ⟨Y.castLvl ho, ?_, .casesOn_drop us n' (e₂.trans hY) ho⟩
      rw [Term.rename_castLvl, e₁, hY]; rfl
  | _, _, _, _, _, _, _, _, .letV_val u b hs => by
      intro rk ru rj _ h
      simp only [Term.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨v', hv, b', hb, rfl⟩ := h
      obtain ⟨v₁', hv₁, hs'⟩ := Val.Step.rename hs rk ru hv
      exact ⟨_, by simp [Term.rename, hv₁, hb], .letV_val u b' hs'⟩
  | _, _, _, _, _, _, _, _, .letV_body u v hs => by
      intro rk ru rj _ h
      simp only [Term.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨v', hv, b', hb, rfl⟩ := h
      obtain ⟨b₁', hb₁, hs'⟩ := Term.Step.rename hs (KRen.lift rk _) ru rj hb
      exact ⟨_, by simp [Term.rename, hv, hb₁], .letV_body u v' hs'⟩
  | _, _, _, _, _, _, _, _, .letE_comp u b hs => by
      intro rk ru rj _ h
      simp only [Term.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨c', hc, b', hb, rfl⟩ := h
      obtain ⟨c₁', hc₁, hs'⟩ := Comp.Step.rename hs rk ru hc
      exact ⟨_, by simp [Term.rename, hc₁, hb], .letE_comp u b' hs'⟩
  | _, _, _, _, _, _, _, _, .letE_body u c hs => by
      intro rk ru rj _ h
      simp only [Term.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨c', hc, b', hb, rfl⟩ := h
      obtain ⟨b₁', hb₁, hs'⟩ := Term.Step.rename hs rk (URen.lift ru _) rj hb
      exact ⟨_, by simp [Term.rename, hc, hb₁], .letE_body u c' hs'⟩
  | _, _, _, _, _, _, _, _, .casesOn_body us n hs => by
      intro rk ru rj _ h
      simp only [Term.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨n', hn, b', hb, rfl⟩ := h
      obtain ⟨b₁', hb₁, hs'⟩ := Term.Step.rename hs rk (URen.liftN ru _) rj hb
      exact ⟨_, by simp [Term.rename, hn, hb₁], .casesOn_body us n' hs'⟩
  | _, _, _, _, _, _, _, _, .branch hs => by
      intro rk ru rj _ h
      simp only [Term.rename, Option.map_eq_some_iff] at h
      obtain ⟨br', hbr, rfl⟩ := h
      obtain ⟨br₁', hbr₁, hs'⟩ := Branch.Step.rename hs rk ru rj hbr
      exact ⟨_, by simp [Term.rename, hbr₁], .branch hs'⟩
  termination_by structural _ _ _ _ _ _ _ _ x => x
theorem Branch.Step.rename : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → {t t₁ : Branch Δ d Φ Γ τ js ℓ} → Branch.Step t t₁ →
    ∀ {Φ' : KCtx ks} {Γ' : UCtx ks} {js' : JCtx ks} (rk : KRen Φ Φ') (ru : URen Γ Γ')
      (rj : JRen js js') {t' : Branch Δ d Φ' Γ' τ js' ℓ},
    t.rename rk ru rj = some t' → ∃ t₁', t₁.rename rk ru rj = some t₁' ∧ Branch.Step t' t₁'
  | _, _, _, _, _, _, _, _, .join_drop σ u uₓ body hm ho => by
      intro rk ru rj _ h
      simp only [Branch.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨body', hbody, mr, hmr, rfl⟩ := h
      have e₁ := Branch.rename_comp (KRen.CompOn.id_left rk) (URen.CompOn.id_left ru)
        (JRen.CompOn.comp JRen.drop rj) _ hm
      have e₂ := Branch.rename_comp (KRen.CompOn.id_right rk) (URen.CompOn.id_right ru)
        (JRen.CompOn.lift_drop rj _ _) _ hmr
      obtain ⟨Y, hY⟩ := Option.isSome_iff_exists.mp (Branch.rename_meet (KRen.Meet.id_left rk)
        (URen.Meet.id_left ru) (JRen.Meet.drop_lift rj _ _) _ hm hmr)
      refine ⟨Y.castLvl ho, ?_, .join_drop σ u uₓ body' (e₂.trans hY) ho⟩
      rw [Branch.rename_castLvl, e₁, hY]; rfl
  | _, _, _, _, _, _, _, _, .ite_then c e hs => by
      intro rk ru rj _ h
      simp only [Branch.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨c', hc, t', ht, e', he, rfl⟩ := h
      obtain ⟨t₁', ht₁, hs'⟩ := Term.Step.rename hs rk ru rj ht
      exact ⟨_, by simp [Branch.rename, hc, ht₁, he], .ite_then c' e' hs'⟩
  | _, _, _, _, _, _, _, _, .ite_else c t hs => by
      intro rk ru rj _ h
      simp only [Branch.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨c', hc, t', ht, e', he, rfl⟩ := h
      obtain ⟨e₁', he₁, hs'⟩ := Term.Step.rename hs rk ru rj he
      exact ⟨_, by simp [Branch.rename, hc, ht, he₁], .ite_else c' t' hs'⟩
  | _, _, _, _, _, _, _, _, .enum_casesOn e i hs hbs => by
      intro rk ru rj _ h
      simp only [Branch.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨e', he, bsr, hbsr, rfl⟩ := h
      obtain ⟨X, hX, hsX⟩ := Term.Step.rename hs rk ru rj (Fin.optAll_eq_some hbsr i)
      obtain ⟨bsr', hbsr', hi₁, hi₂⟩ :=
        Fin.optAll_update hbs (fun _ b => b.rename rk ru rj) hX hbsr
      refine ⟨.enum_casesOn e' bsr', by simp [Branch.rename, he, hbsr'],
        .enum_casesOn e' i (hi₁ ▸ hsX) hi₂⟩
  | _, _, _, _, _, _, _, _, .union_casesOn e hs => by
      intro rk ru rj _ h
      simp only [Branch.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨e', he, bs', hbs, rfl⟩ := h
      obtain ⟨bs₁', hbs₁, hs'⟩ := Branches.Step.rename hs rk ru rj hbs
      exact ⟨_, by simp [Branch.rename, he, hbs₁], .union_casesOn e' hs'⟩
  | _, _, _, _, _, _, _, _, .join_body σ u uₓ main hs => by
      intro rk ru rj _ h
      simp only [Branch.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨body', hbody, main', hmain, rfl⟩ := h
      obtain ⟨body₁', hbody₁, hs'⟩ := Term.Step.rename hs rk (URen.lift ru _) rj hbody
      exact ⟨_, by simp [Branch.rename, hbody₁, hmain], .join_body σ u uₓ main' hs'⟩
  | _, _, _, _, _, _, _, _, .join_main σ u uₓ body hs => by
      intro rk ru rj _ h
      simp only [Branch.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨body', hbody, main', hmain, rfl⟩ := h
      obtain ⟨main₁', hmain₁, hs'⟩ := Branch.Step.rename hs rk ru (JRen.lift rj _) hmain
      exact ⟨_, by simp [Branch.rename, hbody, hmain₁], .join_main σ u uₓ body' hs'⟩
  termination_by structural _ _ _ _ _ _ _ _ x => x
theorem Branches.Step.rename : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    {t t₁ : Branches Δ d Φ Γ cs τ js o} → Branches.Step t t₁ →
    ∀ {Φ' : KCtx ks} {Γ' : UCtx ks} {js' : JCtx ks} (rk : KRen Φ Φ') (ru : URen Γ Γ')
      (rj : JRen js js') {t' : Branches Δ d Φ' Γ' cs τ js' o},
    t.rename rk ru rj = some t' → ∃ t₁', t₁.rename rk ru rj = some t₁' ∧ Branches.Step t' t₁'
  | _, _, _, _, _, _, _, _, _, _, .two_left us₁ us₂ b₂ hs => by
      intro rk ru rj _ h
      simp only [Branches.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨b₁', h₁, b₂', h₂, rfl⟩ := h
      obtain ⟨b₁'', h₁', hs'⟩ := Term.Step.rename hs rk (URen.liftN ru _) rj h₁
      exact ⟨_, by simp [Branches.rename, h₁', h₂], .two_left us₁ us₂ b₂' hs'⟩
  | _, _, _, _, _, _, _, _, _, _, .two_right us₁ us₂ b₁ hs => by
      intro rk ru rj _ h
      simp only [Branches.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨b₁', h₁, b₂', h₂, rfl⟩ := h
      obtain ⟨b₂'', h₂', hs'⟩ := Term.Step.rename hs rk (URen.liftN ru _) rj h₂
      exact ⟨_, by simp [Branches.rename, h₁, h₂'], .two_right us₁ us₂ b₁' hs'⟩
  | _, _, _, _, _, _, _, _, _, _, .cons_head us brs hs => by
      intro rk ru rj _ h
      simp only [Branches.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨b', hb, brs', hbrs, rfl⟩ := h
      obtain ⟨b₁', hb₁, hs'⟩ := Term.Step.rename hs rk (URen.liftN ru _) rj hb
      exact ⟨_, by simp [Branches.rename, hb₁, hbrs], .cons_head us brs' hs'⟩
  | _, _, _, _, _, _, _, _, _, _, .cons_tail us b hs => by
      intro rk ru rj _ h
      simp only [Branches.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨b', hb, brs', hbrs, rfl⟩ := h
      obtain ⟨brs₁', hbrs₁, hs'⟩ := Branches.Step.rename hs rk ru rj hbrs
      exact ⟨_, by simp [Branches.rename, hb, hbrs₁], .cons_tail us b' hs'⟩
  termination_by structural _ _ _ _ _ _ _ _ _ _ x => x
end

end LeanScript

end
