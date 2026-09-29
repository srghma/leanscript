module

public import LeanScript.Term.Optimize.InlineSubst
public import LeanScript.Term.Optimize.SubstEval

@[expose] public section

set_option autoImplicit false

/-!
# Inlining with arguments and answers that are not neutral preserves the value

`BlockFn.applyP_eval` (the body at a call on any argument is the call), `Term.bindAns_eval` and
`Term.bindRet_eval` (a straight-line body followed by the rest is the rest applied to its
answer).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Small maps -/

theorem ULRen.Agree.idL {Γ : UCtx ks} (ρ : UEnv Δ Γ) : ULRen.Agree ULRen.idL ρ ρ := by
  intro _ _ x p h
  simp only [ULRen.idL, Option.some.injEq] at h
  subst h; rfl

theorem KLRen.Agree.wk1 {Φ : KCtx ks} {b : KBinder ks} (κ : KEnv Δ Φ) (x : Ty.Den Δ b.ty) :
    KLRen.Agree (KLRen.wk1 (b := b)) κ (Tuple.cons x κ : KEnv Δ (b :: Φ)) := by
  intro _ _ y p h
  simp only [KLRen.wk1, Option.some.injEq] at h
  subst h
  exact KEnv.get_cons_tail _ _ _

theorem USub.Agree.none {Φ' : KCtx ks} {Γ' : UCtx ks} (κ' : KEnv Δ Φ') (ρ' : UEnv Δ Γ') :
    USub.Agree (USub.none (Δ := Δ) (Φ' := Φ') (Γ' := Γ')) κ' PUnit.unit ρ' := by
  intro _ _ x; exact nomatch x

theorem PExpr.toVal?_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) : {o : Lvl} → (p : PExpr Δ Φ Γ τ o) → {v : Val Δ d Φ Γ τ o} →
    p.toVal? = some v → v.eval κ ρ = p.eval κ ρ
  | _, .record_mk _, _, h => by
      simp only [PExpr.toVal?, Option.some.injEq] at h; subst h; rfl
  | _, .union_mk _ _, _, h => by
      simp only [PExpr.toVal?, Option.some.injEq] at h; subst h; rfl
  | _, .array_mk _, _, h => by
      simp only [PExpr.toVal?, Option.some.injEq] at h; subst h; rfl
  | _, .list_mk _, _, h => by
      simp only [PExpr.toVal?, Option.some.injEq] at h; subst h; rfl
  | _, .data_in _ _ _, _, h => by
      simp only [PExpr.toVal?, Option.some.injEq] at h; subst h; rfl
  | _, .neu _, _, h => by simp [PExpr.toVal?] at h
  | _, .kvar _, _, h => by simp [PExpr.toVal?] at h
  | _, .lit _ _, _, h => by simp [PExpr.toVal?] at h
  | _, .enum_mk _ _, _, h => by simp [PExpr.toVal?] at h

/-! ## Binding a pure expression -/

theorem Term.bindAns_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks}
    {o o' : Lvl} {u : Usage01ω} (e : PExpr Δ Φ Γ σ o) (b : Term Δ d Φ (⟨σ, u, d⟩ :: Γ) τ js o')
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) {r : (o'' : Lvl) × Term Δ d Φ Γ τ js o''}
    (h : Term.bindAns e b = some r) :
    r.2.eval κ ρ jκ = b.eval κ (Tuple.cons (e.eval κ ρ) ρ) jκ := by
  unfold Term.bindAns at h
  split at h
  · exact Term.subst_eval (KLRen.Agree.id κ)
      (USub.Agree.cons (USub.Agree.ofRen (ULRen.Agree.idL ρ)) ⟨_, e⟩) (JRen.Agree.id jκ) b h
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, r', hr', rfl⟩ := h
    simp only [Term.eval]
    rw [Term.subst_eval (κ := κ) (κ' := Tuple.cons (v.eval κ ρ) κ) (KLRen.Agree.wk1 (b := ⟨_, .many, _, true⟩) κ (v.eval κ ρ))
      (USub.Agree.cons (USub.Agree.ofRen (ULRen.Agree.idL ρ)) _) (JRen.Agree.id jκ) b hr']
    simp only [PExpr.eval, KEnv.get_cons_head, PExpr.toVal?_eval κ ρ e hv]

theorem Term.bindRet_eval {d : Nat} {σ τ : Ty ks} {u : Usage1ω} :
    {Φ : KCtx ks} → {Γ : UCtx ks} → {js : JCtx ks} → {o o' : Lvl} →
    (t : Term Δ d Φ Γ σ [] o) → (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
    {r : (o'' : Lvl) × Term Δ d Φ Γ τ js o''} → Term.bindRet t b = some r →
    r.2.eval κ ρ jκ = b.eval κ (Tuple.cons (t.eval κ ρ PUnit.unit) ρ) jκ
  | _, _, _, _, _, .ret e, b, κ, ρ, jκ, r, h => by
      simp only [Term.bindRet] at h
      split at h
      · rename_i n hn
        simp only [Option.some.injEq] at h
        subst h
        simp only [Term.eval, Comp.eval, PExpr.toNeu?_eval κ ρ e hn]
      · exact Term.bindAns_eval e b κ ρ jκ h
  | _, _, _, _, _, .letE u' c t, b, κ, ρ, jκ, r, h => by
      simp only [Term.bindRet, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b', hb', r', hr', rfl⟩ := h
      simp only [Term.eval]
      rw [Term.bindRet_eval t b' κ _ jκ hr']
      exact Term.rename_eval (KRen.Agree.id κ)
        (URen.Agree.lift (URen.Agree.wk1 (b := ⟨_, u'.toUsage01ω, d⟩) ρ (c.eval κ ρ)) _ _)
        (JRen.Agree.id jκ) b hb'
  | _, _, _, _, _, .letV u' v t, b, κ, ρ, jκ, r, h => by
      simp only [Term.bindRet, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b', hb', r', hr', rfl⟩ := h
      simp only [Term.eval]
      rw [Term.bindRet_eval t b' _ ρ jκ hr']
      exact Term.rename_eval (KRen.Agree.wk1 (b := ⟨_, u', _, true⟩) κ (v.eval κ ρ))
        (URen.Agree.id _) (JRen.Agree.id jκ) b hb'
  | _, _, _, _, _, .record_casesOn us n t, b, κ, ρ, jκ, r, h => by
      simp only [Term.bindRet, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b', hb', r', hr', rfl⟩ := h
      simp only [Term.eval]
      rw [Term.bindRet_eval t b' κ _ jκ hr']
      exact Term.rename_eval (KRen.Agree.id κ) (URen.Agree.lift (URen.Agree.wkN ρ _ _) _ _)
        (JRen.Agree.id jκ) b hb'
  | _, _, _, _, _, .branch br, b, κ, ρ, jκ, r, h => by
      simp only [Term.bindRet, Option.some.injEq] at h
      subst h
      simp only [Term.eval, Branch.eval]
      rw [Branch.retToJump_eval br JMap.ofNil .head κ ρ PUnit.unit _ (fun x => nomatch x)]
      simp
  | _, _, _, _, _, .jump _ _, _, _, _, _, _, h => by simp [Term.bindRet] at h

/-! ## The body at a call -/

theorem BlockFn.applyP_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks}
    {js : JCtx ks} {oa : Lvl} {f : BlockFn Δ Φ (.fn σ τ)} {κ : KEnv Δ Φ}
    {g : Ty.Den Δ (.fn σ τ)} (hs : f.Sem κ g) (a : PExpr Δ Φ Γ σ oa) (ρ : UEnv Δ Γ)
    (jκ : JEnv Δ τ js) {r : (o' : Lvl) × Term Δ d Φ Γ τ js o'} (h : f.applyP a = some r) :
    r.2.eval κ ρ jκ = g (a.eval κ ρ) := by
  unfold BlockFn.applyP at h
  split at h
  · rename_i n hn
    rw [BlockFn.applyNeu_eval hs n.2 ρ jκ h, PExpr.toNeu?_eval κ ρ a hn]
  · obtain ⟨σ', τ', hty, u, D, o, body⟩ := f
    simp only at h
    split at h
    · rename_i hst
      obtain ⟨rfl, rfl⟩ := hst
      split at h
      · rw [Term.subst_eval (KLRen.Agree.id κ) (USub.Agree.cons (u := u) (L := D)
          (USub.Agree.none κ ρ) ⟨_, a⟩) (JRen.Agree.ofNil jκ) _ h]
        exact (hs (a.eval κ ρ)).symm
      · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
        obtain ⟨v, hv, r', hr', rfl⟩ := h
        simp only [Term.eval]
        rw [Term.subst_eval (κ := κ) (κ' := Tuple.cons (v.eval κ ρ) κ) (KLRen.Agree.wk1 (b := ⟨_, .many, _, true⟩) κ (v.eval κ ρ))
          (USub.Agree.cons (USub.Agree.none _ ρ) _) (JRen.Agree.ofNil jκ) _ hr']
        simp only [PExpr.eval, KEnv.get_cons_head, PExpr.toVal?_eval κ ρ a hv]
        exact (hs (a.eval κ ρ)).symm
    · cases h


/-! ## Sharing the fields of a record built for a call -/

theorem Args.shareFirst_eval (d : Nat) {Φ : KCtx ks} {Γ : UCtx ks} (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) : {σs : List (Ty ks)} → {o : Lvl} → (as : Args Δ Φ Γ σs o) →
    {r : (τ : Ty ks) × (ℓn : Nat) × Neu Δ Φ Γ τ ℓn × (o' : Lvl) ×
      Args Δ Φ (⟨τ, Usage1ω.many.toUsage01ω, d⟩ :: Γ) σs o'} →
    Args.shareFirst d as = some r →
    r.2.2.2.2.eval κ (Tuple.cons (r.2.2.1.eval κ ρ) ρ) = as.eval κ ρ
  | _, _, .nil, _, h => by simp [Args.shareFirst] at h
  | _, _, .cons a as, r, h => by
      simp only [Args.shareFirst] at h
      split at h
      · rename_i n
        split at h
        · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
          obtain ⟨r', hr', a', ha', rfl⟩ := h
          simp only [Args.eval]
          rw [Args.shareFirst_eval d κ ρ as hr',
            PExpr.rename_eval (KRen.Agree.id κ) (URen.Agree.wk1 ρ _) _ ha']
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨as', has', rfl⟩ := h
          simp only [Args.eval, PExpr.eval, Neu.eval, UEnv.get_cons_head]
          rw [Args.rename_eval (KRen.Agree.id κ) (URen.Agree.wk1 ρ _) _ has']
      · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
        obtain ⟨r', hr', a', ha', rfl⟩ := h
        simp only [Args.eval]
        rw [Args.shareFirst_eval d κ ρ as hr',
          PExpr.rename_eval (KRen.Agree.id κ) (URen.Agree.wk1 ρ _) _ ha']

theorem Comp.shareArg?_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {ℓ : Nat}
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (c : Comp Δ d Φ Γ σ ℓ)
    {r : (τ : Ty ks) × (ℓn : Nat) × Neu Δ Φ Γ τ ℓn × (ℓ' : Nat) ×
      Comp Δ d Φ (⟨τ, Usage1ω.many.toUsage01ω, d⟩ :: Γ) σ ℓ'}
    (h : c.shareArg? = some r) :
    r.2.2.2.2.eval κ (Tuple.cons (r.2.2.1.eval κ ρ) ρ) = c.eval κ ρ := by
  unfold Comp.shareArg? at h
  split at h
  · rename_i k args _
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨r', hr', q, hq, rfl⟩ := h
    simp only [Comp.eval, PExpr.eval]
    rw [Args.shareFirst_eval d κ ρ args hr']
  · cases h

/-! ## The innermost unknown -/

theorem PExpr.isHead?_eval {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {u : Usage01ω} {ℓ : Nat}
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (v : Ty.Den Δ σ) {o : Lvl}
    (e : PExpr Δ Φ (⟨σ, u, ℓ⟩ :: Γ) σ o) {h : PLift (σ = σ)} (he : e.isHead? = some h) :
    e.eval κ (Tuple.cons v ρ) = v := by
  cases e with
  | neu n =>
      cases n with
      | var x =>
          cases x with
          | head _ => simp only [PExpr.eval, Neu.eval, UEnv.get_cons_head]
          | tail _ => simp [PExpr.isHead?, Neu.isHead?, UVar.isHead?] at he
      | data_out => simp [PExpr.isHead?, Neu.isHead?] at he
      | cond => simp [PExpr.isHead?, Neu.isHead?] at he
      | extern => simp [PExpr.isHead?, Neu.isHead?] at he
  | _ => simp [PExpr.isHead?] at he

theorem Term.retHead?_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {u : Usage01ω}
    {ℓ : Nat} {js : JCtx ks} {o : Lvl} (b : Term Δ d Φ (⟨σ, u, ℓ⟩ :: Γ) σ js o)
    {h : PLift (σ = σ)} (hb : b.retHead? = some h) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (v : Ty.Den Δ σ) (jκ : JEnv Δ σ js) : b.eval κ (Tuple.cons v ρ) jκ = v := by
  cases b with
  | ret e =>
      simp only [Term.retHead?] at hb
      simp only [Term.eval]
      exact PExpr.isHead?_eval κ ρ v e hb
  | _ => simp [Term.retHead?] at hb

end LeanScript

end
