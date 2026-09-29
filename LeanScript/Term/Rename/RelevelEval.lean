module

public import LeanScript.Term.Rename.Relevel
public import LeanScript.Term.Rename.Eval

@[expose] public section

set_option autoImplicit false

/-!
# Renamings that change levels preserve the value

`Term.relvl_eval`: when the maps agree with the environments (`ULRen.Agree`, `KLRen.Agree`,
`JRen.Agree`), a statement renamed by `Term.relvl` has the same value.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Agreement -/

/-- Two environments of unknowns agree along a renaming that may change levels. -/
def ULRen.Agree {Γ Γ' : UCtx ks} (r : ULRen Γ Γ') (ρ : UEnv Δ Γ) (ρ' : UEnv Δ Γ') : Prop :=
  ∀ {τ : Ty ks} {ℓ : Nat} (x : UVar Γ τ ℓ) (p : (ℓ' : Nat) × UVar Γ' τ ℓ'), r x = some p →
    ρ'.get p.2 = ρ.get x

/-- Two environments of known values agree along a renaming that may change levels. -/
def KLRen.Agree {Φ Φ' : KCtx ks} (r : KLRen Φ Φ') (κ : KEnv Δ Φ) (κ' : KEnv Δ Φ') : Prop :=
  ∀ {τ : Ty ks} {o : Lvl} (x : KVar Φ τ o) (p : (o' : Lvl) × KVar Φ' τ o'), r x = some p →
    κ'.get p.2 = κ.get x

theorem ULRen.Agree.lift {Γ Γ' : UCtx ks} {r : ULRen Γ Γ'} {ρ : UEnv Δ Γ} {ρ' : UEnv Δ Γ'}
    (h : ULRen.Agree r ρ ρ') (σ : Ty ks) (u : Usage01ω) (L L' : Nat) (v : Ty.Den Δ σ) :
    ULRen.Agree (ULRen.lift r σ u L L')
      (Tuple.cons v ρ : UEnv Δ (⟨σ, u, L⟩ :: Γ)) (Tuple.cons v ρ' : UEnv Δ (⟨σ, u, L'⟩ :: Γ')) := by
  intro _ _ x p hxp
  cases x with
  | head hu =>
      simp only [ULRen.lift, Option.some.injEq] at hxp
      subst hxp; simp
  | tail x =>
      simp only [ULRen.lift, Option.map_eq_some_iff] at hxp
      obtain ⟨q, hq, rfl⟩ := hxp
      simp [h x q hq]

theorem UEnv.append_setLv_cons (L : Nat) {b : UBinder ks} {bs Γ : UCtx ks}
    (vs : UEnv Δ (b :: bs)) (ρ : UEnv Δ Γ) :
    (Tuple.append (UEnv.setLv L vs) ρ : UEnv Δ (UCtx.setLv L (b :: bs) ++ Γ)) =
      (Tuple.cons vs.head (Tuple.append (UEnv.setLv L vs.tail) ρ) :
        UEnv Δ (⟨b.ty, b.use, L⟩ :: (UCtx.setLv L bs ++ Γ))) := by
  cases bs <;> rfl

theorem UEnv.append_ofDL_cons_nil (L : Nat) {t : Ty ks} {ts : List (Ty ks)} {Γ : UCtx ks}
    (v : DenList (DSig.refDen Δ) (t :: ts)) (ρ : UEnv Δ Γ) :
    (Tuple.append (UEnv.ofDL L (t :: ts) [] v) ρ : UEnv Δ (UCtx.annot L (t :: ts) [] ++ Γ)) =
      (Tuple.cons v.head (Tuple.append (UEnv.ofDL L ts [] v.tail) ρ) :
        UEnv Δ (⟨t, .many, L⟩ :: (UCtx.annot L ts [] ++ Γ))) := by
  cases ts <;> rfl

theorem UEnv.append_ofDL_cons_cons (L : Nat) {t : Ty ks} {ts : List (Ty ks)} {u : Usage01ω}
    {us : List Usage01ω} {Γ : UCtx ks} (v : DenList (DSig.refDen Δ) (t :: ts)) (ρ : UEnv Δ Γ) :
    (Tuple.append (UEnv.ofDL L (t :: ts) (u :: us) v) ρ :
        UEnv Δ (UCtx.annot L (t :: ts) (u :: us) ++ Γ)) =
      (Tuple.cons v.head (Tuple.append (UEnv.ofDL L ts us v.tail) ρ) :
        UEnv Δ (⟨t, u, L⟩ :: (UCtx.annot L ts us ++ Γ))) := by
  cases ts <;> cases us <;> rfl

theorem ULRen.Agree.liftSet {Γ Γ' : UCtx ks} {r : ULRen Γ Γ'} {ρ : UEnv Δ Γ} {ρ' : UEnv Δ Γ'}
    (h : ULRen.Agree r ρ ρ') (L' : Nat) : (bs : UCtx ks) → (vs : UEnv Δ bs) →
    ULRen.Agree (ULRen.liftSet r L' bs) (Tuple.append vs ρ) (Tuple.append (UEnv.setLv L' vs) ρ')
  | [], _ => h
  | b :: bs, vs => by
      have h2 : ULRen.Agree (ULRen.lift (ULRen.liftSet r L' bs) b.ty b.use b.lv L') _ _ :=
        ULRen.Agree.lift (ULRen.Agree.liftSet h L' bs vs.tail) b.ty b.use b.lv L' vs.head
      rw [UEnv.append_setLv_cons]
      exact h2

theorem ULRen.Agree.setLvOnly (L' : Nat) : (bs : UCtx ks) → (vs : UEnv Δ bs) →
    ULRen.Agree (ULRen.setLvOnly L' bs) vs (UEnv.setLv L' vs)
  | [], _ => by intro _ _ x; exact nomatch x
  | b :: bs, vs => by
      have h : ULRen.Agree (ULRen.lift (ULRen.setLvOnly L' bs) b.ty b.use b.lv L') _ _ :=
        ULRen.Agree.lift (ULRen.Agree.setLvOnly L' bs vs.tail) b.ty b.use b.lv L' vs.head
      rw [Tuple.cons_head_tail] at h
      exact h

theorem ULRen.Agree.liftAnnot {Γ Γ' : UCtx ks} {r : ULRen Γ Γ'} {ρ : UEnv Δ Γ}
    {ρ' : UEnv Δ Γ'} (h : ULRen.Agree r ρ ρ') (L L' : Nat) :
    (ts : List (Ty ks)) → (us : List Usage01ω) → (v : DenList (DSig.refDen Δ) ts) →
    ULRen.Agree (ULRen.liftAnnot r L L' ts us) (Tuple.append (UEnv.ofDL L ts us v) ρ)
      (Tuple.append (UEnv.ofDL L' ts us v) ρ')
  | [], _, _ => h
  | t :: ts, [], v => by
      have h2 : ULRen.Agree (ULRen.lift (ULRen.liftAnnot r L L' ts []) t .many L L') _ _ :=
        ULRen.Agree.lift (ULRen.Agree.liftAnnot h L L' ts [] v.tail) t .many L L' v.head
      rw [UEnv.append_ofDL_cons_nil, UEnv.append_ofDL_cons_nil]
      exact h2
  | t :: ts, u :: us, v => by
      have h2 : ULRen.Agree (ULRen.lift (ULRen.liftAnnot r L L' ts us) t u L L') _ _ :=
        ULRen.Agree.lift (ULRen.Agree.liftAnnot h L L' ts us v.tail) t u L L' v.head
      rw [UEnv.append_ofDL_cons_cons, UEnv.append_ofDL_cons_cons]
      exact h2

theorem KLRen.Agree.lift {Φ Φ' : KCtx ks} {r : KLRen Φ Φ'} {κ : KEnv Δ Φ} {κ' : KEnv Δ Φ'}
    (h : KLRen.Agree r κ κ') (σ : Ty ks) (u : Usage1ω) (o o' : Lvl) (v : Ty.Den Δ σ) :
    KLRen.Agree (KLRen.lift r σ u o o')
      (Tuple.cons v κ : KEnv Δ (⟨σ, u, o, true⟩ :: Φ))
      (Tuple.cons v κ' : KEnv Δ (⟨σ, u, o', true⟩ :: Φ')) := by
  intro _ _ x p hxp
  cases x with
  | head =>
      simp only [KLRen.lift, Option.some.injEq] at hxp
      subst hxp; simp
  | tail x =>
      simp only [KLRen.lift, Option.map_eq_some_iff] at hxp
      obtain ⟨q, hq, rfl⟩ := hxp
      simp [h x q hq]

theorem KLRen.Agree.closedOnly {Φ Φ' : KCtx ks} {r : KLRen Φ Φ'} {κ : KEnv Δ Φ}
    {κ' : KEnv Δ Φ'} (h : KLRen.Agree r κ κ') :
    KLRen.Agree (KLRen.closedOnly r) (KEnv.closedOnly κ) (KEnv.closedOnly κ') := by
  intro _ _ x p hxp
  simp only [KLRen.closedOnly, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hxp
  obtain ⟨q, hq, y, hy, rfl⟩ := hxp
  rw [KEnv.closedOnly_get, KEnv.closedOnly_get, KVar.mask_unmask q.2 hy, h _ q hq]

theorem Lvl.some?_eq {o : Lvl} {p : (ℓ : Nat) ×' o = some ℓ} (_ : Lvl.some? o = some p) :
    o = some p.1 := p.2

/-! ## Pure expressions -/

section Layer1
variable {Φ Φ' : KCtx ks} {Γ Γ' : UCtx ks} {rk : KLRen Φ Φ'} {ru : ULRen Γ Γ'}
  {κ : KEnv Δ Φ} {κ' : KEnv Δ Φ'} {ρ : UEnv Δ Γ} {ρ' : UEnv Δ Γ'}

mutual
theorem Neu.relvl_eval (hk : KLRen.Agree rk κ κ') (hu : ULRen.Agree ru ρ ρ') :
    {τ : Ty ks} → {ℓ : Nat} → (n : Neu Δ Φ Γ τ ℓ) → {p : (ℓ' : Nat) × Neu Δ Φ' Γ' τ ℓ'} →
    n.relvl rk ru = some p → p.2.eval κ' ρ' = n.eval κ ρ
  | _, _, .var x, _, h => by
      simp only [Neu.relvl, Option.map_eq_some_iff] at h
      obtain ⟨q, hq, rfl⟩ := h
      exact hu x q hq
  | _, _, .data_out b j n, _, h => by
      simp only [Neu.relvl, Option.map_eq_some_iff] at h
      obtain ⟨m, hm, rfl⟩ := h
      simp only [Neu.eval, Neu.relvl_eval hk hu n hm] <;> rfl
  | _, _, .cond c a b, _, h => by
      simp only [Neu.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨c', hc, a', ha, b', hb, rfl⟩ := h
      simp only [Neu.eval, Neu.relvl_eval hk hu c hc, PExpr.relvl_eval hk hu a ha,
        PExpr.relvl_eval hk hu b hb] <;> rfl
  | _, _, .extern e args _, _, h => by
      simp only [Neu.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨as', has, q, hq, rfl⟩ := h
      simp only [Neu.eval, Args.relvl_eval hk hu args has]
theorem PExpr.relvl_eval (hk : KLRen.Agree rk κ κ') (hu : ULRen.Agree ru ρ ρ') :
    {τ : Ty ks} → {o : Lvl} → (e : PExpr Δ Φ Γ τ o) → {p : (o' : Lvl) × PExpr Δ Φ' Γ' τ o'} →
    e.relvl rk ru = some p → p.2.eval κ' ρ' = e.eval κ ρ
  | _, _, .neu n, _, h => by
      simp only [PExpr.relvl, Option.map_eq_some_iff] at h
      obtain ⟨m, hm, rfl⟩ := h
      simp only [PExpr.eval, Neu.relvl_eval hk hu n hm] <;> rfl
  | _, _, .kvar k, _, h => by
      simp only [PExpr.relvl, Option.map_eq_some_iff] at h
      obtain ⟨q, hq, rfl⟩ := h
      exact hk k q hq
  | _, _, .lit _ _, _, h => by
      simp only [PExpr.relvl, Option.some.injEq] at h
      subst h; rfl
  | _, _, .enum_mk _ _, _, h => by
      simp only [PExpr.relvl, Option.some.injEq] at h
      subst h; rfl
  | _, _, .record_mk args, _, h => by
      simp only [PExpr.relvl, Option.map_eq_some_iff] at h
      obtain ⟨as', has, rfl⟩ := h
      simp only [PExpr.eval, Args.relvl_eval hk hu args has] <;> rfl
  | _, _, .union_mk ix args, _, h => by
      simp only [PExpr.relvl, Option.map_eq_some_iff] at h
      obtain ⟨as', has, rfl⟩ := h
      simp only [PExpr.eval, Args.relvl_eval hk hu args has] <;> rfl
  | _, _, .array_mk es, _, h => by
      simp only [PExpr.relvl, Option.map_eq_some_iff] at h
      obtain ⟨es', hes, rfl⟩ := h
      simp only [PExpr.eval, Elems.relvl_eval hk hu es hes] <;> rfl
  | _, _, .list_mk es, _, h => by
      simp only [PExpr.relvl, Option.map_eq_some_iff] at h
      obtain ⟨es', hes, rfl⟩ := h
      simp only [PExpr.eval, Elems.relvl_eval hk hu es hes] <;> rfl
  | _, _, .data_in b j e, _, h => by
      simp only [PExpr.relvl, Option.map_eq_some_iff] at h
      obtain ⟨e', he, rfl⟩ := h
      simp only [PExpr.eval, PExpr.relvl_eval hk hu e he]
theorem Args.relvl_eval (hk : KLRen.Agree rk κ κ') (hu : ULRen.Agree ru ρ ρ') :
    {σs : List (Ty ks)} → {o : Lvl} → (as : Args Δ Φ Γ σs o) →
    {p : (o' : Lvl) × Args Δ Φ' Γ' σs o'} → as.relvl rk ru = some p →
    p.2.eval κ' ρ' = as.eval κ ρ
  | _, _, .nil, _, h => by
      simp only [Args.relvl, Option.some.injEq] at h
      subst h; rfl
  | _, _, .cons a as, _, h => by
      simp only [Args.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨a', ha, as', has, rfl⟩ := h
      simp only [Args.eval, PExpr.relvl_eval hk hu a ha, Args.relvl_eval hk hu as has]
theorem Elems.relvl_eval (hk : KLRen.Agree rk κ κ') (hu : ULRen.Agree ru ρ ρ') :
    {t : Ty ks} → {o : Lvl} → (es : Elems Δ Φ Γ t o) → {p : (o' : Lvl) × Elems Δ Φ' Γ' t o'} →
    es.relvl rk ru = some p → p.2.eval κ' ρ' = es.eval κ ρ
  | _, _, .nil, _, h => by
      simp only [Elems.relvl, Option.some.injEq] at h
      subst h; rfl
  | _, _, .cons e es, _, h => by
      simp only [Elems.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨e', he, es', hes, rfl⟩ := h
      simp only [Elems.eval, PExpr.relvl_eval hk hu e he, Elems.relvl_eval hk hu es hes] <;> rfl
end

end Layer1

/-! ## Statements -/

mutual
theorem Val.relvl_eval : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {rk : KLRen Φ Φ'} → {ru : ULRen Γ Γ'} → {κ : KEnv Δ Φ} → {κ' : KEnv Δ Φ'} →
    {ρ : UEnv Δ Γ} → {ρ' : UEnv Δ Γ'} → KLRen.Agree rk κ κ' → ULRen.Agree ru ρ ρ' →
    {τ : Ty ks} → {o : Lvl} → (v : Val Δ D Φ Γ τ o) → {p : (o' : Lvl) × Val Δ D' Φ' Γ' τ o'} →
    v.relvl rk ru = some p → p.2.eval κ' ρ' = v.eval κ ρ
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, _, _, .lam b, _, h => by
      simp only [Val.relvl, Option.map_eq_some_iff] at h
      obtain ⟨b', hb, rfl⟩ := h
      simp only [Val.eval]
      funext x
      exact Body.relvl_eval hk hu b hb (Tuple.cons x Tuple.nil)
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, _, _, .thunk_mk b, _, h => by
      simp only [Val.relvl, Option.map_eq_some_iff] at h
      obtain ⟨b', hb, rfl⟩ := h
      simp only [Val.eval]
      rw [← Body.relvl_eval hk hu b hb Tuple.nil]; rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, _, _, .lazy_mk b, _, h => by
      simp only [Val.relvl, Option.map_eq_some_iff] at h
      obtain ⟨b', hb, rfl⟩ := h
      simp only [Val.eval]
      rw [← Body.relvl_eval hk hu b hb Tuple.nil]; rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, _, _, .record_mk args, _, h => by
      simp only [Val.relvl, Option.map_eq_some_iff] at h
      obtain ⟨as', has, rfl⟩ := h
      simp only [Val.eval, Args.relvl_eval hk hu args has] <;> rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, _, _, .union_mk ix args, _, h => by
      simp only [Val.relvl, Option.map_eq_some_iff] at h
      obtain ⟨as', has, rfl⟩ := h
      simp only [Val.eval, Args.relvl_eval hk hu args has] <;> rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, _, _, .array_mk es, _, h => by
      simp only [Val.relvl, Option.map_eq_some_iff] at h
      obtain ⟨es', hes, rfl⟩ := h
      simp only [Val.eval, Elems.relvl_eval hk hu es hes] <;> rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, _, _, .list_mk es, _, h => by
      simp only [Val.relvl, Option.map_eq_some_iff] at h
      obtain ⟨es', hes, rfl⟩ := h
      simp only [Val.eval, Elems.relvl_eval hk hu es hes] <;> rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, _, _, .data_in b j e, _, h => by
      simp only [Val.relvl, Option.map_eq_some_iff] at h
      obtain ⟨e', he, rfl⟩ := h
      simp only [Val.eval, PExpr.relvl_eval hk hu e he] <;> rfl
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ => x
theorem Body.relvl_eval : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {rk : KLRen Φ Φ'} → {ru : ULRen Γ Γ'} → {κ : KEnv Δ Φ} → {κ' : KEnv Δ Φ'} →
    {ρ : UEnv Δ Γ} → {ρ' : UEnv Δ Γ'} → KLRen.Agree rk κ κ' → ULRen.Agree ru ρ ρ' →
    {bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} → (b : Body Δ D Φ Γ bs τ o) →
    {p : (o' : Lvl) × Body Δ D' Φ' Γ' (UCtx.setLv (D' + 1) bs) τ o'} → b.relvl rk ru = some p →
    ∀ vs : UEnv Δ bs, p.2.eval κ' ρ' (UEnv.setLv (D' + 1) vs) = b.eval κ ρ vs
  | _, D', _, _, _, _, _, _, _, _, _, _, hk, _, bs, _, _, .closed t, _, h, vs => by
      simp only [Body.relvl, Option.map_eq_some_iff] at h
      obtain ⟨t', ht, rfl⟩ := h
      simp only [Body.eval]
      exact Term.relvl_eval hk.closedOnly (ULRen.Agree.setLvOnly (D' + 1) bs vs)
        JRen.Agree.nil t ht
  | _, D', _, _, _, _, _, _, _, _, _, _, hk, hu, bs, _, _, .opened t _, _, h, vs => by
      simp only [Body.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨o', t'⟩, ht, ⟨m, hm⟩, _, h⟩ := h
      simp only at hm
      subst hm
      split at h
      · simp only [Option.pure_def, Option.some.injEq] at h
        subst h
        simp only [Body.eval]
        exact Term.relvl_eval hk (hu.liftSet (D' + 1) bs vs) JRen.Agree.nil t ht
      · cases h
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ => x
theorem Comp.relvl_eval : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {rk : KLRen Φ Φ'} → {ru : ULRen Γ Γ'} → {κ : KEnv Δ Φ} → {κ' : KEnv Δ Φ'} →
    {ρ : UEnv Δ Γ} → {ρ' : UEnv Δ Γ'} → KLRen.Agree rk κ κ' → ULRen.Agree ru ρ ρ' →
    {τ : Ty ks} → {ℓ : Nat} → (c : Comp Δ D Φ Γ τ ℓ) → {p : (ℓ' : Nat) × Comp Δ D' Φ' Γ' τ ℓ'} →
    c.relvl rk ru = some p → p.2.eval κ' ρ' = c.eval κ ρ
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, _, _, .app f a _, _, h => by
      simp only [Comp.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨f', hf, a', ha, q, hq, rfl⟩ := h
      simp only [Comp.eval, PExpr.relvl_eval hk hu f hf, PExpr.relvl_eval hk hu a ha] <;> rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, _, _, .share n, _, h => by
      simp only [Comp.relvl, Option.map_eq_some_iff] at h
      obtain ⟨n', hn, rfl⟩ := h
      simp only [Comp.eval, Neu.relvl_eval hk hu n hn] <;> rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, _, _, .nat_rec n z s _, _, h => by
      simp only [Comp.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨n', hn, z', hz, s', hs, q, hq, rfl⟩ := h
      simp only [Comp.eval]
      rw [PExpr.relvl_eval hk hu n hn, PExpr.relvl_eval hk hu z hz]
      congr 1
      funext k acc
      exact Body.relvl_eval hk hu s hs (Tuple.cons acc (Tuple.cons k Tuple.nil))
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, _, _, .array_foldl a z s _, _, h => by
      simp only [Comp.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨a', ha, z', hz, s', hs, q, hq, rfl⟩ := h
      simp only [Comp.eval]
      rw [PExpr.relvl_eval hk hu a ha, PExpr.relvl_eval hk hu z hz]
      congr 1
      funext acc x
      exact Body.relvl_eval hk hu s hs (Tuple.cons x (Tuple.cons acc Tuple.nil))
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, _, _, .data_rec b ρt us brs j e _, _, h => by
      simp only [Comp.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨brs', hbrs, e', he, q, hq, rfl⟩ := h
      simp only [Comp.eval]
      rw [PExpr.relvl_eval hk hu e he]
      congr 1
      funext i x
      exact Body.relvl_eval hk hu (brs i) (Fin.optAll_eq_some hbrs i) (Tuple.cons x Tuple.nil)
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, _, _, .data_brec b ρt k us brs j e _, _, h => by
      simp only [Comp.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨brs', hbrs, e', he, q, hq, rfl⟩ := h
      simp only [Comp.eval]
      rw [PExpr.relvl_eval hk hu e he]
      congr 1
      funext i x
      exact Body.relvl_eval hk hu (brs i) (Fin.optAll_eq_some hbrs i) (Tuple.cons x Tuple.nil)
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, _, _, .thunk_force e, _, h => by
      simp only [Comp.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨⟨o', e'⟩, he, ⟨m, hm⟩, _, rfl⟩ := h
      simp only at hm
      subst hm
      simp only [Comp.eval]
      rw [PExpr.relvl_eval hk hu e he]
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, _, _, .lazy_force e, _, h => by
      simp only [Comp.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨⟨o', e'⟩, he, ⟨m, hm⟩, _, rfl⟩ := h
      simp only at hm
      subst hm
      simp only [Comp.eval]
      rw [PExpr.relvl_eval hk hu e he]
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ => x
theorem Term.relvl_eval : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {js js' : JCtx ks} → {τ : Ty ks} → {rk : KLRen Φ Φ'} → {ru : ULRen Γ Γ'} →
    {rj : JRen js js'} → {κ : KEnv Δ Φ} → {κ' : KEnv Δ Φ'} → {ρ : UEnv Δ Γ} →
    {ρ' : UEnv Δ Γ'} → {jκ : JEnv Δ τ js} → {jκ' : JEnv Δ τ js'} →
    KLRen.Agree rk κ κ' → ULRen.Agree ru ρ ρ' → JRen.Agree rj jκ jκ' →
    {o : Lvl} → (t : Term Δ D Φ Γ τ js o) → {p : (o' : Lvl) × Term Δ D' Φ' Γ' τ js' o'} →
    t.relvl rk ru rj = some p → p.2.eval κ' ρ' jκ' = t.eval κ ρ jκ
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, _, _, .ret e, _, h => by
      simp only [Term.relvl, Option.map_eq_some_iff] at h
      obtain ⟨e', he, rfl⟩ := h
      simp only [Term.eval, PExpr.relvl_eval hk hu e he] <;> rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, hj, _, .letV u v b, _, h => by
      simp only [Term.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨v', hv, b', hb, rfl⟩ := h
      simp only [Term.eval, Val.relvl_eval hk hu v hv]
      exact Term.relvl_eval (hk.lift _ _ _ _ _) hu hj b hb
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, hj, _, .letE u c b, _, h => by
      simp only [Term.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨c', hc, b', hb, rfl⟩ := h
      simp only [Term.eval, Comp.relvl_eval hk hu c hc]
      exact Term.relvl_eval hk (hu.lift _ _ _ _ _) hj b hb
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, hj, _,
      .record_casesOn us n b, _, h => by
      simp only [Term.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨n', hn, b', hb, rfl⟩ := h
      simp only [Term.eval, Neu.relvl_eval hk hu n hn]
      exact Term.relvl_eval hk (hu.liftAnnot _ _ _ _ _) hj b hb
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, hj, _, .branch br, _, h => by
      simp only [Term.relvl, Option.map_eq_some_iff] at h
      obtain ⟨br', hbr, rfl⟩ := h
      simp only [Term.eval]
      exact Branch.relvl_eval hk hu hj br hbr
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, hj, _, .jump j e, _, h => by
      simp only [Term.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨j', hj', e', he, rfl⟩ := h
      simp only [Term.eval, PExpr.relvl_eval hk hu e he, hj j j' hj'] <;> rfl
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ => x
theorem Branch.relvl_eval : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {js js' : JCtx ks} → {τ : Ty ks} → {rk : KLRen Φ Φ'} → {ru : ULRen Γ Γ'} →
    {rj : JRen js js'} → {κ : KEnv Δ Φ} → {κ' : KEnv Δ Φ'} → {ρ : UEnv Δ Γ} →
    {ρ' : UEnv Δ Γ'} → {jκ : JEnv Δ τ js} → {jκ' : JEnv Δ τ js'} →
    KLRen.Agree rk κ κ' → ULRen.Agree ru ρ ρ' → JRen.Agree rj jκ jκ' →
    {ℓ : Nat} → (br : Branch Δ D Φ Γ τ js ℓ) → {p : (ℓ' : Nat) × Branch Δ D' Φ' Γ' τ js' ℓ'} →
    br.relvl rk ru rj = some p → p.2.eval κ' ρ' jκ' = br.eval κ ρ jκ
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, hj, _, .ite c t e, _, h => by
      simp only [Branch.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨c', hc, t', ht, e', he, rfl⟩ := h
      simp only [Branch.eval, Neu.relvl_eval hk hu c hc, Term.relvl_eval hk hu hj t ht,
        Term.relvl_eval hk hu hj e he]
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, hj, _, .enum_casesOn e bs, _, h => by
      simp only [Branch.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨e', he, bs', hbs, rfl⟩ := h
      simp only [Branch.eval]
      rw [Neu.relvl_eval hk hu e he]
      exact Term.relvl_eval hk hu hj _ (Fin.optAll_eq_some hbs _)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, hj, _, .union_casesOn e bs, _, h => by
      simp only [Branch.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨e', he, bs', hbs, rfl⟩ := h
      simp only [Branch.eval, Neu.relvl_eval hk hu e he]
      exact Branches.relvl_eval hk hu hj bs hbs _
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, hj, _,
      .join σ u uₓ body main, _, h => by
      simp only [Branch.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨body', hbody, main', hmain, rfl⟩ := h
      simp only [Branch.eval]
      have hf := funext fun v => Term.relvl_eval hk (hu.lift _ _ _ _ v) hj body hbody
      rw [hf]
      exact Branch.relvl_eval hk hu (hj.lift _ _) main hmain
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ => x
theorem Branches.relvl_eval : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {js js' : JCtx ks} → {τ : Ty ks} → {rk : KLRen Φ Φ'} → {ru : ULRen Γ Γ'} →
    {rj : JRen js js'} → {κ : KEnv Δ Φ} → {κ' : KEnv Δ Φ'} → {ρ : UEnv Δ Γ} →
    {ρ' : UEnv Δ Γ'} → {jκ : JEnv Δ τ js} → {jκ' : JEnv Δ τ js'} →
    KLRen.Agree rk κ κ' → ULRen.Agree ru ρ ρ' → JRen.Agree rj jκ jκ' →
    {bs : List Bool} → {cs : Ctors ks bs} → {o : Lvl} → (br : Branches Δ D Φ Γ cs τ js o) →
    {p : (o' : Lvl) × Branches Δ D' Φ' Γ' cs τ js' o'} → br.relvl rk ru rj = some p →
    ∀ x, p.2.eval κ' ρ' jκ' x = br.eval κ ρ jκ x
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, hj, _, _, _,
      .two us₁ us₂ b₁ b₂, _, h, x => by
      simp only [Branches.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨b₁', h₁, b₂', h₂, rfl⟩ := h
      simp only [Branches.eval]
      congr 1
      · funext v; exact Term.relvl_eval hk (hu.liftAnnot _ _ _ _ _) hj b₁ h₁
      · funext v; exact Term.relvl_eval hk (hu.liftAnnot _ _ _ _ _) hj b₂ h₂
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, hj, _, _, _,
      .cons us b bs, _, h, x => by
      simp only [Branches.relvl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨b', hb, bs', hbs, rfl⟩ := h
      simp only [Branches.eval]
      congr 1
      · funext v; exact Term.relvl_eval hk (hu.liftAnnot _ _ _ _ _) hj b hb
      · funext r; exact Branches.relvl_eval hk hu hj bs hbs r
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ => x
end

end LeanScript

end
