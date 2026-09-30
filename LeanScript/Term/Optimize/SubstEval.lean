module

public import LeanScript.Term.Optimize.Subst
public import LeanScript.Term.Optimize.InlineBlockEval

@[expose] public section

set_option autoImplicit false

/-!
# Substitution preserves the value

`Term.subst_eval`: when the known values agree along the renaming (`KLRen.Agree`) and every
pure expression the substitution gives evaluates to the value of the unknown it replaces
(`USub.Agree`), the substituted statement has the same value.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Agreement -/

/-- Every pure expression given by `s` has the value of the unknown it replaces. -/
def USub.Agree {Φ' : KCtx ks} {Γ Γ' : UCtx ks} (s : USub Δ Φ' Γ Γ') (κ' : KEnv Δ Φ')
    (ρ : UEnv Δ Γ) (ρ' : UEnv Δ Γ') : Prop :=
  ∀ {τ : Ty ks} {ℓ : Nat} (x : UVar Γ τ ℓ) (p : (o : Lvl) × PExpr Δ Φ' Γ' τ o), s x = some p →
    p.2.eval κ' ρ' = ρ.get x

section Agree
variable {Φ' : KCtx ks} {Γ Γ' : UCtx ks} {κ' : KEnv Δ Φ'} {ρ : UEnv Δ Γ} {ρ' : UEnv Δ Γ'}

theorem USub.Agree.ofRen {r : ULRen Γ Γ'} (h : ULRen.Agree r ρ ρ') :
    USub.Agree (USub.ofRen (Δ := Δ) (Φ' := Φ') r) κ' ρ ρ' := by
  intro _ _ x p hp
  simp only [USub.ofRen, Option.map_eq_some_iff] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact h x q hq

theorem USub.Agree.wkU {s : USub Δ Φ' Γ Γ'} (h : USub.Agree s κ' ρ ρ') (b : UBinder ks)
    (v : Ty.Den Δ b.ty) : USub.Agree (s.wkU b) κ' ρ (Tuple.cons v ρ' : UEnv Δ (b :: Γ')) := by
  intro _ _ x p hp
  simp only [USub.wkU, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
  obtain ⟨q, hq, e, he, rfl⟩ := hp
  rw [PExpr.rename_eval (KRen.Agree.id κ') (URen.Agree.wk1 ρ' v) q.2 he]
  exact h x q hq

theorem USub.Agree.wkK {s : USub Δ Φ' Γ Γ'} (h : USub.Agree s κ' ρ ρ') (b : KBinder ks)
    (v : Ty.Den Δ b.ty) : USub.Agree (s.wkK b) (Tuple.cons v κ' : KEnv Δ (b :: Φ')) ρ ρ' := by
  intro _ _ x p hp
  simp only [USub.wkK, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
  obtain ⟨q, hq, e, he, rfl⟩ := hp
  rw [PExpr.rename_eval (KRen.Agree.wk1 κ' v) (URen.Agree.id ρ') q.2 he]
  exact h x q hq

theorem USub.Agree.lift {s : USub Δ Φ' Γ Γ'} (h : USub.Agree s κ' ρ ρ') (σ : Ty ks)
    (u : Usage01ω) (L L' : Nat) (v : Ty.Den Δ σ) :
    USub.Agree (USub.lift s σ u L L')  κ'
      (Tuple.cons v ρ : UEnv Δ (⟨σ, u, L⟩ :: Γ)) (Tuple.cons v ρ' : UEnv Δ (⟨σ, u, L'⟩ :: Γ')) := by
  intro _ _ x p hp
  cases x with
  | head hu =>
      simp only [USub.lift, Option.some.injEq] at hp
      subst hp; simp [PExpr.eval, Neu.eval]
  | tail x =>
      simp only [USub.lift] at hp
      rw [UEnv.get_cons_tail]
      exact (h.wkU _ v) x p hp

theorem USub.Agree.liftSet {s : USub Δ Φ' Γ Γ'} (h : USub.Agree s κ' ρ ρ') (L' : Nat) :
    (bs : UCtx ks) → (vs : UEnv Δ bs) →
    USub.Agree (USub.liftSet s L' bs) κ' (Tuple.append vs ρ) (Tuple.append (UEnv.setLv L' vs) ρ')
  | [], _ => h
  | b :: bs, vs => by
      have h2 : USub.Agree (USub.lift (USub.liftSet s L' bs) b.ty b.use b.lv L') κ' _ _ :=
        USub.Agree.lift (USub.Agree.liftSet h L' bs vs.tail) b.ty b.use b.lv L' vs.head
      rw [UEnv.append_setLv_cons]
      exact h2

theorem USub.Agree.liftAnnot {s : USub Δ Φ' Γ Γ'} (h : USub.Agree s κ' ρ ρ') (L L' : Nat) :
    (ts : List (Ty ks)) → (us : List Usage01ω) → (v : DenList (DSig.refDen Δ) ts) →
    USub.Agree (USub.liftAnnot s L L' ts us) κ' (Tuple.append (UEnv.ofDL L ts us v) ρ)
      (Tuple.append (UEnv.ofDL L' ts us v) ρ')
  | [], _, _ => h
  | t :: ts, [], v => by
      have h2 : USub.Agree (USub.lift (USub.liftAnnot s L L' ts []) t .many L L') κ' _ _ :=
        USub.Agree.lift (USub.Agree.liftAnnot h L L' ts [] v.tail) t .many L L' v.head
      rw [UEnv.append_ofDL_cons_nil, UEnv.append_ofDL_cons_nil]
      exact h2
  | t :: ts, u :: us, v => by
      have h2 : USub.Agree (USub.lift (USub.liftAnnot s L L' ts us) t u L L') κ' _ _ :=
        USub.Agree.lift (USub.Agree.liftAnnot h L L' ts us v.tail) t u L L' v.head
      rw [UEnv.append_ofDL_cons_cons, UEnv.append_ofDL_cons_cons]
      exact h2

theorem USub.Agree.cons {s : USub Δ Φ' Γ Γ'} (h : USub.Agree s κ' ρ ρ') {σ : Ty ks}
    {u : Usage01ω} {L : Nat} (a : (o : Lvl) × PExpr Δ Φ' Γ' σ o) :
    USub.Agree (USub.cons (u := u) (L := L) a s) κ'
      (Tuple.cons (a.2.eval κ' ρ') ρ : UEnv Δ (⟨σ, u, L⟩ :: Γ)) ρ' := by
  intro _ _ x p hp
  cases x with
  | head hu =>
      simp only [USub.cons, Option.some.injEq] at hp
      subst hp; simp
  | tail x =>
      simp only [USub.cons] at hp
      rw [UEnv.get_cons_tail]
      exact h x p hp

theorem USub.Agree.consOpt {s : USub Δ Φ' Γ Γ'} (h : USub.Agree s κ' ρ ρ') {σ : Ty ks}
    {u : Usage01ω} {L : Nat} (a : Option ((o : Lvl) × PExpr Δ Φ' Γ' σ o)) (v : Ty.Den Δ σ)
    (ha : ∀ p, a = some p → p.2.eval κ' ρ' = v) :
    USub.Agree (USub.consOpt (u := u) (L := L) a s) κ' (Tuple.cons v ρ : UEnv Δ (⟨σ, u, L⟩ :: Γ)) ρ' := by
  intro _ _ x p hp
  cases x with
  | head hu =>
      simp only [USub.consOpt] at hp
      rw [UEnv.get_cons_head]
      exact ha p hp
  | tail x =>
      simp only [USub.consOpt] at hp
      rw [UEnv.get_cons_tail]
      exact h x p hp

theorem USub.Agree.cheapOnly {s : USub Δ Φ' Γ Γ'} (h : USub.Agree s κ' ρ ρ') :
    USub.Agree s.cheapOnly κ' ρ ρ' := by
  intro _ _ x p hp
  simp only [USub.cheapOnly, Option.bind_eq_some_iff] at hp
  obtain ⟨q, hq, h2⟩ := hp
  split at h2
  · simp only [Option.some.injEq] at h2
    subst h2
    exact h x _ hq
  · cases h2

theorem USub.Agree.ofArgs {s : USub Δ Φ' Γ Γ'} (h : USub.Agree s κ' ρ ρ') (L : Nat) :
    (ts : List (Ty ks)) → (us : List Usage01ω) → {o : Lvl} → (as : Args Δ Φ' Γ' ts o) →
    USub.Agree (USub.ofArgs s L ts us as) κ' (Tuple.append (UEnv.ofDL L ts us (as.eval κ' ρ')) ρ) ρ'
  | [], _, _, .nil => h
  | t :: ts, [], _, .cons a as => by
      intro x p hp
      have h2 := USub.Agree.consOpt (u := .many) (L := L) (USub.Agree.ofArgs h L ts [] as) _
        (a.eval κ' ρ') (by intro q hq; split at hq <;> cases hq; rfl) x p hp
      rw [UEnv.append_ofDL_cons_nil]
      simp only [Args.eval, Tuple.head_cons, Tuple.tail_cons]
      exact h2
  | t :: ts, u :: us, _, .cons a as => by
      intro x p hp
      have h2 := USub.Agree.consOpt (u := u) (L := L) (USub.Agree.ofArgs h L ts us as) _
        (a.eval κ' ρ') (by intro q hq; split at hq <;> cases hq; rfl) x p hp
      rw [UEnv.append_ofDL_cons_cons]
      simp only [Args.eval, Tuple.head_cons, Tuple.tail_cons]
      exact h2

end Agree

theorem Fields.toDL_ofDL {E : Ref ks → Type} : (fs : Fields ks) → (v : DenList E fs.toList) →
    Fields.toDL fs (Fields.ofDL fs v) = v
  | .one _, _ => rfl
  | .cons _ fs, v => by
      simp only [Fields.toDL, Fields.ofDL, Fields.toDL_ofDL fs v.tail]
      exact Tuple.cons_head_tail v

theorem PExpr.recordArgs?_eval {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} {fs : Fields ks}
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : {o : Lvl} → (p : PExpr Δ Φ Γ (.record t fs) o) →
    {as : (o' : Lvl) × Args Δ Φ Γ (t :: fs.toList) o'} → p.recordArgs? = some as →
    Tuple.cons (p.eval κ ρ).1 (Fields.toDL fs (p.eval κ ρ).2) = as.2.eval κ ρ
  | _, .record_mk args, as, h => by
      simp only [PExpr.recordArgs?, Option.some.injEq] at h
      subst h
      simp only [PExpr.eval, Fields.toDL_ofDL]
      exact Tuple.cons_head_tail _
  | _, .neu _, _, h => by simp [PExpr.recordArgs?] at h
  | _, .kvar _, _, h => by simp [PExpr.recordArgs?] at h

/-! ## Pure expressions -/

section Layer1
variable {Φ Φ' : KCtx ks} {Γ Γ' : UCtx ks} {rk : KLRen Φ Φ'} {s : USub Δ Φ' Γ Γ'}
  {κ : KEnv Δ Φ} {κ' : KEnv Δ Φ'} {ρ : UEnv Δ Γ} {ρ' : UEnv Δ Γ'}

mutual
theorem Neu.subst_eval (hk : KLRen.Agree rk κ κ') (hs : USub.Agree s κ' ρ ρ') :
    {τ : Ty ks} → {ℓ : Nat} → (n : Neu Δ Φ Γ τ ℓ) → {p : (o : Lvl) × PExpr Δ Φ' Γ' τ o} →
    n.subst rk s = some p → p.2.eval κ' ρ' = n.eval κ ρ
  | _, _, .var x, _, h => by
      simp only [Neu.subst] at h
      exact hs x _ h
  | _, _, .data_out b j n, _, h => by
      simp only [Neu.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨q, hq, m, hm, rfl⟩ := h
      simp only [PExpr.eval, Neu.eval, PExpr.toNeu?_eval κ' ρ' q.2 hm, Neu.subst_eval hk hs n hq]
  | _, _, .cond c a b, _, h => by
      simp only [Neu.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨q, hq, m, hm, a', ha, b', hb, rfl⟩ := h
      simp only [PExpr.eval, Neu.eval, PExpr.toNeu?_eval κ' ρ' q.2 hm, Neu.subst_eval hk hs c hq,
        PExpr.subst_eval hk hs a ha, PExpr.subst_eval hk hs b hb]
  | _, _, .extern e args _, _, h => by
      simp only [Neu.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨as', has, q, hq, rfl⟩ := h
      simp only [PExpr.eval, Neu.eval, Args.subst_eval hk hs args has]
theorem PExpr.subst_eval (hk : KLRen.Agree rk κ κ') (hs : USub.Agree s κ' ρ ρ') :
    {τ : Ty ks} → {o : Lvl} → (e : PExpr Δ Φ Γ τ o) → {p : (o' : Lvl) × PExpr Δ Φ' Γ' τ o'} →
    e.subst rk s = some p → p.2.eval κ' ρ' = e.eval κ ρ
  | _, _, .neu n, _, h => by
      simp only [PExpr.subst] at h
      simp only [PExpr.eval, Neu.subst_eval hk hs n h]
  | _, _, .kvar k, _, h => by
      simp only [PExpr.subst, Option.map_eq_some_iff] at h
      obtain ⟨q, hq, rfl⟩ := h
      exact hk k q hq
  | _, _, .lit _ _, _, h => by
      simp only [PExpr.subst, Option.some.injEq] at h
      subst h; rfl
  | _, _, .enum_mk _ _, _, h => by
      simp only [PExpr.subst, Option.some.injEq] at h
      subst h; rfl
  | _, _, .record_mk args, _, h => by
      simp only [PExpr.subst, Option.map_eq_some_iff] at h
      obtain ⟨as', has, rfl⟩ := h
      simp only [PExpr.eval, Args.subst_eval hk hs args has] <;> rfl
  | _, _, .union_mk ix args, _, h => by
      simp only [PExpr.subst, Option.map_eq_some_iff] at h
      obtain ⟨as', has, rfl⟩ := h
      simp only [PExpr.eval, Args.subst_eval hk hs args has] <;> rfl
  | _, _, .array_mk es, _, h => by
      simp only [PExpr.subst, Option.map_eq_some_iff] at h
      obtain ⟨es', hes, rfl⟩ := h
      simp only [PExpr.eval, Elems.subst_eval hk hs es hes] <;> rfl
  | _, _, .list_mk es, _, h => by
      simp only [PExpr.subst, Option.map_eq_some_iff] at h
      obtain ⟨es', hes, rfl⟩ := h
      simp only [PExpr.eval, Elems.subst_eval hk hs es hes] <;> rfl
  | _, _, .data_in b j e, _, h => by
      simp only [PExpr.subst, Option.map_eq_some_iff] at h
      obtain ⟨e', he, rfl⟩ := h
      simp only [PExpr.eval, PExpr.subst_eval hk hs e he]
theorem Args.subst_eval (hk : KLRen.Agree rk κ κ') (hs : USub.Agree s κ' ρ ρ') :
    {σs : List (Ty ks)} → {o : Lvl} → (as : Args Δ Φ Γ σs o) →
    {p : (o' : Lvl) × Args Δ Φ' Γ' σs o'} → as.subst rk s = some p →
    p.2.eval κ' ρ' = as.eval κ ρ
  | _, _, .nil, _, h => by
      simp only [Args.subst, Option.some.injEq] at h
      subst h; rfl
  | _, _, .cons a as, _, h => by
      simp only [Args.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨a', ha, as', has, rfl⟩ := h
      simp only [Args.eval, PExpr.subst_eval hk hs a ha, Args.subst_eval hk hs as has]
theorem Elems.subst_eval (hk : KLRen.Agree rk κ κ') (hs : USub.Agree s κ' ρ ρ') :
    {t : Ty ks} → {o : Lvl} → (es : Elems Δ Φ Γ t o) → {p : (o' : Lvl) × Elems Δ Φ' Γ' t o'} →
    es.subst rk s = some p → p.2.eval κ' ρ' = es.eval κ ρ
  | _, _, .nil, _, h => by
      simp only [Elems.subst, Option.some.injEq] at h
      subst h; rfl
  | _, _, .cons e es, _, h => by
      simp only [Elems.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨e', he, es', hes, rfl⟩ := h
      simp only [Elems.eval, PExpr.subst_eval hk hs e he, Elems.subst_eval hk hs es hes] <;> rfl
end

theorem Neu.substN_eval (hk : KLRen.Agree rk κ κ') (hs : USub.Agree s κ' ρ ρ') {τ : Ty ks}
    {ℓ : Nat} (n : Neu Δ Φ Γ τ ℓ) {m : (ℓ' : Nat) × Neu Δ Φ' Γ' τ ℓ'}
    (h : n.substN rk s = some m) : m.2.eval κ' ρ' = n.eval κ ρ := by
  simp only [Neu.substN, Option.bind_eq_some_iff] at h
  obtain ⟨p, hp, hm⟩ := h
  rw [PExpr.toNeu?_eval κ' ρ' p.2 hm, Neu.subst_eval hk hs n hp]

end Layer1

theorem PExpr.enumLit?_eval {Φ : KCtx ks} {Γ : UCtx ks} {e : LeanEnumSchema} (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) : {o : Lvl} → (p : PExpr Δ Φ Γ (.enum e) o) → {i : Fin e.nOfConstructors} →
    p.enumLit? = some i → p.eval κ ρ = i
  | _, .enum_mk _ _, _, h => by
      simp only [PExpr.enumLit?, Option.some.injEq] at h
      subst h; rfl
  | _, .neu _, _, h => by simp [PExpr.enumLit?] at h
  | _, .kvar _, _, h => by simp [PExpr.enumLit?] at h

theorem Term.asBranch?_eval {D : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    {o : Lvl} → (t : Term Δ D Φ Γ τ js o) → {b : (ℓ : Nat) × Branch Δ D Φ Γ τ js ℓ} →
    t.asBranch? = some b → t.eval κ ρ jκ = b.2.eval κ ρ jκ
  | _, .branch _, _, h => by
      simp only [Term.asBranch?, Option.some.injEq] at h
      subst h; rfl
  | _, .ret _, _, h => by simp [Term.asBranch?] at h
  | _, .letV _ _ _, _, h => by simp [Term.asBranch?] at h
  | _, .letE _ _ _, _, h => by simp [Term.asBranch?] at h
  | _, .record_casesOn _ _ _, _, h => by simp [Term.asBranch?] at h
  | _, .jump _ _, _, h => by simp [Term.asBranch?] at h

theorem Term.asJump?_eval {D : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    {o : Lvl} → (t : Term Δ D Φ Γ τ js o) →
    {r : (σ : Ty ks) × JVar js σ × (o' : Lvl) × PExpr Δ Φ Γ σ o'} →
    t.asJump? = some r → t.eval κ ρ jκ = jκ.get r.2.1 (r.2.2.2.eval κ ρ)
  | _, .jump _ _, _, h => by
      simp only [Term.asJump?, Option.some.injEq] at h
      subst h; rfl
  | _, .ret _, _, h => by simp [Term.asJump?] at h
  | _, .letV _ _ _, _, h => by simp [Term.asJump?] at h
  | _, .letE _ _ _, _, h => by simp [Term.asJump?] at h
  | _, .record_casesOn _ _ _, _, h => by simp [Term.asJump?] at h
  | _, .branch _, _, h => by simp [Term.asJump?] at h

theorem JVar.split_inl_get {σ τ' τ : Ty ks} {u : Usage1ω} {js : JCtx ks} (jκ : JEnv Δ τ js)
    (f : Ty.Den Δ σ → Ty.Den Δ τ) :
    (j : JVar (⟨σ, u⟩ :: js) τ') → {h : PLift (τ' = σ)} → j.split = .inl h →
    ∀ v, JEnv.get (Tuple.cons f jκ : JEnv Δ τ (⟨σ, u⟩ :: js)) j v = f (h.down ▸ v)
  | .head, _, _, _ => by simp
  | .tail _, _, h, _ => by simp [JVar.split] at h

theorem JVar.split_inr_get {σ τ' τ : Ty ks} {u : Usage1ω} {js : JCtx ks} (jκ : JEnv Δ τ js)
    (f : Ty.Den Δ σ → Ty.Den Δ τ) :
    (j : JVar (⟨σ, u⟩ :: js) τ') → {j' : JVar js τ'} → j.split = .inr j' →
    JEnv.get (Tuple.cons f jκ : JEnv Δ τ (⟨σ, u⟩ :: js)) j = jκ.get j'
  | .head, _, h => by simp [JVar.split] at h
  | .tail _, _, h => by
      simp only [JVar.split, Sum.inr.injEq] at h
      subst h; simp

theorem PExpr.eval_cast {Φ : KCtx ks} {Γ : UCtx ks} {τ σ : Ty ks} {o : Lvl} (h : τ = σ)
    (a : PExpr Δ Φ Γ τ o) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (h ▸ a : PExpr Δ Φ Γ σ o).eval κ ρ = h ▸ a.eval κ ρ := by
  subst h; rfl

/-! ## Statements -/

mutual
theorem Val.subst_eval : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {rk : KLRen Φ Φ'} → {s : USub Δ Φ' Γ Γ'} → {κ : KEnv Δ Φ} → {κ' : KEnv Δ Φ'} →
    {ρ : UEnv Δ Γ} → {ρ' : UEnv Δ Γ'} → KLRen.Agree rk κ κ' → USub.Agree s κ' ρ ρ' →
    {τ : Ty ks} → {o : Lvl} → (v : Val Δ D Φ Γ τ o) → {p : (o' : Lvl) × Val Δ D' Φ' Γ' τ o'} →
    v.subst rk s = some p → p.2.eval κ' ρ' = v.eval κ ρ
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hs, _, _, .lam b, _, h => by
      simp only [Val.subst, Option.map_eq_some_iff] at h
      obtain ⟨b', hb, rfl⟩ := h
      simp only [Val.eval]
      funext x
      exact Body.subst_eval hk hs b hb (Tuple.cons x Tuple.nil)
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hs, _, _, .thunk_mk b, _, h => by
      simp only [Val.subst, Option.map_eq_some_iff] at h
      obtain ⟨b', hb, rfl⟩ := h
      simp only [Val.eval]
      rw [← Body.subst_eval hk hs b hb Tuple.nil]; rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hs, _, _, .lazy_mk b, _, h => by
      simp only [Val.subst, Option.map_eq_some_iff] at h
      obtain ⟨b', hb, rfl⟩ := h
      simp only [Val.eval]
      rw [← Body.subst_eval hk hs b hb Tuple.nil]; rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hs, _, _, .record_mk args, _, h => by
      simp only [Val.subst, Option.map_eq_some_iff] at h
      obtain ⟨as', has, rfl⟩ := h
      simp only [Val.eval, Args.subst_eval hk hs args has] <;> rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hs, _, _, .union_mk ix args, _, h => by
      simp only [Val.subst, Option.map_eq_some_iff] at h
      obtain ⟨as', has, rfl⟩ := h
      simp only [Val.eval, Args.subst_eval hk hs args has] <;> rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hs, _, _, .array_mk es, _, h => by
      simp only [Val.subst, Option.map_eq_some_iff] at h
      obtain ⟨es', hes, rfl⟩ := h
      simp only [Val.eval, Elems.subst_eval hk hs es hes] <;> rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hs, _, _, .list_mk es, _, h => by
      simp only [Val.subst, Option.map_eq_some_iff] at h
      obtain ⟨es', hes, rfl⟩ := h
      simp only [Val.eval, Elems.subst_eval hk hs es hes] <;> rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hs, _, _, .data_in b j e, _, h => by
      simp only [Val.subst, Option.map_eq_some_iff] at h
      obtain ⟨e', he, rfl⟩ := h
      simp only [Val.eval, PExpr.subst_eval hk hs e he] <;> rfl
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ => x
theorem Body.subst_eval : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {rk : KLRen Φ Φ'} → {s : USub Δ Φ' Γ Γ'} → {κ : KEnv Δ Φ} → {κ' : KEnv Δ Φ'} →
    {ρ : UEnv Δ Γ} → {ρ' : UEnv Δ Γ'} → KLRen.Agree rk κ κ' → USub.Agree s κ' ρ ρ' →
    {bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} → (b : Body Δ D Φ Γ bs τ o) →
    {p : (o' : Lvl) × Body Δ D' Φ' Γ' (UCtx.setLv (D' + 1) bs) τ o'} → b.subst rk s = some p →
    ∀ vs : UEnv Δ bs, p.2.eval κ' ρ' (UEnv.setLv (D' + 1) vs) = b.eval κ ρ vs
  | _, D', _, _, _, _, _, _, _, _, _, _, hk, _, bs, _, _, .closed t, _, h, vs => by
      simp only [Body.subst, Option.map_eq_some_iff] at h
      obtain ⟨t', ht, rfl⟩ := h
      simp only [Body.eval]
      exact Term.relvl_eval hk.closedOnly (ULRen.Agree.setLvOnly (D' + 1) bs vs)
        JRen.Agree.nil t ht
  | _, D', _, _, _, _, _, _, _, _, _, _, hk, hs, bs, _, _, .opened t _, _, h, vs => by
      simp only [Body.subst, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨o', t'⟩, ht, ⟨m, hm⟩, _, h⟩ := h
      simp only at hm
      subst hm
      split at h
      · simp only [Option.pure_def, Option.some.injEq] at h
        subst h
        simp only [Body.eval]
        exact Term.subst_eval hk (USub.Agree.liftSet (@USub.Agree.cheapOnly _ _ _ _ _ _ _ _ _ hs)
          (D' + 1) bs vs) JRen.Agree.nil t ht
      · cases h
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ => x
theorem Comp.subst_eval : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {rk : KLRen Φ Φ'} → {s : USub Δ Φ' Γ Γ'} → {κ : KEnv Δ Φ} → {κ' : KEnv Δ Φ'} →
    {ρ : UEnv Δ Γ} → {ρ' : UEnv Δ Γ'} → KLRen.Agree rk κ κ' → USub.Agree s κ' ρ ρ' →
    {τ : Ty ks} → {ℓ : Nat} → (c : Comp Δ D Φ Γ τ ℓ) → {p : (ℓ' : Nat) × Comp Δ D' Φ' Γ' τ ℓ'} →
    c.subst rk s = some p → p.2.eval κ' ρ' = c.eval κ ρ
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hs, _, _, .app f a _, _, h => by
      simp only [Comp.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨f', hf, a', ha, q, hq, rfl⟩ := h
      simp only [Comp.eval, PExpr.subst_eval hk hs f hf, PExpr.subst_eval hk hs a ha] <;> rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hs, _, _, .share n, _, h => by
      simp only [Comp.subst, Option.map_eq_some_iff] at h
      obtain ⟨n', hn, rfl⟩ := h
      simp only [Comp.eval, Neu.substN_eval hk hs n hn] <;> rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hs, _, _, .nat_rec n z st _, _, h => by
      simp only [Comp.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨n', hn, z', hz, s', hs', q, hq, rfl⟩ := h
      simp only [Comp.eval]
      rw [PExpr.subst_eval hk hs n hn, PExpr.subst_eval hk hs z hz]
      congr 1
      funext k acc
      exact Body.subst_eval hk hs st hs' (Tuple.cons acc (Tuple.cons k Tuple.nil))
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hs, _, _, .array_foldl a z st _, _, h => by
      simp only [Comp.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨a', ha, z', hz, s', hs', q, hq, rfl⟩ := h
      simp only [Comp.eval]
      rw [PExpr.subst_eval hk hs a ha, PExpr.subst_eval hk hs z hz]
      congr 1
      funext acc x
      exact Body.subst_eval hk hs st hs' (Tuple.cons x (Tuple.cons acc Tuple.nil))
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hs, _, _, .data_rec b ρt us brs j e _, _, h => by
      simp only [Comp.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨brs', hbrs, e', he, q, hq, rfl⟩ := h
      simp only [Comp.eval]
      rw [PExpr.subst_eval hk hs e he]
      congr 1
      funext i x
      exact Body.subst_eval hk hs (brs i) (Fin.optAll_eq_some hbrs i) (Tuple.cons x Tuple.nil)
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hs, _, _, .data_brec b ρt k us brs j e _, _, h => by
      simp only [Comp.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨brs', hbrs, e', he, q, hq, rfl⟩ := h
      simp only [Comp.eval]
      rw [PExpr.subst_eval hk hs e he]
      congr 1
      funext i x
      exact Body.subst_eval hk hs (brs i) (Fin.optAll_eq_some hbrs i) (Tuple.cons x Tuple.nil)
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hs, _, _, .thunk_force e, _, h => by
      simp only [Comp.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨⟨o', e'⟩, he, ⟨m, hm⟩, _, rfl⟩ := h
      simp only at hm
      subst hm
      simp only [Comp.eval]
      rw [PExpr.subst_eval hk hs e he]
  | _, _, _, _, _, _, _, _, _, _, _, _, hk, hs, _, _, .lazy_force e, _, h => by
      simp only [Comp.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨⟨o', e'⟩, he, ⟨m, hm⟩, _, rfl⟩ := h
      simp only at hm
      subst hm
      simp only [Comp.eval]
      rw [PExpr.subst_eval hk hs e he]
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ => x
theorem Term.subst_eval : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {js js' : JCtx ks} → {τ : Ty ks} → {rk : KLRen Φ Φ'} → {s : USub Δ Φ' Γ Γ'} →
    {rj : JRen js js'} → {κ : KEnv Δ Φ} → {κ' : KEnv Δ Φ'} → {ρ : UEnv Δ Γ} →
    {ρ' : UEnv Δ Γ'} → {jκ : JEnv Δ τ js} → {jκ' : JEnv Δ τ js'} →
    KLRen.Agree rk κ κ' → USub.Agree s κ' ρ ρ' → JRen.Agree rj jκ jκ' →
    {o : Lvl} → (t : Term Δ D Φ Γ τ js o) → {p : (o' : Lvl) × Term Δ D' Φ' Γ' τ js' o'} →
    t.subst rk s rj = some p → p.2.eval κ' ρ' jκ' = t.eval κ ρ jκ
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hs, _, _, .ret e, _, h => by
      simp only [Term.subst, Option.map_eq_some_iff] at h
      obtain ⟨e', he, rfl⟩ := h
      simp only [Term.eval, PExpr.subst_eval hk hs e he]
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hs, hj, _, .letV u v b, _, h => by
      simp only [Term.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨v', hv, b', hb, rfl⟩ := h
      simp only [Term.eval, Val.subst_eval hk hs v hv]
      exact Term.subst_eval (hk.lift _ _ _ _ _) (hs.wkK _ _) hj b hb
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hs, hj, _, .letE u c b, _, h => by
      simp only [Term.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨c', hc, b', hb, rfl⟩ := h
      simp only [Term.eval, Comp.subst_eval hk hs c hc]
      exact Term.subst_eval hk (hs.lift _ _ _ _ _) hj b hb
  | _, _, _, _, _, _, _, _, _, _, _, _, _, κ', _, ρ', _, _, hk, hs, hj, _,
      .record_casesOn us n b, _, h => by
      simp only [Term.subst, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨q, hq, h⟩ := h
      have hn := Neu.subst_eval hk hs n hq
      split at h
      · rename_i m hm
        simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
        obtain ⟨b', hb, rfl⟩ := h
        simp only [Term.eval, PExpr.toNeu?_eval _ _ q.2 hm, hn]
        exact Term.subst_eval hk (hs.liftAnnot _ _ _ _ _) hj b hb
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨as, has, hb⟩ := h
        have hv := PExpr.recordArgs?_eval κ' ρ' q.2 has
        rw [hn] at hv
        simp only [Term.eval]
        rw [hv]
        exact Term.subst_eval hk (hs.ofArgs _ _ _ as.2) hj b hb
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hs, hj, _, .branch br, _, h => by
      simp only [Term.subst] at h
      simp only [Term.eval]
      exact Branch.subst_eval hk hs hj br h
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hs, hj, _, .jump j e, _, h => by
      simp only [Term.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨j', hj', e', he, rfl⟩ := h
      simp only [Term.eval, PExpr.subst_eval hk hs e he, hj j j' hj']
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ => x
theorem Branch.subst_eval : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {js js' : JCtx ks} → {τ : Ty ks} → {rk : KLRen Φ Φ'} → {s : USub Δ Φ' Γ Γ'} →
    {rj : JRen js js'} → {κ : KEnv Δ Φ} → {κ' : KEnv Δ Φ'} → {ρ : UEnv Δ Γ} →
    {ρ' : UEnv Δ Γ'} → {jκ : JEnv Δ τ js} → {jκ' : JEnv Δ τ js'} →
    KLRen.Agree rk κ κ' → USub.Agree s κ' ρ ρ' → JRen.Agree rj jκ jκ' →
    {ℓ : Nat} → (br : Branch Δ D Φ Γ τ js ℓ) → {p : (o' : Lvl) × Term Δ D' Φ' Γ' τ js' o'} →
    br.subst rk s rj = some p → p.2.eval κ' ρ' jκ' = br.eval κ ρ jκ
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hs, hj, _, .ite c t e, _, h => by
      simp only [Branch.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨c', hc, t', ht, e', he, rfl⟩ := h
      simp only [Term.eval, Branch.eval, Neu.substN_eval hk hs c hc, Term.subst_eval hk hs hj t ht,
        Term.subst_eval hk hs hj e he]
  | _, _, _, _, _, _, _, _, _, _, _, _, _, κ', _, ρ', _, _, hk, hs, hj, _,
      .enum_casesOn e bs, _, h => by
      simp only [Branch.subst, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨q, hq, h⟩ := h
      have he := Neu.subst_eval hk hs e hq
      split at h
      · rename_i m hm
        simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
        obtain ⟨bs', hbs, rfl⟩ := h
        simp only [Term.eval, Branch.eval]
        rw [PExpr.toNeu?_eval κ' ρ' q.2 hm, he]
        exact Term.subst_eval hk hs hj _ (Fin.optAll_eq_some hbs _)
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨i, hi, h⟩ := h
        have hv := PExpr.enumLit?_eval κ' ρ' q.2 hi
        rw [he] at hv
        simp only [Branch.eval]
        rw [hv]
        exact Term.subst_eval hk hs hj _ h
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hs, hj, _, .union_casesOn e bs, _, h => by
      simp only [Branch.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨e', he, bs', hbs, rfl⟩ := h
      simp only [Term.eval, Branch.eval, Neu.substN_eval hk hs e he]
      exact Branches.subst_eval hk hs hj bs hbs _
  | _, _, _, _, _, _, _, _, _, _, _, _, κ, κ', ρ, ρ', jκ, jκ', hk, hs, hj, _,
      .join σ u uₓ body main, _, h => by
      simp only [Branch.subst, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨m, hm, h⟩ := h
      -- the join point, seen from both sides: the source's closure
      let f := fun v => body.eval κ (Tuple.cons v ρ) jκ
      have hmain := Branch.subst_eval (jκ := Tuple.cons f jκ) (jκ' := Tuple.cons f jκ') hk hs
        (hj.lift ⟨σ, u⟩ f) main hm
      simp only [Branch.eval]
      split at h
      · rename_i b hb
        simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
        obtain ⟨body', hbody, rfl⟩ := h
        have hf := funext fun v => Term.subst_eval hk (hs.lift _ _ _ _ v) hj body hbody
        simp only [Term.eval, Branch.eval]
        rw [hf, ← Term.asBranch?_eval κ' ρ' _ m.2 hb]
        exact hmain
      · split at h
        · rename_i σ' j o' a hr
          rw [← hmain, Term.asJump?_eval κ' ρ' _ m.2 hr]
          simp only
          split at h
          · rename_i hh hsplit
            split at h
            · rw [JVar.split_inl_get jκ' f j hsplit]
              have := Term.subst_eval hk (hs.cons ⟨_, hh.down ▸ a⟩) hj body h
              rw [this]
              simp only [f, PExpr.eval_cast]
            · cases h
          · rename_i j' hsplit
            simp only [Option.pure_def, Option.some.injEq] at h
            subst h
            simp only [Term.eval, JVar.split_inr_get jκ' f j hsplit]
        · cases h
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ => x
theorem Branches.subst_eval : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} →
    {js js' : JCtx ks} → {τ : Ty ks} → {rk : KLRen Φ Φ'} → {s : USub Δ Φ' Γ Γ'} →
    {rj : JRen js js'} → {κ : KEnv Δ Φ} → {κ' : KEnv Δ Φ'} → {ρ : UEnv Δ Γ} →
    {ρ' : UEnv Δ Γ'} → {jκ : JEnv Δ τ js} → {jκ' : JEnv Δ τ js'} →
    KLRen.Agree rk κ κ' → USub.Agree s κ' ρ ρ' → JRen.Agree rj jκ jκ' →
    {bs : List Bool} → {cs : Ctors ks bs} → {o : Lvl} → (br : Branches Δ D Φ Γ cs τ js o) →
    {p : (o' : Lvl) × Branches Δ D' Φ' Γ' cs τ js' o'} → br.subst rk s rj = some p →
    ∀ x, p.2.eval κ' ρ' jκ' x = br.eval κ ρ jκ x
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hs, hj, _, _, _,
      .two us₁ us₂ b₁ b₂, _, h, x => by
      simp only [Branches.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨b₁', h₁, b₂', h₂, rfl⟩ := h
      simp only [Branches.eval]
      congr 1
      · funext v; exact Term.subst_eval hk (hs.liftAnnot _ _ _ _ _) hj b₁ h₁
      · funext v; exact Term.subst_eval hk (hs.liftAnnot _ _ _ _ _) hj b₂ h₂
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hs, hj, _, _, _,
      .cons us b bs, _, h, x => by
      simp only [Branches.subst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨b', hb, bs', hbs, rfl⟩ := h
      simp only [Branches.eval]
      congr 1
      · funext v; exact Term.subst_eval hk (hs.liftAnnot _ _ _ _ _) hj b hb
      · funext r; exact Branches.subst_eval hk hs hj bs hbs r
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ => x
end

end LeanScript

end
