module

public import LeanScript.Term.Optimize.InlineBlock
public import LeanScript.Term.Optimize.InlineEval
public import LeanScript.Term.Rename.RelevelEval

@[expose] public section

set_option autoImplicit false

/-!
# Inlining the body of a known closure preserves the value

The pieces of `LeanScript.Term.Optimize.InlineBlock` compute the value they replace:
`BlockFn.applyNeu_eval` (the body at the call is the call) and `Term.bindRet_eval` (a
straight-line body followed by the rest is the rest applied to its answer).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## What is known stays true -/

theorem BlockFn.rename_sem {Φ Φ' : KCtx ks} {rk : KRen Φ Φ'} {κ : KEnv Δ Φ} {κ' : KEnv Δ Φ'}
    (hk : KRen.Agree rk κ κ') {ty : Ty ks} {f : BlockFn Δ Φ ty} {f' : BlockFn Δ Φ' ty}
    (h : f.rename rk = some f') {x : Ty.Den Δ ty} (hs : f.Sem κ x) : f'.Sem κ' x := by
  obtain ⟨σ, τ, hty, u, D, o, body⟩ := f
  simp only [BlockFn.rename, Option.map_eq_some_iff] at h
  obtain ⟨b, hb, rfl⟩ := h
  intro v
  exact (hs v).trans (Term.rename_eval hk (URen.Agree.id _) (JRen.Agree.id _) body hb).symm

theorem BInfo.Agree.empty {Φ : KCtx ks} (κ : KEnv Δ Φ) : (BInfo.empty : BInfo Δ Φ).Agree κ := by
  intro _ _ _ _ h
  cases h

theorem BInfo.Agree.cons {Φ : KCtx ks} {b : KBinder ks} {I : BInfo Δ Φ} {κ : KEnv Δ Φ}
    (hI : I.Agree κ) {new : Option (BlockFn Δ Φ b.ty)} {x : Ty.Den Δ b.ty}
    (hn : ∀ f, new = some f → f.Sem κ x) :
    (BInfo.cons new I).Agree (Tuple.cons x κ : KEnv Δ (b :: Φ)) := by
  intro ty o k f hf
  cases k with
  | head =>
      simp only [BInfo.cons, BInfo.consGet, Option.bind_eq_some_iff] at hf
      obtain ⟨g, hg, hr⟩ := hf
      rw [KEnv.get_cons_head]
      exact BlockFn.rename_sem (KRen.Agree.wk1 κ x) hr (hn g hg)
  | tail k =>
      simp only [BInfo.cons, BInfo.consGet, Option.bind_eq_some_iff] at hf
      obtain ⟨g, hg, hr⟩ := hf
      rw [KEnv.get_cons_tail]
      exact BlockFn.rename_sem (KRen.Agree.wk1 κ x) hr (hI k g hg)

theorem BInfo.Agree.toClosed {Φ : KCtx ks} {I : BInfo Δ Φ} {κ : KEnv Δ Φ} (hI : I.Agree κ) :
    I.toClosed.Agree (KEnv.closedOnly κ) := by
  intro ty o k f hf
  simp only [BInfo.toClosed, Option.bind_eq_some_iff] at hf
  obtain ⟨g, hg, hr⟩ := hf
  rw [KEnv.closedOnly_get]
  exact BlockFn.rename_sem (KRen.Agree.mask κ) hr (hI k.unmask g hg)

theorem Val.blockFn?_sem : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {ty : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ ty o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    {f : BlockFn Δ Φ ty} → v.blockFn? = some f → f.Sem κ (v.eval κ ρ)
  | _, _, _, _, _, .lam (.closed t), κ, ρ, f, h => by
      simp only [Val.blockFn?, Option.map_eq_some_iff] at h
      obtain ⟨t', ht, rfl⟩ := h
      intro v
      have hk : KRen.Agree (fun x => some x.unmask) (KEnv.closedOnly κ) κ := by
        intro _ _ x y hxy
        simp only [Option.some.injEq] at hxy
        subst hxy
        exact (KEnv.closedOnly_get κ x).symm
      rw [Term.rename_eval hk (URen.Agree.id _) (JRen.Agree.id _) t ht]
      rfl
  | _, _, _, _, _, .lam (.opened _ _), _, _, _, h => by simp [Val.blockFn?] at h
  | _, _, _, _, _, .thunk_mk _, _, _, _, h => by simp [Val.blockFn?] at h
  | _, _, _, _, _, .lazy_mk _, _, _, _, h => by simp [Val.blockFn?] at h
  | _, _, _, _, _, .record_mk _, _, _, _, h => by simp [Val.blockFn?] at h
  | _, _, _, _, _, .union_mk _ _, _, _, _, h => by simp [Val.blockFn?] at h
  | _, _, _, _, _, .array_mk _, _, _, _, h => by simp [Val.blockFn?] at h
  | _, _, _, _, _, .list_mk _, _, _, _, h => by simp [Val.blockFn?] at h
  | _, _, _, _, _, .data_in _ _ _, _, _, _, h => by simp [Val.blockFn?] at h

/-! ## The body at a call -/

theorem ULRen.Agree.single {Γ : UCtx ks} {σ : Ty ks} {u : Usage01ω} {D ℓx : Nat}
    (x : UVar Γ σ ℓx) (ρ : UEnv Δ Γ) :
    ULRen.Agree (ULRen.single (u := u) (D := D) x)
      (Tuple.cons (ρ.get x) Tuple.nil : UEnv Δ [⟨σ, u, D⟩]) ρ := by
  intro _ _ y p hyp
  cases y with
  | head _ =>
      simp only [ULRen.single, Option.some.injEq] at hyp
      subst hyp; simp
  | tail y => exact nomatch y

theorem KLRen.Agree.id {Φ : KCtx ks} (κ : KEnv Δ Φ) : KLRen.Agree KLRen.id κ κ := by
  intro _ _ x p h
  simp only [KLRen.id, Option.some.injEq] at h
  subst h; rfl

theorem JRen.Agree.ofNil {τ : Ty ks} {js : JCtx ks} (jκ : JEnv Δ τ js) :
    JRen.Agree JRen.ofNil (PUnit.unit : JEnv Δ τ []) jκ := by
  intro _ x; exact nomatch x

theorem BlockFn.applyVar_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks}
    {js : JCtx ks} {ℓx : Nat} {f : BlockFn Δ Φ (.fn σ τ)} {κ : KEnv Δ Φ}
    {g : Ty.Den Δ (.fn σ τ)} (hs : f.Sem κ g) (x : UVar Γ σ ℓx) (ρ : UEnv Δ Γ)
    (jκ : JEnv Δ τ js) {r : (o' : Lvl) × Term Δ d Φ Γ τ js o'} (h : f.applyVar x = some r) :
    r.2.eval κ ρ jκ = g (ρ.get x) := by
  obtain ⟨σ', τ', hty, u, D, o, body⟩ := f
  simp only [BlockFn.applyVar] at h
  split at h
  · rename_i hst
    obtain ⟨rfl, rfl⟩ := hst
    rw [Term.relvl_eval (KLRen.Agree.id κ) (ULRen.Agree.single x ρ) (JRen.Agree.ofNil jκ) _ h]
    exact (hs (ρ.get x)).symm
  · cases h

theorem BlockFn.applyNeu_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks}
    {js : JCtx ks} {ℓn : Nat} {f : BlockFn Δ Φ (.fn σ τ)} {κ : KEnv Δ Φ}
    {g : Ty.Den Δ (.fn σ τ)} (hs : f.Sem κ g) (n : Neu Δ Φ Γ σ ℓn) (ρ : UEnv Δ Γ)
    (jκ : JEnv Δ τ js) {r : (o' : Lvl) × Term Δ d Φ Γ τ js o'} (h : f.applyNeu n = some r) :
    r.2.eval κ ρ jκ = g (n.eval κ ρ) := by
  unfold BlockFn.applyNeu at h
  split at h
  · rename_i x
    exact BlockFn.applyVar_eval hs x ρ jκ h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    simp only [Term.eval, Comp.eval]
    rw [BlockFn.applyVar_eval hs _ _ jκ hr', UEnv.get_cons_head]

/-! ## Splicing -/

theorem URen.Agree.wk1 {Γ : UCtx ks} {b : UBinder ks} (ρ : UEnv Δ Γ) (v : Ty.Den Δ b.ty) :
    URen.Agree (URen.wk1 (b := b)) ρ (Tuple.cons v ρ : UEnv Δ (b :: Γ)) := by
  intro _ _ x y h
  simp only [URen.wk1, Option.some.injEq] at h
  subst h
  exact UEnv.get_cons_tail _ _ _

theorem URen.Agree.wkN {Γ : UCtx ks} (ρ : UEnv Δ Γ) : (bs : UCtx ks) → (vs : UEnv Δ bs) →
    URen.Agree (URen.wkN bs) ρ (Tuple.append vs ρ)
  | [], _ => URen.Agree.id ρ
  | b :: bs, vs => by
      intro x y h
      simp only [URen.wkN, Option.map_eq_some_iff] at h
      obtain ⟨z, hz, rfl⟩ := h
      rw [Tuple.append_cons, UEnv.get_cons_tail]
      exact URen.Agree.wkN ρ bs vs.tail x z hz

theorem JMap.lift_agree {σ τ : Ty ks} {js js' : JCtx ks} {m : JMap js js'} {j : JVar js' σ}
    {jκ : JEnv Δ σ js} {jκ' : JEnv Δ τ js'}
    (hm : ∀ {σ' : Ty ks} (x : JVar js σ') (v : Ty.Den Δ σ'), jκ'.get (m x) v = jκ'.get j (jκ.get x v))
    (b : JBinder ks) (f : Ty.Den Δ b.ty → Ty.Den Δ σ) (f' : Ty.Den Δ b.ty → Ty.Den Δ τ)
    (hf : ∀ v, f' v = jκ'.get j (f v)) :
    ∀ {σ' : Ty ks} (x : JVar (b :: js) σ') (v : Ty.Den Δ σ'),
      JEnv.get (Tuple.cons f' jκ' : JEnv Δ τ (b :: js')) (m.lift b x) v =
        JEnv.get (Tuple.cons f' jκ' : JEnv Δ τ (b :: js')) (.tail j)
          (JEnv.get (Tuple.cons f jκ : JEnv Δ σ (b :: js)) x v) := by
  intro σ' x v
  obtain ⟨bσ, bu⟩ := b
  cases x with
  | head => simp only [JMap.lift, JEnv.get_cons_head, JEnv.get_cons_tail]; exact hf v
  | tail x => simp only [JMap.lift, JEnv.get_cons_tail]; exact hm x v

mutual
theorem Term.retToJump_eval {σ τ : Ty ks} : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {js js' : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ σ js o) → (m : JMap js js') →
    (j : JVar js' σ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ σ js) →
    (jκ' : JEnv Δ τ js') →
    (∀ {σ' : Ty ks} (x : JVar js σ') (v : Ty.Den Δ σ'), jκ'.get (m x) v = jκ'.get j (jκ.get x v)) →
    (t.retToJump m j).eval κ ρ jκ' = jκ'.get j (t.eval κ ρ jκ)
  | _, _, _, _, _, _, .ret e, _, j, κ, ρ, jκ, jκ', _ => rfl
  | _, _, _, _, _, _, .letV u v b, m, j, κ, ρ, jκ, jκ', hm => by
      simp only [Term.retToJump, Term.eval]; exact Term.retToJump_eval b m j _ ρ jκ jκ' hm
  | _, _, _, _, _, _, .letE u c b, m, j, κ, ρ, jκ, jκ', hm => by
      simp only [Term.retToJump, Term.eval]; exact Term.retToJump_eval b m j κ _ jκ jκ' hm
  | _, _, _, _, _, _, .record_casesOn us n b, m, j, κ, ρ, jκ, jκ', hm => by
      simp only [Term.retToJump, Term.eval]; exact Term.retToJump_eval b m j κ _ jκ jκ' hm
  | _, _, _, _, _, _, .branch br, m, j, κ, ρ, jκ, jκ', hm => by
      simp only [Term.retToJump, Term.eval]; exact Branch.retToJump_eval br m j κ ρ jκ jκ' hm
  | _, _, _, _, _, _, .jump x e, m, j, κ, ρ, jκ, jκ', hm => by
      simp only [Term.retToJump, Term.eval]; exact hm x _
  termination_by structural _ _ _ _ _ _ t => t
theorem Branch.retToJump_eval {σ τ : Ty ks} : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {js js' : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ σ js ℓ) → (m : JMap js js') →
    (j : JVar js' σ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ σ js) →
    (jκ' : JEnv Δ τ js') →
    (∀ {σ' : Ty ks} (x : JVar js σ') (v : Ty.Den Δ σ'), jκ'.get (m x) v = jκ'.get j (jκ.get x v)) →
    (br.retToJump m j).eval κ ρ jκ' = jκ'.get j (br.eval κ ρ jκ)
  | _, _, _, _, _, _, .ite c t e, m, j, κ, ρ, jκ, jκ', hm => by
      simp only [Branch.retToJump, Branch.eval]
      split <;> exact Term.retToJump_eval _ m j κ ρ jκ jκ' hm
  | _, _, _, _, _, _, .enum_casesOn e bs, m, j, κ, ρ, jκ, jκ', hm => by
      simp only [Branch.retToJump, Branch.eval]; exact Term.retToJump_eval _ m j κ ρ jκ jκ' hm
  | _, _, _, _, _, _, .union_casesOn e bs, m, j, κ, ρ, jκ, jκ', hm => by
      simp only [Branch.retToJump, Branch.eval]
      exact Branches.retToJump_eval bs m j κ ρ jκ jκ' hm _
  | _, _, _, _, _, _, .join σ' u uₓ body main, m, j, κ, ρ, jκ, jκ', hm => by
      simp only [Branch.retToJump, Branch.eval]
      rw [Branch.retToJump_eval main (m.lift _) (.tail j) κ ρ _ _
        (JMap.lift_agree hm ⟨σ', u⟩ _ _ (fun v => Term.retToJump_eval body m j κ (Tuple.cons v ρ) jκ jκ' hm))]
      exact JEnv.get_cons_tail (b := ⟨σ', u⟩) _ jκ' j ▸ rfl
  termination_by structural _ _ _ _ _ _ br => br
theorem Branches.retToJump_eval {σ τ : Ty ks} : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {js js' : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs σ js o) → (m : JMap js js') → (j : JVar js' σ) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ σ js) → (jκ' : JEnv Δ τ js') →
    (∀ {σ' : Ty ks} (x : JVar js σ') (v : Ty.Den Δ σ'), jκ'.get (m x) v = jκ'.get j (jκ.get x v)) →
    ∀ x, (br.retToJump m j).eval κ ρ jκ' x = jκ'.get j (br.eval κ ρ jκ x)
  | _, _, _, _, _, _, _, _, .two (c₁ := c₁) (c₂ := c₂) us₁ us₂ b₁ b₂, m, j, κ, ρ, jκ, jκ', hm, x => by
      simp only [Branches.retToJump, Branches.eval]
      have h₁ := fun v => Term.retToJump_eval b₁ m j κ
        (Tuple.append (UEnv.ofDL _ _ us₁ v) ρ) jκ jκ' hm
      have h₂ := fun v => Term.retToJump_eval b₂ m j κ
        (Tuple.append (UEnv.ofDL _ _ us₂ v) ρ) jκ jκ' hm
      simp only [h₁, h₂]
      unfold Ctor.twoCase
      split <;> (split <;> rfl)
  | _, _, _, _, _, _, _, _, .cons (c := c) us b bs, m, j, κ, ρ, jκ, jκ', hm, x => by
      simp only [Branches.retToJump, Branches.eval]
      have h₁ := fun v => Term.retToJump_eval b m j κ
        (Tuple.append (UEnv.ofDL _ _ us v) ρ) jκ jκ' hm
      have h₂ := fun r => Branches.retToJump_eval bs m j κ ρ jκ jκ' hm r
      simp only [h₁, h₂]
      unfold Ctor.consCase
      split <;> (split <;> rfl)
  termination_by structural _ _ _ _ _ _ _ _ br => br
end

theorem Term.bindRet_eval {d : Nat} {σ τ : Ty ks} {u : Usage1ω} :
    {Φ : KCtx ks} → {Γ : UCtx ks} → {js : JCtx ks} → {o o' : Lvl} →
    (t : Term Δ d Φ Γ σ [] o) → (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
    {r : (o'' : Lvl) × Term Δ d Φ Γ τ js o''} → Term.bindRet t b = some r →
    r.2.eval κ ρ jκ = b.eval κ (Tuple.cons (t.eval κ ρ PUnit.unit) ρ) jκ
  | _, _, _, _, _, .ret e, b, κ, ρ, jκ, r, h => by
      cases e with
      | neu n =>
          simp only [Term.bindRet, Option.some.injEq] at h
          subst h; rfl
      | _ => simp [Term.bindRet] at h
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

end LeanScript

end
