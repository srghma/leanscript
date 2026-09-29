module

public import LeanScript.Term.Optimize.Inline

@[expose] public section

set_option autoImplicit false

/-!
# Inlining known closures preserves the value

`Term.inlineKnown_eval`: the walk of `LeanScript.Term.Optimize.Inline` does not change the
value of a statement, in any environment.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## What is known stays true -/

theorem ExprFn.rename_sem {Φ Φ' : KCtx ks} {rk : KRen Φ Φ'} {κ : KEnv Δ Φ} {κ' : KEnv Δ Φ'}
    (hk : KRen.Agree rk κ κ') {ty : Ty ks} {f : ExprFn Δ Φ ty} {f' : ExprFn Δ Φ' ty}
    (h : f.rename rk = some f') {x : Ty.Den Δ ty} (hs : f.Sem κ x) : f'.Sem κ' x := by
  obtain ⟨σ, τ, hty, u, lv, o, body⟩ := f
  simp only [ExprFn.rename, Option.map_eq_some_iff] at h
  obtain ⟨b, hb, rfl⟩ := h
  intro v
  exact (hs v).trans (PExpr.rename_eval hk (URen.Agree.id _) body hb).symm

theorem KInfo.Agree.empty {Φ : KCtx ks} (κ : KEnv Δ Φ) : (KInfo.empty : KInfo Δ Φ).Agree κ := by
  intro _ _ _ _ h
  cases h

theorem KRen.Agree.wk1 {Φ : KCtx ks} {b : KBinder ks} (κ : KEnv Δ Φ) (x : Ty.Den Δ b.ty) :
    KRen.Agree (KRen.wk1 (b := b)) κ (Tuple.cons x κ : KEnv Δ (b :: Φ)) := by
  intro _ _ y z h
  simp only [KRen.wk1, Option.some.injEq] at h
  subst h
  exact KEnv.get_cons_tail _ _ _

theorem KInfo.Agree.cons {Φ : KCtx ks} {b : KBinder ks} {I : KInfo Δ Φ} {κ : KEnv Δ Φ}
    (hI : I.Agree κ) {new : Option (ExprFn Δ Φ b.ty)} {x : Ty.Den Δ b.ty}
    (hn : ∀ f, new = some f → f.Sem κ x) :
    (KInfo.cons new I).Agree (Tuple.cons x κ : KEnv Δ (b :: Φ)) := by
  intro ty o k f hf
  cases k with
  | head =>
      simp only [KInfo.cons, KInfo.consGet, Option.bind_eq_some_iff] at hf
      obtain ⟨g, hg, hr⟩ := hf
      rw [KEnv.get_cons_head]
      exact ExprFn.rename_sem (KRen.Agree.wk1 κ x) hr (hn g hg)
  | tail k =>
      simp only [KInfo.cons, KInfo.consGet, Option.bind_eq_some_iff] at hf
      obtain ⟨g, hg, hr⟩ := hf
      rw [KEnv.get_cons_tail]
      exact ExprFn.rename_sem (KRen.Agree.wk1 κ x) hr (hI k g hg)

theorem KRen.Agree.mask {Φ : KCtx ks} (κ : KEnv Δ Φ) :
    KRen.Agree (fun x => x.mask) κ (KEnv.closedOnly κ) := by
  intro _ _ x y h
  rw [KEnv.closedOnly_get, KVar.mask_unmask x h]

theorem KInfo.Agree.toClosed {Φ : KCtx ks} {I : KInfo Δ Φ} {κ : KEnv Δ Φ} (hI : I.Agree κ) :
    I.toClosed.Agree (KEnv.closedOnly κ) := by
  intro ty o k f hf
  simp only [KInfo.toClosed, Option.bind_eq_some_iff] at hf
  obtain ⟨g, hg, hr⟩ := hf
  rw [KEnv.closedOnly_get]
  exact ExprFn.rename_sem (KRen.Agree.mask κ) hr (hI k.unmask g hg)

theorem Val.exprFn?_sem : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {ty : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ ty o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    {f : ExprFn Δ Φ ty} → v.exprFn? = some f → f.Sem κ (v.eval κ ρ)
  | _, _, _, _, _, .lam (.closed (.ret p)), κ, ρ, f, h => by
      simp only [Val.exprFn?, Option.map_eq_some_iff] at h
      obtain ⟨p', hp, rfl⟩ := h
      intro v
      have hk : KRen.Agree (fun x => some x.unmask) (KEnv.closedOnly κ) κ := by
        intro _ _ x y hxy
        simp only [Option.some.injEq] at hxy
        subst hxy
        exact (KEnv.closedOnly_get κ x).symm
      rw [PExpr.rename_eval hk (URen.Agree.id _) p hp]
      rfl
  | _, _, _, _, _, .lam (.closed (.letV _ _ _)), _, _, _, h => by simp [Val.exprFn?] at h
  | _, _, _, _, _, .lam (.closed (.letE _ _ _)), _, _, _, h => by simp [Val.exprFn?] at h
  | _, _, _, _, _, .lam (.closed (.record_casesOn _ _ _)), _, _, _, h => by
      simp [Val.exprFn?] at h
  | _, _, _, _, _, .lam (.closed (.branch _)), _, _, _, h => by simp [Val.exprFn?] at h
  | _, _, _, _, _, .lam (.closed (.jump _ _)), _, _, _, h => by simp [Val.exprFn?] at h
  | _, _, _, _, _, .lam (.opened _ _), _, _, _, h => by simp [Val.exprFn?] at h
  | _, _, _, _, _, .thunk_mk _, _, _, _, h => by simp [Val.exprFn?] at h
  | _, _, _, _, _, .lazy_mk _, _, _, _, h => by simp [Val.exprFn?] at h
  | _, _, _, _, _, .record_mk _, _, _, _, h => by simp [Val.exprFn?] at h
  | _, _, _, _, _, .union_mk _ _, _, _, _, h => by simp [Val.exprFn?] at h
  | _, _, _, _, _, .array_mk _, _, _, _, h => by simp [Val.exprFn?] at h
  | _, _, _, _, _, .list_mk _, _, _, _, h => by simp [Val.exprFn?] at h
  | _, _, _, _, _, .data_in _ _ _, _, _, _, h => by simp [Val.exprFn?] at h

/-! ## Substitution -/

theorem PExpr.toNeu?_eval {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) : {o : Lvl} → (p : PExpr Δ Φ Γ τ o) → {m : (ℓ : Nat) × Neu Δ Φ Γ τ ℓ} →
    p.toNeu? = some m → m.2.eval κ ρ = p.eval κ ρ
  | _, .neu n, m, h => by
      simp only [PExpr.toNeu?, Option.some.injEq] at h
      subst h; rfl
  | _, .kvar _, _, h => by simp [PExpr.toNeu?] at h
  | _, .lit _ _, _, h => by simp [PExpr.toNeu?] at h
  | _, .enum_mk _ _, _, h => by simp [PExpr.toNeu?] at h
  | _, .record_mk _, _, h => by simp [PExpr.toNeu?] at h
  | _, .union_mk _ _, _, h => by simp [PExpr.toNeu?] at h
  | _, .array_mk _, _, h => by simp [PExpr.toNeu?] at h
  | _, .list_mk _, _, h => by simp [PExpr.toNeu?] at h
  | _, .data_in _ _ _, _, h => by simp [PExpr.toNeu?] at h

section Subst
variable {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {u : Usage01ω} {lv : Nat} {oa : Lvl}
  (a : PExpr Δ Φ Γ σ oa) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)

mutual
theorem Neu.inl_eval : {τ : Ty ks} → {ℓ : Nat} → (n : Neu Δ Φ [⟨σ, u, lv⟩] τ ℓ) →
    {r : (o' : Lvl) × PExpr Δ Φ Γ τ o'} → Neu.inl a n = some r →
    r.2.eval κ ρ = n.eval κ (Tuple.cons (a.eval κ ρ) Tuple.nil)
  | _, _, .var (.head _), _, h => by
      simp only [Neu.inl, Option.some.injEq] at h
      subst h; rfl
  | _, _, .var (.tail x), _, _ => nomatch x
  | _, _, .data_out b j n, _, h => by
      simp only [Neu.inl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨r, hr, m, hm, rfl⟩ := h
      simp only [PExpr.eval, Neu.eval]
      rw [PExpr.toNeu?_eval κ ρ _ hm, Neu.inl_eval n hr]
  | _, _, .cond c x y, _, h => by
      simp only [Neu.inl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨r, hr, m, hm, x', hx, y', hy, rfl⟩ := h
      simp only [PExpr.eval, Neu.eval]
      rw [PExpr.toNeu?_eval κ ρ _ hm, Neu.inl_eval c hr, PExpr.inl_eval x hx,
        PExpr.inl_eval y hy]
  | _, _, .extern e args _, _, h => by
      simp only [Neu.inl, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨o', args'⟩, hr, h2⟩ := h
      cases o' with
      | none => simp at h2
      | some ℓ' =>
          simp only [Option.pure_def, Option.some.injEq] at h2
          subst h2
          simp only [PExpr.eval, Neu.eval]
          rw [Args.inl_eval args hr]
  termination_by structural _ _ n => n
theorem PExpr.inl_eval : {τ : Ty ks} → {o : Lvl} → (p : PExpr Δ Φ [⟨σ, u, lv⟩] τ o) →
    {r : (o' : Lvl) × PExpr Δ Φ Γ τ o'} → PExpr.inl a p = some r →
    r.2.eval κ ρ = p.eval κ (Tuple.cons (a.eval κ ρ) Tuple.nil)
  | _, _, .neu n, _, h => by
      simp only [PExpr.inl] at h
      rw [Neu.inl_eval n h]; rfl
  | _, _, .kvar _, _, h => by
      simp only [PExpr.inl, Option.some.injEq] at h
      subst h; rfl
  | _, _, .lit _ _, _, h => by
      simp only [PExpr.inl, Option.some.injEq] at h
      subst h; rfl
  | _, _, .enum_mk _ _, _, h => by
      simp only [PExpr.inl, Option.some.injEq] at h
      subst h; rfl
  | _, _, .record_mk args, _, h => by
      simp only [PExpr.inl, Option.map_eq_some_iff] at h
      obtain ⟨r, hr, rfl⟩ := h
      simp only [PExpr.eval]
      rw [Args.inl_eval args hr]
  | _, _, .union_mk ix args, _, h => by
      simp only [PExpr.inl, Option.map_eq_some_iff] at h
      obtain ⟨r, hr, rfl⟩ := h
      simp only [PExpr.eval]
      rw [Args.inl_eval args hr]
  | _, _, .array_mk es, _, h => by
      simp only [PExpr.inl, Option.map_eq_some_iff] at h
      obtain ⟨r, hr, rfl⟩ := h
      simp only [PExpr.eval]
      rw [Elems.inl_eval es hr]
  | _, _, .list_mk es, _, h => by
      simp only [PExpr.inl, Option.map_eq_some_iff] at h
      obtain ⟨r, hr, rfl⟩ := h
      simp only [PExpr.eval]
      rw [Elems.inl_eval es hr]
  | _, _, .data_in b j e, _, h => by
      simp only [PExpr.inl, Option.map_eq_some_iff] at h
      obtain ⟨r, hr, rfl⟩ := h
      simp only [PExpr.eval]
      rw [PExpr.inl_eval e hr]
  termination_by structural _ _ p => p
theorem Args.inl_eval : {σs : List (Ty ks)} → {o : Lvl} → (as : Args Δ Φ [⟨σ, u, lv⟩] σs o) →
    {r : (o' : Lvl) × Args Δ Φ Γ σs o'} → Args.inl a as = some r →
    r.2.eval κ ρ = as.eval κ (Tuple.cons (a.eval κ ρ) Tuple.nil)
  | _, _, .nil, _, h => by
      simp only [Args.inl, Option.some.injEq] at h
      subst h; rfl
  | _, _, .cons x xs, _, h => by
      simp only [Args.inl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨x', hx, xs', hxs, rfl⟩ := h
      simp only [Args.eval]
      rw [PExpr.inl_eval x hx, Args.inl_eval xs hxs]
  termination_by structural _ _ as => as
theorem Elems.inl_eval : {t : Ty ks} → {o : Lvl} → (es : Elems Δ Φ [⟨σ, u, lv⟩] t o) →
    {r : (o' : Lvl) × Elems Δ Φ Γ t o'} → Elems.inl a es = some r →
    r.2.eval κ ρ = es.eval κ (Tuple.cons (a.eval κ ρ) Tuple.nil)
  | _, _, .nil, _, h => by
      simp only [Elems.inl, Option.some.injEq] at h
      subst h; rfl
  | _, _, .cons x xs, _, h => by
      simp only [Elems.inl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨x', hx, xs', hxs, rfl⟩ := h
      simp only [Elems.eval]
      rw [PExpr.inl_eval x hx, Elems.inl_eval xs hxs]
  termination_by structural _ _ es => es
end

end Subst

theorem ExprFn.apply_eval {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {oa : Lvl}
    {f : ExprFn Δ Φ (.fn σ τ)} {κ : KEnv Δ Φ} {x : Ty.Den Δ (.fn σ τ)} (hs : f.Sem κ x)
    (a : PExpr Δ Φ Γ σ oa) (ρ : UEnv Δ Γ) {r : (o' : Lvl) × PExpr Δ Φ Γ τ o'}
    (h : f.apply a = some r) : r.2.eval κ ρ = x (a.eval κ ρ) := by
  obtain ⟨σ', τ', hty, u, lv, o, body⟩ := f
  simp only [ExprFn.apply] at h
  split at h
  · rename_i hst
    obtain ⟨rfl, rfl⟩ := hst
    rw [PExpr.inl_eval a κ ρ _ h]
    exact (hs (a.eval κ ρ)).symm
  · cases h

theorem PExpr.asShare_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat}
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : {o' : Lvl} → (p : PExpr Δ Φ Γ τ o') →
    {c : Comp Δ d Φ Γ τ ℓ} → p.asShare = some c → c.eval κ ρ = p.eval κ ρ
  | _, .neu n, c, h => by
      simp only [PExpr.asShare] at h
      split at h
      · rename_i hl
        subst hl
        simp only [Option.some.injEq] at h
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

theorem Comp.inlApp_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {of oa : Lvl}
    {ℓ : Nat} {I : KInfo Δ Φ} {κ : KEnv Δ Φ} (hI : I.Agree κ) (ρ : UEnv Δ Γ)
    (f : PExpr Δ Φ Γ (.fn σ τ) of) (a : PExpr Δ Φ Γ σ oa) (h : Lvl.meet of oa = some ℓ) :
    (Comp.inlApp (d := d) I f a h).eval κ ρ = (Comp.app f a h : Comp Δ d Φ Γ τ ℓ).eval κ ρ := by
  cases f with
  | neu n => rfl
  | kvar k =>
      simp only [Comp.inlApp]
      cases hk : I.get k with
      | none => rfl
      | some e =>
          simp only [Option.bind_some]
          cases he : e.apply a with
          | none => rfl
          | some r =>
              simp only [Option.bind_some]
              cases hc : r.2.asShare (d := d) (ℓ := ℓ) with
              | none => rfl
              | some c =>
                  simp only [Option.getD_some]
                  rw [PExpr.asShare_eval κ ρ _ hc, ExprFn.apply_eval (hI k e hk) a ρ he]
                  rfl

/-! ## The walk -/

mutual
theorem Val.inlWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → (I : KInfo Δ Φ) → (κ : KEnv Δ Φ) → I.Agree κ →
    (ρ : UEnv Δ Γ) → (v.inlWalk I).eval κ ρ = v.eval κ ρ
  | _, _, _, _, _, .lam b, I, κ, hI, ρ => by
      simp only [Val.inlWalk, Val.eval]; funext x; rw [Body.inlWalk_eval b I κ hI ρ]
  | _, _, _, _, _, .thunk_mk b, I, κ, hI, ρ => by
      simp only [Val.inlWalk, Val.eval]; rw [Body.inlWalk_eval b I κ hI ρ]
  | _, _, _, _, _, .lazy_mk b, I, κ, hI, ρ => by
      simp only [Val.inlWalk, Val.eval]; rw [Body.inlWalk_eval b I κ hI ρ]
  | _, _, _, _, _, .record_mk _, _, _, _, _ => rfl
  | _, _, _, _, _, .union_mk _ _, _, _, _, _ => rfl
  | _, _, _, _, _, .array_mk _, _, _, _, _ => rfl
  | _, _, _, _, _, .list_mk _, _, _, _, _ => rfl
  | _, _, _, _, _, .data_in _ _ _, _, _, _, _ => rfl
  termination_by structural _ _ _ _ _ x => x
theorem Body.inlWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (I : KInfo Δ Φ) → (κ : KEnv Δ Φ) → I.Agree κ →
    (ρ : UEnv Δ Γ) → (vs : UEnv Δ bs) → (b.inlWalk I).eval κ ρ vs = b.eval κ ρ vs
  | _, _, _, _, _, _, .closed t, I, κ, hI, _, _ => by
      simp only [Body.inlWalk, Body.eval]; exact Term.inlWalk_eval t _ _ hI.toClosed _ _
  | _, _, _, _, _, _, .opened t _, I, κ, hI, _, _ => by
      simp only [Body.inlWalk, Body.eval]; exact Term.inlWalk_eval t _ _ hI _ _
  termination_by structural _ _ _ _ _ _ x => x
theorem Comp.inlWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (I : KInfo Δ Φ) → (κ : KEnv Δ Φ) → I.Agree κ →
    (ρ : UEnv Δ Γ) → (c.inlWalk I).eval κ ρ = c.eval κ ρ
  | _, _, _, _, _, .app f a h, I, κ, hI, ρ => by
      simp only [Comp.inlWalk]; exact Comp.inlApp_eval hI ρ f a h
  | _, _, _, _, _, .share _, _, _, _, _ => rfl
  | _, _, _, _, _, .nat_rec n z s _, I, κ, hI, ρ => by
      simp only [Comp.inlWalk, Comp.eval]
      congr 1; funext k acc; exact Body.inlWalk_eval s I κ hI ρ _
  | _, _, _, _, _, .array_foldl a z s _, I, κ, hI, ρ => by
      simp only [Comp.inlWalk, Comp.eval]
      congr 1; funext acc x; exact Body.inlWalk_eval s I κ hI ρ _
  | _, _, _, _, _, .data_rec b ρt us brs j e _, I, κ, hI, ρ => by
      simp only [Comp.inlWalk, Comp.eval]
      congr 1; funext i x; exact Body.inlWalk_eval (brs i) I κ hI ρ _
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, I, κ, hI, ρ => by
      simp only [Comp.inlWalk, Comp.eval]
      congr 1; funext i x; exact Body.inlWalk_eval (brs i) I κ hI ρ _
  | _, _, _, _, _, .thunk_force _, _, _, _, _ => rfl
  | _, _, _, _, _, .lazy_force _, _, _, _, _ => rfl
  termination_by structural _ _ _ _ _ x => x
theorem Term.inlWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → (I : KInfo Δ Φ) →
    (κ : KEnv Δ Φ) → I.Agree κ → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
    (t.inlWalk I).eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, .ret _, _, _, _, _, _ => rfl
  | _, _, _, _, _, _, .letV u v b, I, κ, hI, ρ, jκ => by
      simp only [Term.inlWalk, Term.eval]
      rw [Term.inlWalk_eval b _ _ (hI.cons (fun f hf => Val.exprFn?_sem _ κ ρ hf)) ρ jκ,
        Val.inlWalk_eval v I κ hI ρ]
  | _, _, _, _, _, _, .letE u c b, I, κ, hI, ρ, jκ => by
      simp only [Term.inlWalk, Term.eval]
      rw [Comp.inlWalk_eval c I κ hI ρ, Term.inlWalk_eval b I κ hI _ jκ]
  | _, _, _, _, _, _, .record_casesOn us n b, I, κ, hI, ρ, jκ => by
      simp only [Term.inlWalk, Term.eval]
      exact Term.inlWalk_eval b I κ hI _ jκ
  | _, _, _, _, _, _, .branch br, I, κ, hI, ρ, jκ => by
      simp only [Term.inlWalk, Term.eval]
      exact Branch.inlWalk_eval br I κ hI ρ jκ
  | _, _, _, _, _, _, .jump _ _, _, _, _, _, _ => rfl
  termination_by structural _ _ _ _ _ _ x => x
theorem Branch.inlWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → (I : KInfo Δ Φ) →
    (κ : KEnv Δ Φ) → I.Agree κ → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
    (br.inlWalk I).eval κ ρ jκ = br.eval κ ρ jκ
  | _, _, _, _, _, _, .ite c t e, I, κ, hI, ρ, jκ => by
      simp only [Branch.inlWalk, Branch.eval, Term.inlWalk_eval t I κ hI,
        Term.inlWalk_eval e I κ hI]
  | _, _, _, _, _, _, .enum_casesOn e bs, I, κ, hI, ρ, jκ => by
      simp only [Branch.inlWalk, Branch.eval]; exact Term.inlWalk_eval _ I κ hI _ _
  | _, _, _, _, _, _, .union_casesOn e bs, I, κ, hI, ρ, jκ => by
      simp only [Branch.inlWalk, Branch.eval]; exact Branches.inlWalk_eval bs I κ hI ρ jκ _
  | _, _, _, _, _, _, .join σ u uₓ body main, I, κ, hI, ρ, jκ => by
      simp only [Branch.inlWalk, Branch.eval, Branch.inlWalk_eval main I κ hI,
        Term.inlWalk_eval body I κ hI]
  termination_by structural _ _ _ _ _ _ x => x
theorem Branches.inlWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (I : KInfo Δ Φ) → (κ : KEnv Δ Φ) → I.Agree κ →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
      ∀ x, (br.inlWalk I).eval κ ρ jκ x = br.eval κ ρ jκ x
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, I, κ, hI, ρ, jκ, x => by
      simp only [Branches.inlWalk, Branches.eval, Term.inlWalk_eval b₁ I κ hI,
        Term.inlWalk_eval b₂ I κ hI]
  | _, _, _, _, _, _, _, _, .cons us b bs, I, κ, hI, ρ, jκ, x => by
      simp only [Branches.inlWalk, Branches.eval, Term.inlWalk_eval b I κ hI,
        Branches.inlWalk_eval bs I κ hI]
  termination_by structural _ _ _ _ _ _ _ _ x => x
end

/-- **Inlining known closures does not change the value of a statement**, in any
    environment. -/
theorem Term.inlineKnown_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {o : Lvl} (t : Term Δ d Φ Γ τ js o) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    t.inlineKnown.eval κ ρ jκ = t.eval κ ρ jκ :=
  Term.inlWalk_eval t _ κ (KInfo.Agree.empty κ) ρ jκ

end LeanScript

end
