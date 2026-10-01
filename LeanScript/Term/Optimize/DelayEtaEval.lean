module

public import LeanScript.Term.Optimize.DelayEta
public import LeanScript.Term.Optimize.CountRename

@[expose] public section

set_option autoImplicit false

/-!
# Replacing delays that only force another delay preserves the value and the calls

`Term.delayEta_eval`: the walk of `LeanScript.Term.Optimize.DelayEta` does not change the value
of a statement, in any environment; `Term.numCalls_delayEta`: nor the number of its calls.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## What is known -/

theorem AInfo.Agree.empty {Φ : KCtx ks} {Γ : UCtx ks} (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (AInfo.empty : AInfo Δ Φ Γ).Agree κ ρ := by
  intro _ _ _ _ h
  cases h

theorem AInfo.Agree.cons {Φ : KCtx ks} {Γ : UCtx ks} {b : KBinder ks} {I : AInfo Δ Φ Γ}
    {κ : KEnv Δ Φ} {ρ : UEnv Δ Γ} (hI : I.Agree κ ρ) {new : Option (PExpr Δ Φ Γ b.ty b.lv)}
    {x : Ty.Den Δ b.ty} (hn : ∀ e, new = some e → e.eval κ ρ = x) :
    (AInfo.cons new I).Agree (Tuple.cons x κ : KEnv Δ (b :: Φ)) ρ := by
  intro ty o k f hf
  cases k with
  | head =>
      simp only [AInfo.cons, AInfo.consGet, Option.bind_eq_some_iff] at hf
      obtain ⟨g, hg, hr⟩ := hf
      rw [KEnv.get_cons_head, PExpr.rename_eval (KRen.Agree.wk1 κ x) (URen.Agree.id ρ) g hr]
      exact hn g hg
  | tail k =>
      simp only [AInfo.cons, AInfo.consGet, Option.bind_eq_some_iff] at hf
      obtain ⟨g, hg, hr⟩ := hf
      rw [KEnv.get_cons_tail, PExpr.rename_eval (KRen.Agree.wk1 κ x) (URen.Agree.id ρ) g hr]
      exact hI k g hg

theorem AInfo.Agree.wkN {Φ : KCtx ks} {Γ : UCtx ks} {I : AInfo Δ Φ Γ} {κ : KEnv Δ Φ}
    {ρ : UEnv Δ Γ} (hI : I.Agree κ ρ) (bs : UCtx ks) (vs : UEnv Δ bs) :
    (I.wkN bs).Agree κ (Tuple.append vs ρ) := by
  intro ty o k f hf
  simp only [AInfo.wkN, Option.bind_eq_some_iff] at hf
  obtain ⟨g, hg, hr⟩ := hf
  rw [PExpr.rename_eval (KRen.Agree.id κ) (URen.Agree.wkN ρ bs vs) g hr]
  exact hI k g hg

theorem AInfo.Agree.wk1 {Φ : KCtx ks} {Γ : UCtx ks} {I : AInfo Δ Φ Γ} {κ : KEnv Δ Φ}
    {ρ : UEnv Δ Γ} (hI : I.Agree κ ρ) (b : UBinder ks) (v : Ty.Den Δ b.ty) :
    (I.wk1 b).Agree κ (Tuple.cons v ρ : UEnv Δ (b :: Γ)) := by
  intro ty o k f hf
  simp only [AInfo.wk1, Option.bind_eq_some_iff] at hf
  obtain ⟨g, hg, hr⟩ := hf
  rw [PExpr.rename_eval (KRen.Agree.id κ) (URen.Agree.wk1 ρ v) g hr]
  exact hI k g hg

/-! ## Delays that force a delay -/

theorem Comp.lazyEtaWith_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {js : JCtx ks}
    {τ : Ty ks false} {u : Usage01ω} {o' : Lvl} (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (jκ : JEnv Δ τ.relax js) : {σ : Ty ks} → {ℓ : Nat} → (c : Comp Δ d Φ Γ σ ℓ) →
    (b : Term Δ d Φ (⟨σ, u, d⟩ :: Γ) τ.relax js o') →
    {r : (ℓ : Nat) × PExpr Δ Φ Γ (.lazy τ) (some ℓ)} → c.lazyEtaWith b = some r →
    b.eval κ (Tuple.cons (c.eval κ ρ) ρ) jκ = Ty.toRelax _ τ (r.2.eval κ ρ)
  | _, _, .lazy_force (τ := τ') e, b, r, h => by
      simp only [Comp.lazyEtaWith] at h
      split at h
      · rename_i hτ
        subst hτ
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨hh, hb, rfl⟩ := h
        simp only [Comp.eval]
        exact Term.retHead?_eval b hb κ ρ _ jκ
      · cases h
  | _, _, .app _ _ _, _, _, h => by simp [Comp.lazyEtaWith] at h
  | _, _, .share _, _, _, h => by simp [Comp.lazyEtaWith] at h
  | _, _, .nat_rec _ _ _ _, _, _, h => by simp [Comp.lazyEtaWith] at h
  | _, _, .array_foldl _ _ _ _, _, _, h => by simp [Comp.lazyEtaWith] at h
  | _, _, .data_rec _ _ _ _ _ _ _, _, _, h => by simp [Comp.lazyEtaWith] at h
  | _, _, .data_brec _ _ _ _ _ _ _ _, _, _, h => by simp [Comp.lazyEtaWith] at h
  | _, _, .thunk_force _, _, _, h => by simp [Comp.lazyEtaWith] at h

theorem Term.lazyForceRet?_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {js : JCtx ks}
    {τ : Ty ks false} (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ.relax js) :
    {o : Lvl} → (t : Term Δ d Φ Γ τ.relax js o) →
    {r : (ℓ : Nat) × PExpr Δ Φ Γ (.lazy τ) (some ℓ)} → t.lazyForceRet? = some r →
    t.eval κ ρ jκ = Ty.toRelax _ τ (r.2.eval κ ρ)
  | _, .letE _ c b, _, h => by
      simp only [Term.lazyForceRet?] at h
      simp only [Term.eval]
      exact Comp.lazyEtaWith_eval κ ρ jκ c b h
  | _, .ret _, _, h => by simp [Term.lazyForceRet?] at h
  | _, .letV _ _ _, _, h => by simp [Term.lazyForceRet?] at h
  | _, .record_casesOn _ _ _, _, h => by simp [Term.lazyForceRet?] at h
  | _, .branch _, _, h => by simp [Term.lazyForceRet?] at h
  | _, .jump _ _, _, h => by simp [Term.lazyForceRet?] at h

theorem Body.lazyAlias?_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks false}
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : {o : Lvl} → (b : Body Δ d Φ Γ [] τ.relax o) →
    {e : PExpr Δ Φ Γ (.lazy τ) o} → b.lazyAlias? = some e →
    e.eval κ ρ = Ty.ofRelax _ τ (b.eval κ ρ Tuple.nil)
  | _, .closed _, _, h => by simp [Body.lazyAlias?] at h
  | _, .opened t _, e, h => by
      simp only [Body.lazyAlias?, Option.bind_eq_some_iff] at h
      obtain ⟨r, hr, h⟩ := h
      split at h
      · rename_i hl
        obtain ⟨ℓ, e'⟩ := r
        simp only at hl
        subst hl
        simp only [Option.some.injEq] at h
        subst h
        simp only [Body.eval]
        rw [Term.lazyForceRet?_eval (js := []) κ _ PUnit.unit t hr]
        exact (Ty.ofRelax_toRelax _ _ _).symm
      · cases h

theorem Comp.thunkEtaWith_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {js : JCtx ks}
    {τ : Ty ks false} {u : Usage01ω} {o' : Lvl} (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (jκ : JEnv Δ τ.relax js) : {σ : Ty ks} → {ℓ : Nat} → (c : Comp Δ d Φ Γ σ ℓ) →
    (b : Term Δ d Φ (⟨σ, u, d⟩ :: Γ) τ.relax js o') →
    {r : (ℓ : Nat) × PExpr Δ Φ Γ (.thunk τ) (some ℓ)} → c.thunkEtaWith b = some r →
    b.eval κ (Tuple.cons (c.eval κ ρ) ρ) jκ = Ty.toRelax _ τ (r.2.eval κ ρ)
  | _, _, .thunk_force (τ := τ') e, b, r, h => by
      simp only [Comp.thunkEtaWith] at h
      split at h
      · rename_i hτ
        subst hτ
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨hh, hb, rfl⟩ := h
        simp only [Comp.eval]
        exact Term.retHead?_eval b hb κ ρ _ jκ
      · cases h
  | _, _, .app _ _ _, _, _, h => by simp [Comp.thunkEtaWith] at h
  | _, _, .share _, _, _, h => by simp [Comp.thunkEtaWith] at h
  | _, _, .nat_rec _ _ _ _, _, _, h => by simp [Comp.thunkEtaWith] at h
  | _, _, .array_foldl _ _ _ _, _, _, h => by simp [Comp.thunkEtaWith] at h
  | _, _, .data_rec _ _ _ _ _ _ _, _, _, h => by simp [Comp.thunkEtaWith] at h
  | _, _, .data_brec _ _ _ _ _ _ _ _, _, _, h => by simp [Comp.thunkEtaWith] at h
  | _, _, .lazy_force _, _, _, h => by simp [Comp.thunkEtaWith] at h

theorem Term.thunkForceRet?_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {js : JCtx ks}
    {τ : Ty ks false} (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ.relax js) :
    {o : Lvl} → (t : Term Δ d Φ Γ τ.relax js o) →
    {r : (ℓ : Nat) × PExpr Δ Φ Γ (.thunk τ) (some ℓ)} → t.thunkForceRet? = some r →
    t.eval κ ρ jκ = Ty.toRelax _ τ (r.2.eval κ ρ)
  | _, .letE _ c b, _, h => by
      simp only [Term.thunkForceRet?] at h
      simp only [Term.eval]
      exact Comp.thunkEtaWith_eval κ ρ jκ c b h
  | _, .ret _, _, h => by simp [Term.thunkForceRet?] at h
  | _, .letV _ _ _, _, h => by simp [Term.thunkForceRet?] at h
  | _, .record_casesOn _ _ _, _, h => by simp [Term.thunkForceRet?] at h
  | _, .branch _, _, h => by simp [Term.thunkForceRet?] at h
  | _, .jump _ _, _, h => by simp [Term.thunkForceRet?] at h

theorem Body.thunkAlias?_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks false}
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : {o : Lvl} → (b : Body Δ d Φ Γ [] τ.relax o) →
    {e : PExpr Δ Φ Γ (.thunk τ) o} → b.thunkAlias? = some e →
    e.eval κ ρ = Ty.ofRelax _ τ (b.eval κ ρ Tuple.nil)
  | _, .closed _, _, h => by simp [Body.thunkAlias?] at h
  | _, .opened t _, e, h => by
      simp only [Body.thunkAlias?, Option.bind_eq_some_iff] at h
      obtain ⟨r, hr, h⟩ := h
      split at h
      · rename_i hl
        obtain ⟨ℓ, e'⟩ := r
        simp only at hl
        subst hl
        simp only [Option.some.injEq] at h
        subst h
        simp only [Body.eval]
        rw [Term.thunkForceRet?_eval (js := []) κ _ PUnit.unit t hr]
        exact (Ty.ofRelax_toRelax _ _ _).symm
      · cases h

theorem Val.delayAlias?_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {ty : Ty ks} {o : Lvl}
    (v : Val Δ d Φ Γ ty o) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (e : PExpr Δ Φ Γ ty o)
    (h : v.delayAlias? = some e) : e.eval κ ρ = v.eval κ ρ := by
  cases v with
  | lazy_mk b =>
      simp only [Val.delayAlias?] at h
      simp only [Val.eval]
      exact Body.lazyAlias?_eval κ ρ b h
  | thunk_mk b =>
      simp only [Val.delayAlias?] at h
      simp only [Val.eval]
      exact Body.thunkAlias?_eval κ ρ b h
  | _ => simp [Val.delayAlias?] at h

/-! ## Replacing the known values in pure expressions -/

section SubA
variable {Φ : KCtx ks} {Γ : UCtx ks} {I : AInfo Δ Φ Γ} {κ : KEnv Δ Φ} {ρ : UEnv Δ Γ}

mutual
theorem Neu.subA_eval (hI : I.Agree κ ρ) :
    {τ : Ty ks} → {ℓ : Nat} → (n : Neu Δ Φ Γ τ ℓ) → (n.subA I).eval κ ρ = n.eval κ ρ
  | _, _, .var _ => rfl
  | _, _, .data_out b j n => by simp only [Neu.subA, Neu.eval, Neu.subA_eval hI n] <;> rfl
  | _, _, .cond c a b => by
      simp only [Neu.subA, Neu.eval, Neu.subA_eval hI c, PExpr.subA_eval hI a,
        PExpr.subA_eval hI b] <;> rfl
  | _, _, .extern e args _ => by simp only [Neu.subA, Neu.eval, Args.subA_eval hI args] <;> rfl
theorem PExpr.subA_eval (hI : I.Agree κ ρ) :
    {τ : Ty ks} → {o : Lvl} → (e : PExpr Δ Φ Γ τ o) → (e.subA I).eval κ ρ = e.eval κ ρ
  | _, _, .neu n => by simp only [PExpr.subA, PExpr.eval, Neu.subA_eval hI n] <;> rfl
  | _, _, .kvar k => by
      cases hk : I.get k with
      | none => simp only [PExpr.subA, hk, Option.getD_none]
      | some e => simp only [PExpr.subA, hk, Option.getD_some, PExpr.eval]; exact hI k e hk
  | _, _, .lit _ _ => rfl
  | _, _, .enum_mk _ _ => rfl
  | _, _, .record_mk args => by simp only [PExpr.subA, PExpr.eval, Args.subA_eval hI args] <;> rfl
  | _, _, .union_mk _ args => by simp only [PExpr.subA, PExpr.eval, Args.subA_eval hI args] <;> rfl
  | _, _, .array_mk es => by simp only [PExpr.subA, PExpr.eval, Elems.subA_eval hI es] <;> rfl
  | _, _, .list_mk es => by simp only [PExpr.subA, PExpr.eval, Elems.subA_eval hI es] <;> rfl
  | _, _, .data_in b j e => by simp only [PExpr.subA, PExpr.eval, PExpr.subA_eval hI e] <;> rfl
theorem Args.subA_eval (hI : I.Agree κ ρ) :
    {σs : List (Ty ks)} → {o : Lvl} → (as : Args Δ Φ Γ σs o) → (as.subA I).eval κ ρ = as.eval κ ρ
  | _, _, .nil => rfl
  | _, _, .cons a as => by
      simp only [Args.subA, Args.eval, PExpr.subA_eval hI a, Args.subA_eval hI as] <;> rfl
theorem Elems.subA_eval (hI : I.Agree κ ρ) :
    {t : Ty ks} → {o : Lvl} → (es : Elems Δ Φ Γ t o) → (es.subA I).eval κ ρ = es.eval κ ρ
  | _, _, .nil => rfl
  | _, _, .cons e es => by
      simp only [Elems.subA, Elems.eval, PExpr.subA_eval hI e, Elems.subA_eval hI es] <;> rfl
end

end SubA

/-! ## The walk preserves the value -/

mutual
theorem Val.deWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → (I : AInfo Δ Φ Γ) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → I.Agree κ ρ → (v.deWalk I).eval κ ρ = v.eval κ ρ
  | _, _, _, _, _, .lam b, I, κ, ρ, hI => by
      simp only [Val.deWalk, Val.eval]; funext x; rw [Body.deWalk_eval b I κ ρ hI]
  | _, _, _, _, _, .thunk_mk b, I, κ, ρ, hI => by
      simp only [Val.deWalk, Val.eval]; rw [Body.deWalk_eval b I κ ρ hI]
  | _, _, _, _, _, .lazy_mk b, I, κ, ρ, hI => by
      simp only [Val.deWalk, Val.eval]; rw [Body.deWalk_eval b I κ ρ hI]
  | _, _, _, _, _, .record_mk args, _, _, _, hI => by
      simp only [Val.deWalk, Val.eval, Args.subA_eval hI] <;> rfl
  | _, _, _, _, _, .union_mk _ args, _, _, _, hI => by
      simp only [Val.deWalk, Val.eval, Args.subA_eval hI] <;> rfl
  | _, _, _, _, _, .array_mk es, _, _, _, hI => by
      simp only [Val.deWalk, Val.eval, Elems.subA_eval hI] <;> rfl
  | _, _, _, _, _, .list_mk es, _, _, _, hI => by
      simp only [Val.deWalk, Val.eval, Elems.subA_eval hI] <;> rfl
  | _, _, _, _, _, .data_in _ _ e, _, _, _, hI => by
      simp only [Val.deWalk, Val.eval, PExpr.subA_eval hI] <;> rfl
  termination_by structural _ _ _ _ _ x => x
theorem Body.deWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (I : AInfo Δ Φ Γ) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → I.Agree κ ρ → (vs : UEnv Δ bs) → (b.deWalk I).eval κ ρ vs = b.eval κ ρ vs
  | _, _, _, _, _, _, .closed t, _, κ, _, _, vs => by
      simp only [Body.deWalk, Body.eval]
      exact Term.deWalk_eval t _ _ _ (AInfo.Agree.empty _ _) _
  | _, _, _, bs, _, _, .opened t _, I, κ, ρ, hI, vs => by
      simp only [Body.deWalk, Body.eval]
      exact Term.deWalk_eval t _ _ _ (hI.wkN bs vs) _
  termination_by structural _ _ _ _ _ _ x => x
theorem Comp.deWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (I : AInfo Δ Φ Γ) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → I.Agree κ ρ → (c.deWalk I).eval κ ρ = c.eval κ ρ
  | _, _, _, _, _, .app f a _, _, _, _, hI => by
      simp only [Comp.deWalk, Comp.eval, PExpr.subA_eval hI]
  | _, _, _, _, _, .share n, _, _, _, hI => by
      simp only [Comp.deWalk, Comp.eval, Neu.subA_eval hI]
  | _, _, _, _, _, .nat_rec n z s _, I, κ, ρ, hI => by
      simp only [Comp.deWalk, Comp.eval]
      rw [PExpr.subA_eval hI n, PExpr.subA_eval hI z]
      congr 1; funext k acc; exact Body.deWalk_eval s I κ ρ hI _
  | _, _, _, _, _, .array_foldl a z s _, I, κ, ρ, hI => by
      simp only [Comp.deWalk, Comp.eval]
      rw [PExpr.subA_eval hI a, PExpr.subA_eval hI z]
      congr 1; funext acc x; exact Body.deWalk_eval s I κ ρ hI _
  | _, _, _, _, _, .data_rec b ρt us brs j e _, I, κ, ρ, hI => by
      simp only [Comp.deWalk, Comp.eval]
      rw [PExpr.subA_eval hI e]
      congr 1; funext i x; exact Body.deWalk_eval (brs i) I κ ρ hI _
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, I, κ, ρ, hI => by
      simp only [Comp.deWalk, Comp.eval]
      rw [PExpr.subA_eval hI e]
      congr 1; funext i x; exact Body.deWalk_eval (brs i) I κ ρ hI _
  | _, _, _, _, _, .thunk_force e, _, _, _, hI => by
      simp only [Comp.deWalk, Comp.eval, PExpr.subA_eval hI]
  | _, _, _, _, _, .lazy_force e, _, _, _, hI => by
      simp only [Comp.deWalk, Comp.eval, PExpr.subA_eval hI]
  termination_by structural _ _ _ _ _ x => x
theorem Term.deWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → (I : AInfo Δ Φ Γ) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → I.Agree κ ρ → (jκ : JEnv Δ τ js) →
    (t.deWalk I).eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, .ret e, _, _, _, hI, _ => by
      simp only [Term.deWalk, Term.eval, PExpr.subA_eval hI]
  | _, _, _, _, _, _, .letV u v b, I, κ, ρ, hI, jκ => by
      simp only [Term.deWalk, Term.eval]
      rw [Term.deWalk_eval b _ _ ρ
        (hI.cons (fun e he => Val.delayAlias?_eval (v.deWalk I) κ ρ e he)) jκ,
        Val.deWalk_eval v I κ ρ hI]
  | _, _, _, _, _, _, .letE u c b, I, κ, ρ, hI, jκ => by
      simp only [Term.deWalk, Term.eval]
      rw [Comp.deWalk_eval c I κ ρ hI]
      exact Term.deWalk_eval b _ κ _ (hI.wk1 _ _) jκ
  | _, _, _, _, _, _, .record_casesOn us n b, I, κ, ρ, hI, jκ => by
      simp only [Term.deWalk, Term.eval, Neu.subA_eval hI]
      exact Term.deWalk_eval b _ κ _ (hI.wkN _ _) jκ
  | _, _, _, _, _, _, .branch br, I, κ, ρ, hI, jκ => by
      simp only [Term.deWalk, Term.eval]
      exact Branch.deWalk_eval br I κ ρ hI jκ
  | _, _, _, _, _, _, .jump _ _, _, _, _, hI, _ => by
      simp only [Term.deWalk, Term.eval, PExpr.subA_eval hI]
  termination_by structural _ _ _ _ _ _ x => x
theorem Branch.deWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → (I : AInfo Δ Φ Γ) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → I.Agree κ ρ → (jκ : JEnv Δ τ js) →
    (br.deWalk I).eval κ ρ jκ = br.eval κ ρ jκ
  | _, _, _, _, _, _, .ite c t e, I, κ, ρ, hI, jκ => by
      simp only [Branch.deWalk, Branch.eval, Neu.subA_eval hI, Term.deWalk_eval t I κ ρ hI,
        Term.deWalk_eval e I κ ρ hI]
  | _, _, _, _, _, _, .enum_casesOn e bs, I, κ, ρ, hI, jκ => by
      simp only [Branch.deWalk, Branch.eval]
      have he := Neu.subA_eval hI e
      generalize (Neu.subA I e).eval κ ρ = x at he ⊢
      subst he
      exact Term.deWalk_eval _ I κ ρ hI _
  | _, _, _, _, _, _, .union_casesOn e bs, I, κ, ρ, hI, jκ => by
      simp only [Branch.deWalk, Branch.eval, Neu.subA_eval hI]
      exact Branches.deWalk_eval bs I κ ρ hI jκ _
  | _, _, _, _, _, _, .join σ u uₓ body main, I, κ, ρ, hI, jκ => by
      simp only [Branch.deWalk, Branch.eval]
      rw [Branch.deWalk_eval main I κ ρ hI]
      have hf : (fun v => (body.deWalk (I.wk1 _)).eval κ (Tuple.cons v ρ) jκ) =
          (fun v => body.eval κ (Tuple.cons v ρ) jκ) :=
        funext fun v => Term.deWalk_eval body _ κ _ (hI.wk1 _ v) jκ
      rw [hf]
  termination_by structural _ _ _ _ _ _ x => x
theorem Branches.deWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (I : AInfo Δ Φ Γ) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → I.Agree κ ρ → (jκ : JEnv Δ τ js) →
      ∀ x, (br.deWalk I).eval κ ρ jκ x = br.eval κ ρ jκ x
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, I, κ, ρ, hI, jκ, x => by
      simp only [Branches.deWalk, Branches.eval]
      congr 1
      · funext v; exact Term.deWalk_eval b₁ _ κ _ (hI.wkN _ _) jκ
      · funext v; exact Term.deWalk_eval b₂ _ κ _ (hI.wkN _ _) jκ
  | _, _, _, _, _, _, _, _, .cons us b bs, I, κ, ρ, hI, jκ, x => by
      simp only [Branches.deWalk, Branches.eval]
      congr 1
      · funext v; exact Term.deWalk_eval b _ κ _ (hI.wkN _ _) jκ
      · funext r; exact Branches.deWalk_eval bs I κ ρ hI jκ r
  termination_by structural _ _ _ _ _ _ _ _ x => x
end

/-- **Replacing the delays that only force another delay by that delay does not change the
    value of a statement**, in any environment. -/
theorem Term.delayEta_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {o : Lvl} (t : Term Δ d Φ Γ τ js o) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    t.delayEta.eval κ ρ jκ = t.eval κ ρ jκ :=
  Term.deWalk_eval t _ κ ρ (AInfo.Agree.empty κ ρ) jκ

/-! ## The walk keeps the calls -/

mutual
theorem Val.numCalls_deWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → (I : AInfo Δ Φ Γ) → (v.deWalk I).numCalls = v.numCalls
  | _, _, _, _, _, .lam b, I => by
      simp only [Val.deWalk, Val.numCalls]; exact Body.numCalls_deWalk b I
  | _, _, _, _, _, .thunk_mk b, I => by
      simp only [Val.deWalk, Val.numCalls]; exact Body.numCalls_deWalk b I
  | _, _, _, _, _, .lazy_mk b, I => by
      simp only [Val.deWalk, Val.numCalls]; exact Body.numCalls_deWalk b I
  | _, _, _, _, _, .record_mk _, _ => rfl
  | _, _, _, _, _, .union_mk _ _, _ => rfl
  | _, _, _, _, _, .array_mk _, _ => rfl
  | _, _, _, _, _, .list_mk _, _ => rfl
  | _, _, _, _, _, .data_in _ _ _, _ => rfl
  termination_by structural _ _ _ _ _ x => x
theorem Body.numCalls_deWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (I : AInfo Δ Φ Γ) →
    (b.deWalk I).numCalls = b.numCalls
  | _, _, _, _, _, _, .closed t, _ => by
      simp only [Body.deWalk, Body.numCalls]; exact Term.numCalls_deWalk t _
  | _, _, _, _, _, _, .opened t _, I => by
      simp only [Body.deWalk, Body.numCalls]; exact Term.numCalls_deWalk t _
  termination_by structural _ _ _ _ _ _ x => x
theorem Comp.numCalls_deWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (I : AInfo Δ Φ Γ) → (c.deWalk I).numCalls = c.numCalls
  | _, _, _, _, _, .app _ _ _, _ => rfl
  | _, _, _, _, _, .share _, _ => rfl
  | _, _, _, _, _, .nat_rec n z s _, I => by
      simp only [Comp.deWalk, Comp.numCalls]; exact Body.numCalls_deWalk s I
  | _, _, _, _, _, .array_foldl a z s _, I => by
      simp only [Comp.deWalk, Comp.numCalls]; exact Body.numCalls_deWalk s I
  | _, _, _, _, _, .data_rec b ρt us brs j e _, I => by
      simp only [Comp.deWalk, Comp.numCalls]
      exact Fin.sumNat_congr _ (fun i => Body.numCalls_deWalk (brs i) I)
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, I => by
      simp only [Comp.deWalk, Comp.numCalls]
      exact Fin.sumNat_congr _ (fun i => Body.numCalls_deWalk (brs i) I)
  | _, _, _, _, _, .thunk_force _, _ => rfl
  | _, _, _, _, _, .lazy_force _, _ => rfl
  termination_by structural _ _ _ _ _ x => x
theorem Term.numCalls_deWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → (I : AInfo Δ Φ Γ) →
    (t.deWalk I).numCalls = t.numCalls
  | _, _, _, _, _, _, .ret _, _ => rfl
  | _, _, _, _, _, _, .letV u v b, I => by
      simp only [Term.deWalk, Term.numCalls, Val.numCalls_deWalk v I, Term.numCalls_deWalk b]
  | _, _, _, _, _, _, .letE u c b, I => by
      simp only [Term.deWalk, Term.numCalls, Comp.numCalls_deWalk c I, Term.numCalls_deWalk b]
  | _, _, _, _, _, _, .record_casesOn us n b, I => by
      simp only [Term.deWalk, Term.numCalls]; exact Term.numCalls_deWalk b _
  | _, _, _, _, _, _, .branch br, I => by
      simp only [Term.deWalk, Term.numCalls]; exact Branch.numCalls_deWalk br I
  | _, _, _, _, _, _, .jump _ _, _ => rfl
  termination_by structural _ _ _ _ _ _ x => x
theorem Branch.numCalls_deWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → (I : AInfo Δ Φ Γ) →
    (br.deWalk I).numCalls = br.numCalls
  | _, _, _, _, _, _, .ite c t e, I => by
      simp only [Branch.deWalk, Branch.numCalls, Term.numCalls_deWalk t I, Term.numCalls_deWalk e I]
  | _, _, _, _, _, _, .enum_casesOn e bs, I => by
      simp only [Branch.deWalk, Branch.numCalls]
      exact Fin.sumNat_congr _ (fun i => Term.numCalls_deWalk (bs i) I)
  | _, _, _, _, _, _, .union_casesOn e bs, I => by
      simp only [Branch.deWalk, Branch.numCalls]; exact Branches.numCalls_deWalk bs I
  | _, _, _, _, _, _, .join σ u uₓ body main, I => by
      simp only [Branch.deWalk, Branch.numCalls, Term.numCalls_deWalk body,
        Branch.numCalls_deWalk main I]
  termination_by structural _ _ _ _ _ _ x => x
theorem Branches.numCalls_deWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (I : AInfo Δ Φ Γ) → (br.deWalk I).numCalls = br.numCalls
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, I => by
      simp only [Branches.deWalk, Branches.numCalls, Term.numCalls_deWalk b₁,
        Term.numCalls_deWalk b₂]
  | _, _, _, _, _, _, _, _, .cons us b bs, I => by
      simp only [Branches.deWalk, Branches.numCalls, Term.numCalls_deWalk b,
        Branches.numCalls_deWalk bs I]
  termination_by structural _ _ _ _ _ _ _ _ x => x
end

/-- **Replacing the delays that only force another delay keeps the number of calls.** -/
theorem Term.numCalls_delayEta {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} {o : Lvl} (t : Term Δ d Φ Γ τ js o) : t.delayEta.numCalls = t.numCalls :=
  Term.numCalls_deWalk t _

end LeanScript

end
