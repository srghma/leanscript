module

public import LeanScript.Term.Optimize.InlineRet
public import LeanScript.Term.Optimize.InlineEval
public import LeanScript.Term.Optimize.InlineBlockEval

@[expose] public section

set_option autoImplicit false

/-!
# Inlining in tail position preserves the value

`Term.inlineRet_eval`: the walk of `LeanScript.Term.Optimize.InlineRet` does not change the
value of a statement, in any environment.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## The pieces -/

theorem Term.keepLvl_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {o : Lvl} (t : Term Δ d Φ Γ τ js o) (r : (o' : Lvl) × Term Δ d Φ Γ τ js o')
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) (hr : r.2.eval κ ρ jκ = t.eval κ ρ jκ) :
    (t.keepLvl r).eval κ ρ jκ = t.eval κ ρ jκ := by
  unfold Term.keepLvl
  split
  · rename_i h
    obtain ⟨o', t'⟩ := r
    simp only at h
    subst h
    exact hr
  · rfl

theorem Comp.answer?_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {ℓ : Nat}
    {I : KInfo Δ Φ} {κ : KEnv Δ Φ} (hI : I.Agree κ) (ρ : UEnv Δ Γ) (c : Comp Δ d Φ Γ σ ℓ)
    {r : (o : Lvl) × PExpr Δ Φ Γ σ o} (h : c.answer? I = some r) :
    r.2.eval κ ρ = c.eval κ ρ := by
  unfold Comp.answer? at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h; rfl
  · rename_i k a hl
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨e, he, ha⟩ := h
    rw [ExprFn.apply_eval (hI k e he) a ρ ha]
    rfl
  · cases h

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

theorem Term.substTail_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {u : Usage01ω}
    {ℓ : Nat} {op : Lvl} (p : PExpr Δ Φ Γ σ op) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} → (b : Term Δ d Φ (⟨σ, u, ℓ⟩ :: Γ) τ js o) →
    (jκ : JEnv Δ τ js) → {r : (o' : Lvl) × Term Δ d Φ Γ τ js o'} → Term.substTail p b = some r →
    r.2.eval κ ρ jκ = b.eval κ (Tuple.cons (p.eval κ ρ) ρ) jκ
  | _, _, _, .ret e, jκ, r, h => by
      simp only [Term.substTail, Option.map_eq_some_iff] at h
      obtain ⟨⟨hh⟩, he, rfl⟩ := h
      subst hh
      simp only [Term.eval]
      rw [PExpr.isHead?_eval κ ρ _ e he]
  | _, _, _, .jump j e, jκ, r, h => by
      simp only [Term.substTail, Option.map_eq_some_iff] at h
      obtain ⟨⟨hh⟩, he, rfl⟩ := h
      subst hh
      simp only [Term.eval]
      rw [PExpr.isHead?_eval κ ρ _ e he]
  | _, _, _, .letV _ _ _, _, _, h => by simp [Term.substTail] at h
  | _, _, _, .letE _ _ _, _, _, h => by simp [Term.substTail] at h
  | _, _, _, .record_casesOn _ _ _, _, _, h => by simp [Term.substTail] at h
  | _, _, _, .branch _, _, _, h => by simp [Term.substTail] at h

theorem PExpr.shareAny?_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) : {o : Lvl} → (p : PExpr Δ Φ Γ τ o) →
    {r : (ℓ : Nat) × Comp Δ d Φ Γ τ ℓ} → p.shareAny? = some r → r.2.eval κ ρ = p.eval κ ρ := by
  intro o p r h
  unfold PExpr.shareAny? at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h; rfl
  · cases h

/-- `I` describes the values of `κ`. -/
def RInfo.Agree {Φ : KCtx ks} (I : RInfo Δ Φ) (κ : KEnv Δ Φ) : Prop :=
  I.e.Agree κ ∧ I.b.Agree κ

theorem RInfo.Agree.empty {Φ : KCtx ks} (κ : KEnv Δ Φ) : (RInfo.empty : RInfo Δ Φ).Agree κ :=
  ⟨KInfo.Agree.empty κ, BInfo.Agree.empty κ⟩

theorem RInfo.Agree.toClosed {Φ : KCtx ks} {I : RInfo Δ Φ} {κ : KEnv Δ Φ} (hI : I.Agree κ) :
    I.toClosed.Agree (KEnv.closedOnly κ) :=
  ⟨KInfo.Agree.toClosed hI.1, BInfo.Agree.toClosed hI.2⟩

theorem Val.blockFnIf_sem {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {ty : Ty ks} {o : Lvl}
    (u : Usage1ω) (v : Val Δ d Φ Γ ty o) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) {f : BlockFn Δ Φ ty}
    (h : v.blockFnIf u = some f) : f.Sem κ (v.eval κ ρ) := by
  cases u with
  | one => exact Val.blockFn?_sem v κ ρ h
  | many => simp [Val.blockFnIf] at h

theorem RInfo.Agree.cons {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {o : Lvl}
    {I : RInfo Δ Φ} {κ : KEnv Δ Φ} (hI : I.Agree κ) (u : Usage1ω) (v : Val Δ d Φ Γ σ o)
    (ρ : UEnv Δ Γ) :
    (RInfo.cons u v I).Agree (Tuple.cons (v.eval κ ρ) κ : KEnv Δ (⟨σ, u, o, true⟩ :: Φ)) :=
  ⟨KInfo.Agree.cons hI.1 (fun _ hf => Val.exprFn?_sem v κ ρ hf),
    BInfo.Agree.cons hI.2 (fun _ hf => Val.blockFnIf_sem u v κ ρ hf)⟩

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

theorem Comp.blockCall?_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {ℓ : Nat}
    {js : JCtx ks} {B : BInfo Δ Φ} {κ : KEnv Δ Φ} (hB : B.Agree κ) (ρ : UEnv Δ Γ)
    (jκ : JEnv Δ σ js) (c : Comp Δ d Φ Γ σ ℓ) {r : (o : Lvl) × Term Δ d Φ Γ σ js o}
    (h : c.blockCall? B = some r) : r.2.eval κ ρ jκ = c.eval κ ρ := by
  unfold Comp.blockCall? at h
  split at h
  · rename_i k a hl
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨f, hf, m, hm, h⟩ := h
    split at h
    · rw [BlockFn.applyNeu_eval (hB k f hf) m.2 ρ jκ h, PExpr.toNeu?_eval κ ρ a hm]
      rfl
    · cases h
  · cases h

theorem Term.blockLetE_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks}
    {ℓ : Nat} {o' : Lvl} {B : BInfo Δ Φ} {κ : KEnv Δ Φ} (hB : B.Agree κ) (u : Usage1ω)
    (c : Comp Δ d Φ Γ σ ℓ) (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o')
    (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) {r : (o : Lvl) × Term Δ d Φ Γ τ js o}
    (h : Term.blockLetE B u c b = some r) :
    r.2.eval κ ρ jκ = (Term.letE u c b).eval κ ρ jκ := by
  unfold Term.blockLetE at h
  split at h
  · rename_i hh hb
    obtain ⟨hh⟩ := hh
    subst hh
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    simp only [Term.eval]
    rw [Term.retHead?_eval b hb κ ρ _ jκ]
    exact Comp.blockCall?_eval hB ρ jκ c hr'
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨r', hr', h⟩ := h
    rw [Term.bindRet_eval r'.2 b κ ρ jκ h, Comp.blockCall?_eval (js := []) hB ρ PUnit.unit c hr']
    rfl

theorem Term.retLetE_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks}
    {ℓ : Nat} {o' : Lvl} {I : RInfo Δ Φ} {κ : KEnv Δ Φ} (hI : I.Agree κ) (u : Usage1ω)
    (c : Comp Δ d Φ Γ σ ℓ) (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o')
    (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    (Term.retLetE I u c b).2.eval κ ρ jκ = (Term.letE u c b).eval κ ρ jκ := by
  unfold Term.retLetE
  cases hb : b.rename KRen.id URen.drop JRen.id with
  | some b' =>
      simp only [Term.eval]
      exact Term.rename_eval (KRen.Agree.id _) (URen.Agree.drop _ ρ) (JRen.Agree.id _) b hb
  | none =>
      simp only
      cases hc : c.answer? I.e with
      | none =>
          simp only
          cases hbl : Term.blockLetE I.b u c b with
          | none => rfl
          | some r => exact Term.blockLetE_eval hI.2 u c b ρ jκ hbl
      | some r =>
          obtain ⟨op, p⟩ := r
          have hp := Comp.answer?_eval hI.1 ρ c hc
          simp only
          cases hs : Term.substTail p b with
          | some r =>
              simp only
              rw [Term.substTail_eval p κ ρ b jκ hs, hp]
              rfl
          | none =>
              simp only
              cases hsh : p.shareAny? (d := d) with
              | none => rfl
              | some r =>
                  obtain ⟨ℓ', c'⟩ := r
                  simp only [Term.eval]
                  rw [PExpr.shareAny?_eval κ ρ p hsh, hp]

theorem Term.retLetV_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks}
    {o o' : Lvl} (u : Usage1ω) (v : Val Δ d Φ Γ σ o) (b : Term Δ d (⟨σ, u, o, true⟩ :: Φ) Γ τ js o')
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    (Term.retLetV u v b).2.eval κ ρ jκ = (Term.letV u v b).eval κ ρ jκ := by
  unfold Term.retLetV
  split
  · rename_i b' hb
    simp only [Term.eval]
    exact Term.rename_eval (KRen.Agree.drop _ κ) (URen.Agree.id _) (JRen.Agree.id _) b hb
  · rfl

/-! ## The walk -/

mutual
theorem Val.retWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → (I : RInfo Δ Φ) → (κ : KEnv Δ Φ) → I.Agree κ →
    (ρ : UEnv Δ Γ) → (v.retWalk I).eval κ ρ = v.eval κ ρ
  | _, _, _, _, _, .lam b, I, κ, hI, ρ => by
      simp only [Val.retWalk, Val.eval]; funext x; rw [Body.retWalk_eval b I κ hI ρ]
  | _, _, _, _, _, .thunk_mk b, I, κ, hI, ρ => by
      simp only [Val.retWalk, Val.eval]; rw [Body.retWalk_eval b I κ hI ρ]
  | _, _, _, _, _, .lazy_mk b, I, κ, hI, ρ => by
      simp only [Val.retWalk, Val.eval]; rw [Body.retWalk_eval b I κ hI ρ]
  | _, _, _, _, _, .record_mk _, _, _, _, _ => rfl
  | _, _, _, _, _, .union_mk _ _, _, _, _, _ => rfl
  | _, _, _, _, _, .array_mk _, _, _, _, _ => rfl
  | _, _, _, _, _, .list_mk _, _, _, _, _ => rfl
  | _, _, _, _, _, .data_in _ _ _, _, _, _, _ => rfl
  termination_by structural _ _ _ _ _ x => x
theorem Body.retWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (I : RInfo Δ Φ) → (κ : KEnv Δ Φ) → I.Agree κ →
    (ρ : UEnv Δ Γ) → (vs : UEnv Δ bs) → (b.retWalk I).eval κ ρ vs = b.eval κ ρ vs
  | _, _, _, _, _, _, .closed t, I, κ, hI, _, _ => by
      simp only [Body.retWalk, Body.eval]; exact Term.retWalk_eval t _ _ hI.toClosed _ _
  | _, _, _, _, _, _, .opened t _, I, κ, hI, ρ, vs => by
      simp only [Body.retWalk, Body.eval]
      exact Term.keepLvl_eval t _ κ _ _ (Term.retWalk_eval t _ _ hI _ _)
  termination_by structural _ _ _ _ _ _ x => x
theorem Comp.retWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (I : RInfo Δ Φ) → (κ : KEnv Δ Φ) → I.Agree κ →
    (ρ : UEnv Δ Γ) → (c.retWalk I).eval κ ρ = c.eval κ ρ
  | _, _, _, _, _, .app _ _ _, _, _, _, _ => rfl
  | _, _, _, _, _, .share _, _, _, _, _ => rfl
  | _, _, _, _, _, .nat_rec n z s _, I, κ, hI, ρ => by
      simp only [Comp.retWalk, Comp.eval]
      congr 1; funext k acc; exact Body.retWalk_eval s I κ hI ρ _
  | _, _, _, _, _, .array_foldl a z s _, I, κ, hI, ρ => by
      simp only [Comp.retWalk, Comp.eval]
      congr 1; funext acc x; exact Body.retWalk_eval s I κ hI ρ _
  | _, _, _, _, _, .data_rec b ρt us brs j e _, I, κ, hI, ρ => by
      simp only [Comp.retWalk, Comp.eval]
      congr 1; funext i x; exact Body.retWalk_eval (brs i) I κ hI ρ _
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, I, κ, hI, ρ => by
      simp only [Comp.retWalk, Comp.eval]
      congr 1; funext i x; exact Body.retWalk_eval (brs i) I κ hI ρ _
  | _, _, _, _, _, .thunk_force _, _, _, _, _ => rfl
  | _, _, _, _, _, .lazy_force _, _, _, _, _ => rfl
  termination_by structural _ _ _ _ _ x => x
theorem Term.retWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → (I : RInfo Δ Φ) →
    (κ : KEnv Δ Φ) → I.Agree κ → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
    (t.retWalk I).2.eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, .ret _, _, _, _, _, _ => rfl
  | _, _, _, _, _, _, .letV u v b, I, κ, hI, ρ, jκ => by
      simp only [Term.retWalk]
      rw [Term.retLetV_eval]
      simp only [Term.eval]
      rw [Term.retWalk_eval b _ _ (hI.cons u (v.retWalk I) ρ) ρ jκ,
        Val.retWalk_eval v I κ hI ρ]
  | _, _, _, _, _, _, .letE u c b, I, κ, hI, ρ, jκ => by
      simp only [Term.retWalk]
      rw [Term.retLetE_eval hI]
      simp only [Term.eval]
      rw [Comp.retWalk_eval c I κ hI ρ, Term.retWalk_eval b I κ hI _ jκ]
  | _, _, _, _, _, _, .record_casesOn us n b, I, κ, hI, ρ, jκ => by
      simp only [Term.retWalk, Term.eval]
      exact Term.retWalk_eval b I κ hI _ jκ
  | _, _, _, _, _, _, .branch br, I, κ, hI, ρ, jκ => by
      simp only [Term.retWalk, Term.eval]
      exact Branch.retWalk_eval br I κ hI ρ jκ
  | _, _, _, _, _, _, .jump _ _, _, _, _, _, _ => rfl
  termination_by structural _ _ _ _ _ _ x => x
theorem Branch.retWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → (I : RInfo Δ Φ) →
    (κ : KEnv Δ Φ) → I.Agree κ → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
    (br.retWalk I).2.eval κ ρ jκ = br.eval κ ρ jκ
  | _, _, _, _, _, _, .ite c t e, I, κ, hI, ρ, jκ => by
      simp only [Branch.retWalk, Branch.eval, Term.retWalk_eval t I κ hI,
        Term.retWalk_eval e I κ hI]
  | _, _, _, _, _, _, .enum_casesOn e bs, I, κ, hI, ρ, jκ => by
      simp only [Branch.retWalk, Branch.eval]; exact Term.retWalk_eval _ I κ hI _ _
  | _, _, _, _, _, _, .union_casesOn e bs, I, κ, hI, ρ, jκ => by
      simp only [Branch.retWalk, Branch.eval]; exact Branches.retWalk_eval bs I κ hI ρ jκ _
  | _, _, _, _, _, _, .join σ u uₓ body main, I, κ, hI, ρ, jκ => by
      simp only [Branch.retWalk, Branch.eval, Branch.retWalk_eval main I κ hI,
        Term.retWalk_eval body I κ hI]
  termination_by structural _ _ _ _ _ _ x => x
theorem Branches.retWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (I : RInfo Δ Φ) → (κ : KEnv Δ Φ) → I.Agree κ →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
      ∀ x, (br.retWalk I).2.eval κ ρ jκ x = br.eval κ ρ jκ x
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, I, κ, hI, ρ, jκ, x => by
      simp only [Branches.retWalk, Branches.eval, Term.retWalk_eval b₁ I κ hI,
        Term.retWalk_eval b₂ I κ hI]
  | _, _, _, _, _, _, _, _, .cons us b bs, I, κ, hI, ρ, jκ, x => by
      simp only [Branches.retWalk, Branches.eval, Term.retWalk_eval b I κ hI,
        Branches.retWalk_eval bs I κ hI]
  termination_by structural _ _ _ _ _ _ _ _ x => x
end

/-- **Inlining in tail position (and dropping dead bindings) does not change the value of a
    statement**, in any environment. -/
theorem Term.inlineRet_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {o : Lvl} (t : Term Δ d Φ Γ τ js o) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    t.inlineRet.eval κ ρ jκ = t.eval κ ρ jκ :=
  Term.keepLvl_eval t _ κ ρ jκ (Term.retWalk_eval t _ κ (RInfo.Agree.empty κ) ρ jκ)

end LeanScript

end
