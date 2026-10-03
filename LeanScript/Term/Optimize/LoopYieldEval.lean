module

public import LeanScript.Term.Optimize.LoopYield
public import LeanScript.Term.Optimize.JoinCtorEval

@[expose] public section

set_option autoImplicit false

/-!
# Writing a loop over the field of its state keeps the value

`Term.loopYield_eval`: `Term.loopYield` (`LeanScript.Term.Optimize.LoopYield`) does not change
the value of a statement, in any environment.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## The pieces -/

/-- The value of the constructor `ix` on `v`, as a value of `τ = union cs`. -/
def CtorIx.injTo {bs : List Bool} {cs : Ctors ks bs} {h : UnionShape bs} {b : Bool}
    {c : Ctor ks b} {τ : Ty ks} (hτ : τ = Ty.union cs (h := h)) (ix : CtorIx cs c)
    (v : DenList (DSig.refDen Δ) c.binds) : Ty.Den Δ τ :=
  hτ ▸ (ix.inject v : Ty.Den Δ (Ty.union cs (h := h)))

theorem CtorIx.sameArgs?_eval {Φ : KCtx ks} {Γ : UCtx ks} {o : Lvl} (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) : {bs : List Bool} → {cs : Ctors ks bs} → {b b' : Bool} → {c : Ctor ks b} →
    {c' : Ctor ks b'} → (ix : CtorIx cs c) → (ix' : CtorIx cs c') →
    (args : Args Δ Φ Γ c'.binds o) → {args' : Args Δ Φ Γ c.binds o} →
    CtorIx.sameArgs? ix ix' args = some args' →
    (ix'.inject (args.eval κ ρ) : Ctors.den (DSig.refDen Δ) cs) = ix.inject (args'.eval κ ρ)
  | _, _, _, _, _, _, .two₁, .two₁, _, _, h => by
      simp only [CtorIx.sameArgs?, Option.some.injEq] at h; subst h; rfl
  | _, _, _, _, _, _, .two₂, .two₂, _, _, h => by
      simp only [CtorIx.sameArgs?, Option.some.injEq] at h; subst h; rfl
  | _, _, _, _, _, _, .head, .head, _, _, h => by
      simp only [CtorIx.sameArgs?, Option.some.injEq] at h; subst h; rfl
  | _, _, _, _, _, _, .tail i, .tail j, args, _, h => by
      simp only [CtorIx.sameArgs?] at h
      show Ctor.inTail _ _ = Ctor.inTail _ _
      rw [CtorIx.sameArgs?_eval κ ρ i j args h]
  | _, _, _, _, _, _, .two₁, .two₂, _, _, h => by simp [CtorIx.sameArgs?] at h
  | _, _, _, _, _, _, .two₂, .two₁, _, _, h => by simp [CtorIx.sameArgs?] at h
  | _, _, _, _, _, _, .head, .tail _, _, _, h => by simp [CtorIx.sameArgs?] at h
  | _, _, _, _, _, _, .tail _, .head, _, _, h => by simp [CtorIx.sameArgs?] at h

theorem Args.one_eval {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    {o : Lvl} → (args : Args Δ Φ Γ [σ] o) →
    ((Args.one args).2.eval κ ρ : Ty.Den Δ σ) = (args.eval κ ρ : DenList (DSig.refDen Δ) [σ])
  | _, .cons _ .nil => rfl

theorem PExpr.ctorField?_eval {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool} {cs : Ctors ks bs}
    {h : UnionShape bs} {σ : Ty ks} (ix : CtorIx cs (.fields (.one σ))) {o : Lvl}
    (e : PExpr Δ Φ Γ (.union cs (h := h)) o) {p : (o' : Lvl) × PExpr Δ Φ Γ σ o'}
    (hp : e.ctorField? ix = some p) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    e.eval κ ρ = ix.inject (p.2.eval κ ρ) := by
  simp only [PExpr.ctorField?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hp
  obtain ⟨⟨b', c', ix', o', args⟩, hl, args', hs, rfl⟩ := hp
  rw [PExpr.unionLit?_eval κ ρ e hl, CtorIx.sameArgs?_eval κ ρ ix ix' args hs]
  exact congrArg ix.inject (Args.one_eval κ ρ args').symm

theorem LoopYield.congr2 {α β γ : Sort _} (f : α → β → γ) {a a' : α} {b b' : β} (ha : a = a')
    (hb : b = b') : f a b = f a' b' := by
  subst ha hb; rfl

theorem Ctor.twoCase_map {E : Ref ks → Type} {a b : Bool} {R R' : Type} (f : R → R')
    (c : Ctor ks a) (d : Ctor ks b) (x : twoT (Ctor.den E c) (Ctor.den E d))
    (k₁ : DenList E c.binds → R) (k₂ : DenList E d.binds → R) :
    f (Ctor.twoCase c d x k₁ k₂) = Ctor.twoCase c d x (fun v => f (k₁ v)) (fun v => f (k₂ v)) := by
  cases c <;> cases d <;> simp only [Ctor.twoCase] <;> split <;> rfl

theorem Ctor.consCase_map {E : Ref ks → Type} {a : Bool} {R R' RT : Type} (f : R → R')
    (c : Ctor ks a) (x : consT (Ctor.den E c) RT) (k₁ : DenList E c.binds → R) (k₂ : RT → R) :
    f (Ctor.consCase c x k₁ k₂) = Ctor.consCase c x (fun v => f (k₁ v)) (fun r => f (k₂ r)) := by
  cases c <;> simp only [Ctor.consCase] <;> split <;> rfl

/-! ## Answers `ix e` written `e` -/

section UnCtor
variable {bs : List Bool} {cs : Ctors ks bs} {h : UnionShape bs} {σ : Ty ks}
  (ix : CtorIx cs (.fields (.one σ))) {τ : Ty ks} (hτ : τ = Ty.union cs (h := h))

/-- The join points of the rewritten statement, put through the constructor `ix`, are those of
    the original. -/
def JEnv.InjRel {js : JCtx ks} (jκ : JEnv Δ τ js) (jκ' : JEnv Δ σ js) : Prop :=
  ∀ {σ' : Ty ks} (j : JVar js σ') (v : Ty.Den Δ σ'), jκ.get j v = CtorIx.injTo hτ ix (jκ'.get j v)

mutual
theorem Term.unCtor_eval : {D : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {js : JCtx ks} →
    {o : Lvl} → (t : Term Δ D Φ Γ τ js o) → {p : (o' : Lvl) × Term Δ D Φ Γ σ js o'} →
    t.unCtor ix hτ = some p → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
    (jκ' : JEnv Δ σ js) → JEnv.InjRel ix hτ jκ jκ' →
    t.eval κ ρ jκ = CtorIx.injTo hτ ix (p.2.eval κ ρ jκ')
  | _, _, _, _, _, .ret e, _, hp, κ, ρ, _, _, _ => by
      simp only [Term.unCtor, Option.map_eq_some_iff] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      subst hτ
      exact PExpr.ctorField?_eval ix _ hq κ ρ
  | _, _, _, _, _, .letV u v b, _, hp, κ, ρ, jκ, jκ', hj => by
      simp only [Term.unCtor, Option.map_eq_some_iff] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      exact Term.unCtor_eval b hq _ ρ jκ jκ' hj
  | _, _, _, _, _, .letE u c b, _, hp, κ, ρ, jκ, jκ', hj => by
      simp only [Term.unCtor, Option.map_eq_some_iff] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      exact Term.unCtor_eval b hq κ _ jκ jκ' hj
  | _, _, _, _, _, .record_casesOn us n b, _, hp, κ, ρ, jκ, jκ', hj => by
      simp only [Term.unCtor, Option.map_eq_some_iff] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      exact Term.unCtor_eval b hq κ _ jκ jκ' hj
  | _, _, _, _, _, .branch br, _, hp, κ, ρ, jκ, jκ', hj => by
      simp only [Term.unCtor, Option.map_eq_some_iff] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      exact Branch.unCtor_eval br hq κ ρ jκ jκ' hj
  | _, _, _, _, _, .jump j e, _, hp, κ, ρ, jκ, jκ', hj => by
      simp only [Term.unCtor, Option.some.injEq] at hp
      subst hp
      exact hj j _
  termination_by structural _ _ _ _ _ x => x
theorem Branch.unCtor_eval : {D : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {js : JCtx ks} →
    {ℓ : Nat} → (br : Branch Δ D Φ Γ τ js ℓ) → {p : (ℓ' : Nat) × Branch Δ D Φ Γ σ js ℓ'} →
    br.unCtor ix hτ = some p → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
    (jκ' : JEnv Δ σ js) → JEnv.InjRel ix hτ jκ jκ' →
    br.eval κ ρ jκ = CtorIx.injTo hτ ix (p.2.eval κ ρ jκ')
  | _, _, _, _, _, .ite c t e, _, hp, κ, ρ, jκ, jκ', hj => by
      simp only [Branch.unCtor, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at hp
      obtain ⟨t', ht, e', he, rfl⟩ := hp
      simp only [Branch.eval]
      rcases Bool.eq_false_or_eq_true (c.eval κ ρ) with hc | hc <;> simp only [hc]
      · exact Term.unCtor_eval t ht κ ρ jκ jκ' hj
      · exact Term.unCtor_eval e he κ ρ jκ jκ' hj
  | _, _, _, _, _, .enum_casesOn e bs, _, hp, κ, ρ, jκ, jκ', hj => by
      simp only [Branch.unCtor, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at hp
      obtain ⟨g, hg, rfl⟩ := hp
      simp only [Branch.eval]
      exact Term.unCtor_eval _ (Fin.optAll_eq_some hg _) κ ρ jκ jκ' hj
  | _, _, _, _, _, .union_casesOn e bs, _, hp, κ, ρ, jκ, jκ', hj => by
      simp only [Branch.unCtor, Option.map_eq_some_iff] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      simp only [Branch.eval]
      exact Branches.unCtor_eval bs hq κ ρ jκ jκ' hj _
  | _, _, _, _, _, .join σ' u uₓ body main, _, hp, κ, ρ, jκ, jκ', hj => by
      simp only [Branch.unCtor, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at hp
      obtain ⟨b', hb, m', hm, rfl⟩ := hp
      simp only [Branch.eval]
      apply Branch.unCtor_eval main hm κ ρ _ _
      intro σ'' j v
      cases j with
      | head => simp only [JEnv.get_cons_head]; exact Term.unCtor_eval body hb κ _ jκ jκ' hj
      | tail j => simp only [JEnv.get_cons_tail]; exact hj j v
  termination_by structural _ _ _ _ _ x => x
theorem Branches.unCtor_eval : {D : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs' : List Bool} →
    {cs' : Ctors ks bs'} → {js : JCtx ks} → {o : Lvl} → (br : Branches Δ D Φ Γ cs' τ js o) →
    {p : (o' : Lvl) × Branches Δ D Φ Γ cs' σ js o'} → br.unCtor ix hτ = some p →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → (jκ' : JEnv Δ σ js) →
    JEnv.InjRel ix hτ jκ jκ' →
    ∀ x, br.eval κ ρ jκ x = CtorIx.injTo hτ ix (p.2.eval κ ρ jκ' x)
  | _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, _, hp, κ, ρ, jκ, jκ', hj, x => by
      simp only [Branches.unCtor, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at hp
      obtain ⟨b₁', h₁, b₂', h₂, rfl⟩ := hp
      simp only [Branches.eval]
      exact (LoopYield.congr2 (Ctor.twoCase _ _ x)
        (funext fun v => Term.unCtor_eval b₁ h₁ κ _ jκ jκ' hj)
        (funext fun v => Term.unCtor_eval b₂ h₂ κ _ jκ jκ' hj)).trans
        (Ctor.twoCase_map (CtorIx.injTo hτ ix) _ _ x _ _).symm
  | _, _, _, _, _, _, _, .cons us b bs, _, hp, κ, ρ, jκ, jκ', hj, x => by
      simp only [Branches.unCtor, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at hp
      obtain ⟨b', h₁, bs', h₂, rfl⟩ := hp
      simp only [Branches.eval]
      exact (LoopYield.congr2 (Ctor.consCase _ x)
        (funext fun v => Term.unCtor_eval b h₁ κ _ jκ jκ' hj)
        (funext fun r => Branches.unCtor_eval bs h₂ κ ρ jκ jκ' hj r)).trans
        (Ctor.consCase_map (CtorIx.injTo hτ ix) _ x _ _).symm
  termination_by structural _ _ _ _ _ _ _ x => x
end

end UnCtor

/-! ## The step of the loop -/

theorem CtorIx.cast_injTo {bs : List Bool} {cs : Ctors ks bs} {h : UnionShape bs} {b : Bool}
    {c : Ctor ks b} {τ : Ty ks} (hτ : τ = Ty.union cs (h := h)) (ix : CtorIx cs c)
    (v : DenList (DSig.refDen Δ) c.binds) :
    cast (congrArg (Ty.Den Δ) hτ) (CtorIx.injTo hτ ix v) = ix.inject v := by
  subst hτ; rfl

theorem USub.Agree.yieldStep {Φ : KCtx ks} {X : UCtx ks} {τ σ : Ty ks} {u₁ u₂ : Usage01ω}
    {D : Nat} (us : List Usage01ω) (κ : KEnv Δ Φ) (ρ : UEnv Δ X) (x : Ty.Den Δ τ) (k : Nat)
    (v : Ty.Den Δ σ) :
    USub.Agree (USub.yieldStep (u₁ := u₁) us) κ
      (Tuple.append (UEnv.ofDL D [σ] us v)
        (Tuple.cons x (Tuple.cons k ρ) : UEnv Δ (⟨τ, u₁, D⟩ :: ⟨.nat, u₂, D⟩ :: X)))
      (Tuple.cons v (Tuple.cons k ρ) : UEnv Δ (⟨σ, .many, D⟩ :: ⟨.nat, u₂, D⟩ :: X)) := by
  exact USub.Agree.ofArgs
    (s := USub.consOpt Option.none (USub.wkU (USub.ofRen ULRen.idL) ⟨σ, .many, D⟩))
    (USub.Agree.consOpt (USub.Agree.wkU (USub.Agree.ofRen
      (ULRen.Agree.idL (Tuple.cons k ρ : UEnv Δ (⟨.nat, u₂, D⟩ :: X)))) ⟨σ, .many, D⟩ v)
      Option.none x (fun _ h => nomatch h)) D [σ] us
    (Args.cons (PExpr.neu (Neu.var (UVar.head (u := .many) (by decide)))) Args.nil)

theorem Term.yieldStep?_eval {D : Nat} {Φ : KCtx ks} {X : UCtx ks} {τ : Ty ks}
    {u₁ u₂ : Usage01ω} {o : Lvl}
    (pick : {bs : List Bool} → (cs : Ctors ks bs) → (h : UnionShape bs) →
      τ = Ty.union cs (h := h) → Option ((σ : Ty ks) × CtorIx cs (.fields (.one σ))))
    (t : Term Δ D Φ (⟨τ, u₁, D⟩ :: ⟨.nat, u₂, D⟩ :: X) τ [] o) {Y : YieldStep Δ D Φ X τ u₂}
    (hY : t.yieldStep? pick = some Y) (κ : KEnv Δ Φ) (ρ : UEnv Δ X) (v : Ty.Den Δ Y.σ)
    (k : Nat) :
    t.eval κ (Tuple.cons (CtorIx.injTo Y.hτ Y.ix v) (Tuple.cons k ρ)) PUnit.unit =
      CtorIx.injTo Y.hτ Y.ix (Y.step.eval κ (Tuple.cons v (Tuple.cons k ρ)) PUnit.unit) := by
  unfold Term.yieldStep? at hY
  split at hY
  · rename_i bs cs h hτ o' brs hC
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hY
    obtain ⟨⟨σ, ix⟩, _, arm, harm, step, hstep, rfl⟩ := hY
    refine (Term.caseJoin?_eval t hC κ _ _ _).trans ?_
    simp only [CaseJoin.sem]
    dsimp only at v ⊢
    have e1 : cast (congrArg (Ty.Den Δ) hτ) (CtorIx.injTo hτ ix v) = ix.inject v :=
      CtorIx.cast_injTo hτ ix v
    refine (congrArg (brs.eval κ _ PUnit.unit) e1).trans ?_
    refine (Branches.select_eval brs ix κ _ _ v).trans ?_
    refine (Term.subst_eval (KLRen.Agree.id κ) (USub.Agree.yieldStep _ κ ρ _ k v)
      (JRen.Agree.id _) _ harm).symm.trans ?_
    exact Term.unCtor_eval ix hτ arm.2 hstep κ _ _ _ (fun j _ => nomatch j)
  · cases hY

theorem Body.yieldStep?_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {u₁ u₂ : Usage01ω} {o : Lvl}
    (pick : {bs : List Bool} → (cs : Ctors ks bs) → (h : UnionShape bs) →
      τ = Ty.union cs (h := h) → Option ((σ : Ty ks) × CtorIx cs (.fields (.one σ))))
    (s : Body Δ d Φ Γ [⟨τ, u₁, d + 1⟩, ⟨.nat, u₂, d + 1⟩] τ o) {Y : YieldBody Δ d Φ Γ τ u₂}
    (hY : s.yieldStep? pick = some Y) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (v : Ty.Den Δ Y.σ)
    (k : Nat) :
    s.eval κ ρ (Tuple.cons (CtorIx.injTo Y.hτ Y.ix v) (Tuple.cons k Tuple.nil)) =
      CtorIx.injTo Y.hτ Y.ix (Y.body.eval κ ρ (Tuple.cons v (Tuple.cons k Tuple.nil))) := by
  cases s with
  | closed t =>
      simp only [Body.yieldStep?, Option.map_eq_some_iff] at hY
      obtain ⟨Y', hY', rfl⟩ := hY
      exact Term.yieldStep?_eval (X := []) pick t hY' κ.closedOnly PUnit.unit v k
  | opened t _ =>
      simp only [Body.yieldStep?] at hY
      split at hY
      · rename_i bs cs h hτ σ ix m step hs
        split at hY
        · simp only [Option.some.injEq] at hY
          subst hY
          exact Term.yieldStep?_eval (X := Γ) pick t hs κ ρ v k
        · cases hY
      · cases hY

theorem natIter_map {α β : Type} (f : β → α) (z : β) (s : Nat → α → α) (s' : Nat → β → β)
    (h : ∀ k v, s k (f v) = f (s' k v)) : (n : Nat) → natIter (f z) s n = f (natIter z s' n)
  | 0 => rfl
  | n + 1 => by simp only [natIter]; rw [natIter_map f z s s' h n, h]

theorem PExpr.ctorField?_cast_eval {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool}
    {cs : Ctors ks bs} {h : UnionShape bs} {σ τ : Ty ks} (hτ : τ = Ty.union cs (h := h))
    (ix : CtorIx cs (.fields (.one σ))) {o : Lvl} (z : PExpr Δ Φ Γ τ o)
    {p : (o' : Lvl) × PExpr Δ Φ Γ σ o'}
    (hp : (hτ ▸ z : PExpr Δ Φ Γ (.union cs (h := h)) o).ctorField? ix = some p)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : z.eval κ ρ = CtorIx.injTo hτ ix (p.2.eval κ ρ) := by
  subst hτ
  exact PExpr.ctorField?_eval ix z hp κ ρ

theorem PExpr.ctorOfHead_eval {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool} {cs : Ctors ks bs}
    {h : UnionShape bs} {σ τ : Ty ks} {u : Usage01ω} {L : Nat}
    (ix : CtorIx cs (.fields (.one σ))) (hτ : τ = Ty.union cs (h := h)) (hu : u ≠ .zero)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (v : Ty.Den Δ σ) :
    (PExpr.ctorOfHead (Δ := Δ) (Φ := Φ) (Γ := Γ) (L := L) ix hτ hu).eval κ (Tuple.cons v ρ) =
      CtorIx.injTo hτ ix v := by
  subst hτ
  simp only [PExpr.ctorOfHead, PExpr.eval, Args.eval, Neu.eval, UEnv.get_cons_head]
  rfl

theorem Term.loopYieldLet_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ τ' : Ty ks}
    {js : JCtx ks} {ℓ : Nat} {o' : Lvl} (u : Usage1ω) (c : Comp Δ d Φ Γ τ ℓ)
    (b : Term Δ d Φ (⟨τ, u.toUsage01ω, d⟩ :: Γ) τ' js o') (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (jκ : JEnv Δ τ' js) :
    (Term.loopYieldLet u c b).2.eval κ ρ jκ = (Term.letE u c b).eval κ ρ jκ := by
  cases c with
  | nat_rec n z s hl0 =>
      simp only [Term.loopYieldLet]
      split
      · rfl
      · rename_i Y hY
        dsimp only
        split
        · rfl
        · rename_i a ha
          dsimp only
          split
          · rfl
          · rename_i ℓ' hl
            dsimp only
            split
            · rfl
            · rename_i b' hb
              dsimp only
              by_cases hc : (Comp.nat_rec n a.snd Y.body hl).numCalls + b'.snd.numCalls ≤
                (Comp.nat_rec n z s hl0).numCalls + b.numCalls
              · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
                simp only [Term.eval, Comp.eval]
                have hz := PExpr.ctorField?_cast_eval Y.hτ Y.ix z ha κ ρ
                rw [hz]
                refine Eq.trans ?_ (congrArg (fun X => b.eval κ (Tuple.cons X ρ) jκ)
                  (natIter_map _ _ _ _ (fun k v => Body.yieldStep?_eval _ s hY κ ρ v k) _).symm)
                rw [Term.subst_eval (KLRen.Agree.id κ) (USub.Agree.cons
                  (USub.Agree.wkU (USub.Agree.ofRen (ULRen.Agree.idL ρ)) _ _) _)
                  (JRen.Agree.id jκ) b hb]
                rw [PExpr.ctorOfHead_eval]
              · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
  | _ => rfl

/-! ## A record rebuilt from its fields -/

theorem UEnv.get_eq_of_index : {Γ : UCtx ks} → {τ : Ty ks} → {ℓ ℓ' : Nat} → (ρ : UEnv Δ Γ) →
    (x : UVar Γ τ ℓ) → (y : UVar Γ τ ℓ') → x.index = y.index → ρ.get x = ρ.get y
  | _, _, _, _, _, .head _, .head _, _ => rfl
  | _, _, _, _, ρ, .tail x, .tail y, h => by
      simp only [UVar.index, Nat.add_right_cancel_iff] at h
      exact UEnv.get_eq_of_index ρ.tail x y h
  | _, _, _, _, _, .head _, .tail _, h => by simp [UVar.index] at h
  | _, _, _, _, _, .tail _, .head _, h => by simp [UVar.index] at h

theorem PExpr.var?_eval {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl}
    (e : PExpr Δ Φ Γ τ o) {p : (ℓ : Nat) × UVar Γ τ ℓ} (hp : e.var? = some p)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : e.eval κ ρ = ρ.get p.2 := by
  cases e with
  | neu n =>
      cases n with
      | var x =>
          simp only [PExpr.var?, Option.some.injEq] at hp
          subst hp; rfl
      | _ => simp [PExpr.var?] at hp
  | _ => simp [PExpr.var?] at hp

theorem Args.areVars_eval {Φ : KCtx ks} {Γ : UCtx ks} {d : Nat} (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) : {ts : List (Ty ks)} → {o : Lvl} → (as : Args Δ Φ Γ ts o) →
    (fv : FieldVars Γ d ts) → (v : DenList (DSig.refDen Δ) ts) → as.areVars fv = true →
    fv.Holds ρ v → as.eval κ ρ = v
  | [], _, .nil, .nil, _, _, _ => rfl
  | _ :: _, _, .cons a as, .cons (some y) fv, v, h, hh => by
      simp only [Args.areVars, Bool.and_eq_true] at h
      obtain ⟨h₁, h₂⟩ := h
      obtain ⟨hh₁, hh₂⟩ := hh
      split at h₁
      · rename_i x hx
        simp only [beq_iff_eq] at h₁
        simp only [Args.eval]
        rw [Args.areVars_eval κ ρ as fv v.tail h₂ hh₂, PExpr.var?_eval a hx κ ρ,
          UEnv.get_eq_of_index ρ _ y h₁, hh₁ y rfl, Tuple.cons_head_tail]
      · cases h₁
  | _ :: _, _, .cons _ _, .cons none _, _, h, _ => by simp [Args.areVars] at h

theorem Fields.ofDL_toDL {E : Ref ks → Type} : (fs : Fields ks) → (x : Fields.den E fs) →
    Fields.ofDL fs (Fields.toDL fs x) = x
  | .one _, _ => rfl
  | .cons _ fs, x => by
      simp only [Fields.toDL, Fields.ofDL, Tuple.head_cons, Tuple.tail_cons, Fields.ofDL_toDL fs]
      rfl

theorem Term.recordEta_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} {fs : Fields ks}
    {τ : Ty ks} {js : JCtx ks} {ℓ : Nat} {o' : Lvl} (us : List Usage01ω)
    (n : Neu Δ Φ Γ (.record t fs) ℓ)
    (b : Term Δ d Φ (UCtx.annot d (t :: fs.toList) us ++ Γ) τ js o') (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    (Term.recordEta us n b).2.eval κ ρ jκ = (Term.record_casesOn us n b).eval κ ρ jκ := by
  unfold Term.recordEta
  by_cases h : τ = Ty.record t fs
  · subst h
    rw [dite_eq_left_of_eq_true (eq_true rfl)]
    cases b with
    | ret e =>
        dsimp only
        rcases hl : e.recordLit? with _ | ⟨o₂, args⟩
        · rfl
        · dsimp only
          by_cases hv : args.areVars (FieldVars.ofAnnot Γ d (t :: fs.toList) us) = true
          · rw [ite_eq_left_of_eq_true _ _ (eq_true hv)]
            simp only [Term.eval]
            rw [PExpr.recordLit?_eval κ _ e hl, Args.areVars_eval κ _ args _ _ hv
              (FieldVars.Holds.ofAnnot ρ d _ us _)]
            simp only [Tuple.head_cons, Tuple.tail_cons, Fields.ofDL_toDL]
            rfl
          · rw [ite_eq_right_of_eq_false _ _ (eq_false hv)]
    | _ => rfl
  · rw [dite_eq_right_of_eq_false (eq_false h)]

/-! ## The walk -/

mutual
theorem Val.yieldWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    v.yieldWalk.eval κ ρ = v.eval κ ρ
  | _, _, _, _, _, .lam b, κ, ρ => by
      simp only [Val.yieldWalk, Val.eval]; funext x; rw [Body.yieldWalk_eval b κ ρ]
  | _, _, _, _, _, .thunk_mk b, κ, ρ => by
      simp only [Val.yieldWalk, Val.eval]; rw [Body.yieldWalk_eval b κ ρ]
  | _, _, _, _, _, .lazy_mk b, κ, ρ => by
      simp only [Val.yieldWalk, Val.eval]; rw [Body.yieldWalk_eval b κ ρ]
  | _, _, _, _, _, .record_mk _, _, _ => rfl
  | _, _, _, _, _, .union_mk _ _, _, _ => rfl
  | _, _, _, _, _, .array_mk _, _, _ => rfl
  | _, _, _, _, _, .list_mk _, _, _ => rfl
  | _, _, _, _, _, .data_in _ _ _, _, _ => rfl
  termination_by structural _ _ _ _ _ x => x
theorem Body.yieldWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (vs : UEnv Δ bs) → b.yieldWalk.eval κ ρ vs = b.eval κ ρ vs
  | _, _, _, _, _, _, .closed t, κ, _, _ => by
      simp only [Body.yieldWalk, Body.eval]; exact Term.yieldWalk_eval t _ _ _
  | _, _, _, _, _, _, .opened t _, κ, ρ, vs => by
      simp only [Body.yieldWalk, Body.eval]
      exact Term.keepLvl_eval t _ κ _ _ (Term.yieldWalk_eval t _ _ _)
  termination_by structural _ _ _ _ _ _ x => x
theorem Comp.yieldWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    c.yieldWalk.eval κ ρ = c.eval κ ρ
  | _, _, _, _, _, .app _ _ _, _, _ => rfl
  | _, _, _, _, _, .share _, _, _ => rfl
  | _, _, _, _, _, .nat_rec n z s _, κ, ρ => by
      simp only [Comp.yieldWalk, Comp.eval]
      congr 1; funext k acc; exact Body.yieldWalk_eval s κ ρ _
  | _, _, _, _, _, .array_foldl a z s _, κ, ρ => by
      simp only [Comp.yieldWalk, Comp.eval]
      congr 1; funext acc x; exact Body.yieldWalk_eval s κ ρ _
  | _, _, _, _, _, .data_rec b ρt us brs j e _, κ, ρ => by
      simp only [Comp.yieldWalk, Comp.eval]
      congr 1; funext i x; exact Body.yieldWalk_eval (brs i) κ ρ _
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, κ, ρ => by
      simp only [Comp.yieldWalk, Comp.eval]
      congr 1; funext i x; exact Body.yieldWalk_eval (brs i) κ ρ _
  | _, _, _, _, _, .thunk_force _, _, _ => rfl
  | _, _, _, _, _, .lazy_force _, _, _ => rfl
  termination_by structural _ _ _ _ _ x => x
theorem Term.yieldWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
    t.yieldWalk.2.eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, .ret _, _, _, _ => rfl
  | _, _, _, _, _, _, .letV u v b, κ, ρ, jκ => by
      simp only [Term.yieldWalk, Term.eval, Val.yieldWalk_eval v κ ρ]
      exact Term.yieldWalk_eval b _ ρ jκ
  | _, _, _, _, _, _, .letE u c b, κ, ρ, jκ => by
      simp only [Term.yieldWalk]
      rw [Term.loopYieldLet_eval]
      simp only [Term.eval, Comp.yieldWalk_eval c κ ρ]
      exact Term.yieldWalk_eval b κ _ jκ
  | _, _, _, _, _, _, .record_casesOn us n b, κ, ρ, jκ => by
      simp only [Term.yieldWalk]
      rw [Term.recordEta_eval]
      simp only [Term.eval]
      exact Term.yieldWalk_eval b κ _ jκ
  | _, _, _, _, _, _, .branch br, κ, ρ, jκ => by
      simp only [Term.yieldWalk, Term.eval]
      exact Branch.yieldWalk_eval br κ ρ jκ
  | _, _, _, _, _, _, .jump _ _, _, _, _ => rfl
  termination_by structural _ _ _ _ _ _ x => x
theorem Branch.yieldWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
    br.yieldWalk.2.eval κ ρ jκ = br.eval κ ρ jκ
  | _, _, _, _, _, _, .ite c t e, κ, ρ, jκ => by
      simp only [Branch.yieldWalk, Branch.eval, Term.yieldWalk_eval t κ ρ jκ, Term.yieldWalk_eval e κ ρ jκ]
  | _, _, _, _, _, _, .enum_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.yieldWalk, Branch.eval]; exact Term.yieldWalk_eval _ κ ρ jκ
  | _, _, _, _, _, _, .union_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.yieldWalk, Branch.eval]
      exact Branches.yieldWalk_eval bs κ ρ jκ _
  | _, _, _, _, _, _, .join σ u uₓ body main, κ, ρ, jκ => by
      simp only [Branch.yieldWalk]
      simp only [Branch.eval, Branch.yieldWalk_eval main κ ρ, Term.yieldWalk_eval body κ]
  termination_by structural _ _ _ _ _ _ x => x
theorem Branches.yieldWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (jκ : JEnv Δ τ js) → ∀ x, br.yieldWalk.2.eval κ ρ jκ x = br.eval κ ρ jκ x
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, κ, ρ, jκ, x => by
      simp only [Branches.yieldWalk, Branches.eval, Term.yieldWalk_eval b₁ κ, Term.yieldWalk_eval b₂ κ]
  | _, _, _, _, _, _, _, _, .cons us b bs, κ, ρ, jκ, x => by
      simp only [Branches.yieldWalk, Branches.eval, Term.yieldWalk_eval b κ, Branches.yieldWalk_eval bs κ ρ jκ]
  termination_by structural _ _ _ _ _ _ _ _ x => x
end

/-- **Writing the loops whose state is always the same constructor over its field does not
    change the value of a statement**, in any environment. -/
theorem Term.loopYield_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {o : Lvl} (t : Term Δ d Φ Γ τ js o) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    t.loopYield.eval κ ρ jκ = t.eval κ ρ jκ :=
  Term.keepLvl_eval t _ κ ρ jκ (Term.yieldWalk_eval t κ ρ jκ)

end LeanScript

end
