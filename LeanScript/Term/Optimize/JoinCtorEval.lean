module

public import LeanScript.Term.Optimize.JoinCtor

@[expose] public section

set_option autoImplicit false

/-!
# Writing a join point at its jumps preserves the value

`Term.joinCtor_eval`: the walk of `LeanScript.Term.Optimize.JoinCtor` does not change the
value of a statement, in any environment.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## The pieces -/

theorem Branches.select_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (brs : Branches Δ d Φ Γ cs τ js o) → {b : Bool} → {c : Ctor ks b} → (ix : CtorIx cs c) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
    (v : DenList (DSig.refDen Δ) c.binds) →
    brs.eval κ ρ jκ (ix.inject v) =
      (brs.select ix).2.2.eval κ (Tuple.append (UEnv.ofDL d c.binds (brs.select ix).1 v) ρ) jκ
  | _, _, _, _, _, _, _, _, .two _ _ _ _, _, _, .two₁, _, _, _, _ => by
      exact Ctor.twoCase_inTwo₁ _ _ _ _ _
  | _, _, _, _, _, _, _, _, .two _ _ _ _, _, _, .two₂, _, _, _, _ => by
      exact Ctor.twoCase_inTwo₂ _ _ _ _ _
  | _, _, _, _, _, _, _, _, .cons _ _ _, _, _, .head, _, _, _, _ => by
      exact Ctor.consCase_inHead _ _ _ _
  | _, _, _, _, _, _, _, _, .cons _ _ bs, _, _, .tail ix, κ, ρ, jκ, v => by
      exact (Ctor.consCase_inTail _ _ _ _).trans (Branches.select_eval bs ix κ ρ jκ v)

theorem Neu.isHead?_cast_eval {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {u : Usage01ω} {ℓ : Nat}
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (v : Ty.Den Δ σ) {τ : Ty ks} {ℓ' : Nat}
    (n : Neu Δ Φ (⟨σ, u, ℓ⟩ :: Γ) τ ℓ') {h : PLift (τ = σ)} (hn : n.isHead? = some h) :
    n.eval κ (Tuple.cons v ρ) = cast (congrArg (Ty.Den Δ) h.down.symm) v := by
  cases n with
  | var y =>
      cases y with
      | head _ => simp only [Neu.eval, UEnv.get_cons_head]; rfl
      | tail _ => simp [Neu.isHead?, UVar.isHead?] at hn
  | data_out => simp [Neu.isHead?] at hn
  | cond => simp [Neu.isHead?] at hn
  | extern => simp [Neu.isHead?] at hn

theorem PExpr.recordLit?_eval {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} {fs : Fields ks}
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) {o : Lvl} (e : PExpr Δ Φ Γ (.record t fs) o) {o' : Lvl}
    {args : Args Δ Φ Γ (t :: fs.toList) o'} (he : e.recordLit? = some ⟨o', args⟩) :
    e.eval κ ρ = ((args.eval κ ρ).head, Fields.ofDL fs (args.eval κ ρ).tail) := by
  cases e with
  | record_mk args' =>
      simp only [PExpr.recordLit?, Option.some.injEq, Sigma.mk.injEq] at he
      obtain ⟨rfl, he⟩ := he
      cases he
      rfl
  | _ => simp [PExpr.recordLit?] at he

theorem Term.caseJoin?_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {uₓ : Usage01ω}
    {τ : Ty ks} {js : JCtx ks} {o : Lvl} (t : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o)
    {C : CaseJoin Δ d Φ Γ σ uₓ τ js} (hC : t.caseJoin? = some C) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (jκ : JEnv Δ τ js) (x : Ty.Den Δ σ) : t.eval κ (Tuple.cons x ρ) jκ = C.sem κ ρ jκ x := by
  unfold Term.caseJoin? at hC
  split at hC
  · rename_i n brs
    simp only [Option.map_eq_some_iff] at hC
    obtain ⟨h, hh, rfl⟩ := hC
    simp only [Term.eval, Branch.eval, CaseJoin.sem]
    rw [Neu.isHead?_cast_eval κ ρ x n hh]; rfl
  · rename_i us n b
    simp only [Option.map_eq_some_iff] at hC
    obtain ⟨h, hh, rfl⟩ := hC
    simp only [Term.eval, CaseJoin.sem]
    rw [Neu.isHead?_cast_eval κ ρ x n hh]
  · cases hC

theorem JVar.same?_eq : {js : JCtx ks} → {σ' σ : Ty ks} → (a : JVar js σ') → (b : JVar js σ) →
    {h : PLift (σ' = σ)} → JVar.same? a b = some h → h.down ▸ a = b
  | _, _, _, .head, .head, _, _ => rfl
  | _, _, _, .tail a, .tail b, h, hs => by
      simp only [JVar.same?] at hs
      have := JVar.same?_eq a b hs
      obtain ⟨hh⟩ := h
      subst hh
      simp only at this ⊢
      rw [this]
  | _, _, _, .head, .tail _, _, hs => by simp [JVar.same?] at hs
  | _, _, _, .tail _, .head, _, hs => by simp [JVar.same?] at hs

/-! ## Agreement along the position of a jump -/

/-- The current environments agree with those of the join point along `P`, and the join point
    `P.jv` is the body `C` in the environments of its definition. -/
structure JPos.Agree {d : Nat} {Φ₀ : KCtx ks} {Γ₀ : UCtx ks} {js₀ : JCtx ks} {σ : Ty ks}
    {uₓ : Usage01ω} {τ : Ty ks} {Φ : KCtx ks} {Γ : UCtx ks} {js : JCtx ks}
    (C : CaseJoin Δ d Φ₀ Γ₀ σ uₓ τ js₀) (P : JPos Φ₀ Γ₀ js₀ σ Φ Γ js) (κ₀ : KEnv Δ Φ₀)
    (ρ₀ : UEnv Δ Γ₀) (jκ₀ : JEnv Δ τ js₀) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    Prop where
  hk : KLRen.Agree P.rk κ₀ κ
  hu : ULRen.Agree P.ru ρ₀ ρ
  hj : JRen.Agree P.rj jκ₀ jκ
  hv : ∀ x, jκ.get P.jv x = C.sem κ₀ ρ₀ jκ₀ x

section Agree
variable {d : Nat} {Φ₀ : KCtx ks} {Γ₀ : UCtx ks} {js₀ : JCtx ks} {σ : Ty ks} {uₓ : Usage01ω}
  {τ : Ty ks} {C : CaseJoin Δ d Φ₀ Γ₀ σ uₓ τ js₀} {κ₀ : KEnv Δ Φ₀} {ρ₀ : UEnv Δ Γ₀}
  {jκ₀ : JEnv Δ τ js₀} {Φ : KCtx ks} {Γ : UCtx ks} {js : JCtx ks}
  {P : JPos Φ₀ Γ₀ js₀ σ Φ Γ js} {κ : KEnv Δ Φ} {ρ : UEnv Δ Γ} {jκ : JEnv Δ τ js}

theorem JPos.Agree.wkK (hP : JPos.Agree C P κ₀ ρ₀ jκ₀ κ ρ jκ) (b : KBinder ks)
    (v : Ty.Den Δ b.ty) :
    JPos.Agree C (P.wkK b) κ₀ ρ₀ jκ₀ (Tuple.cons v κ : KEnv Δ (b :: Φ)) ρ jκ where
  hk := by
    intro _ _ x p h
    simp only [JPos.wkK, Option.map_eq_some_iff] at h
    obtain ⟨q, hq, rfl⟩ := h
    rw [KEnv.get_cons_tail]
    exact hP.hk x q hq
  hu := hP.hu
  hj := hP.hj
  hv := hP.hv

theorem JPos.Agree.wk1 (hP : JPos.Agree C P κ₀ ρ₀ jκ₀ κ ρ jκ) (b : UBinder ks)
    (v : Ty.Den Δ b.ty) :
    JPos.Agree C (P.wk1 b) κ₀ ρ₀ jκ₀ κ (Tuple.cons v ρ : UEnv Δ (b :: Γ)) jκ where
  hk := hP.hk
  hu := by
    intro _ _ x p h
    simp only [JPos.wk1, Option.map_eq_some_iff] at h
    obtain ⟨q, hq, rfl⟩ := h
    rw [UEnv.get_cons_tail]
    exact hP.hu x q hq
  hj := hP.hj
  hv := hP.hv

theorem JPos.Agree.wkN (hP : JPos.Agree C P κ₀ ρ₀ jκ₀ κ ρ jκ) (bs : UCtx ks)
    (vs : UEnv Δ bs) :
    JPos.Agree C (P.wkN bs) κ₀ ρ₀ jκ₀ κ (Tuple.append vs ρ) jκ where
  hk := hP.hk
  hu := by
    intro _ _ x p h
    simp only [JPos.wkN, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨q, hq, y, hy, rfl⟩ := h
    rw [URen.Agree.wkN ρ bs vs _ _ hy]
    exact hP.hu x q hq
  hj := hP.hj
  hv := hP.hv

theorem JPos.Agree.wkJ (hP : JPos.Agree C P κ₀ ρ₀ jκ₀ κ ρ jκ) (b : JBinder ks)
    (f : Ty.Den Δ b.ty → Ty.Den Δ τ) :
    JPos.Agree C (P.wkJ b) κ₀ ρ₀ jκ₀ κ ρ (Tuple.cons f jκ : JEnv Δ τ (b :: js)) where
  hk := hP.hk
  hu := hP.hu
  hj := by
    intro _ x y h
    simp only [JPos.wkJ, Option.map_eq_some_iff] at h
    obtain ⟨z, hz, rfl⟩ := h
    rw [JEnv.get_cons_tail]
    exact hP.hj x z hz
  hv := by
    intro x
    simp only [JPos.wkJ, JEnv.get_cons_tail]
    exact hP.hv x

end Agree

theorem JPos.Agree.init {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {js : JCtx ks} {σ : Ty ks}
    {u : Usage1ω} {uₓ : Usage01ω} {τ : Ty ks} {o : Lvl}
    (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o) {C : CaseJoin Δ d Φ Γ σ uₓ τ js}
    (hC : body.caseJoin? = some C) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    JPos.Agree C (JPos.init (u := u)) κ ρ jκ κ ρ
      (Tuple.cons (fun v => body.eval κ (Tuple.cons v ρ) jκ) jκ :
        JEnv Δ τ (⟨σ, u⟩ :: js)) where
  hk := KLRen.Agree.id κ
  hu := ULRen.Agree.idL ρ
  hj := by
    intro _ x y h
    simp only [JPos.init, Option.some.injEq] at h
    subst h
    rw [JEnv.get_cons_tail]
  hv := by
    intro x
    simp only [JPos.init, JEnv.get_cons_head]
    exact Term.caseJoin?_eval body hC κ ρ jκ x

theorem JPos.jump?_eval {d : Nat} {Φ₀ : KCtx ks} {Γ₀ : UCtx ks} {js₀ : JCtx ks} {σ : Ty ks}
    {uₓ : Usage01ω} {τ : Ty ks} {Φ : KCtx ks} {Γ : UCtx ks} {js : JCtx ks}
    {C : CaseJoin Δ d Φ₀ Γ₀ σ uₓ τ js₀} {P : JPos Φ₀ Γ₀ js₀ σ Φ Γ js} {κ₀ : KEnv Δ Φ₀}
    {ρ₀ : UEnv Δ Γ₀} {jκ₀ : JEnv Δ τ js₀} {κ : KEnv Δ Φ} {ρ : UEnv Δ Γ} {jκ : JEnv Δ τ js}
    (hP : JPos.Agree C P κ₀ ρ₀ jκ₀ κ ρ jκ) {σ' : Ty ks} (j : JVar js σ') {o : Lvl}
    (e : PExpr Δ Φ Γ σ' o) {r : (o' : Lvl) × Term Δ d Φ Γ τ js o'}
    (h : JPos.jump? C P j e = some r) : r.2.eval κ ρ jκ = jκ.get j (e.eval κ ρ) := by
  cases C with
  | union bs cs hsh hσ oC brs =>
    cases hσ
    unfold JPos.jump? at h
    split at h
    · cases h
    · rename_i hh hs
      have hj := JVar.same?_eq j P.jv hs
      obtain ⟨hσ'⟩ := hh
      subst hσ'
      simp only at hj
      rw [hj, hP.hv]
      simp only at h
      split at h
      · cases h
      · rename_i b c ix o' args hl
        have hv := PExpr.unionLit?_eval κ ρ e hl
        have hs : USub.Agree (USub.ofArgs (USub.consOpt (u := uₓ) (L := d)
            (if uₓ.atMostOnce = true then some ⟨o, e⟩ else none) (USub.ofRen P.ru))
            d c.binds (brs.select ix).1 args) κ
            (Tuple.append (UEnv.ofDL d c.binds (brs.select ix).1 (args.eval κ ρ))
              (Tuple.cons (e.eval κ ρ) ρ₀)) ρ := by
          refine USub.Agree.ofArgs (USub.Agree.consOpt (USub.Agree.ofRen hP.hu) _ _ ?_) _ _ _ _
          intro p hp
          split at hp
          · cases hp; rfl
          · cases hp
        rw [Term.subst_eval hP.hk hs hP.hj _ h,
          ← Branches.select_eval brs ix κ₀ (Tuple.cons (e.eval κ ρ) ρ₀) jκ₀ (args.eval κ ρ)]
        simp only [CaseJoin.sem]
        rw [← hv]
        rfl
  | record t fs hσ us oC body =>
    cases hσ
    unfold JPos.jump? at h
    split at h
    · cases h
    · rename_i hh hs
      have hj := JVar.same?_eq j P.jv hs
      obtain ⟨hσ'⟩ := hh
      subst hσ'
      simp only at hj
      rw [hj, hP.hv]
      simp only at h
      split at h
      · cases h
      · rename_i o' args hl
        have hv := PExpr.recordLit?_eval κ ρ e hl
        have hs : USub.Agree (USub.ofArgs (USub.consOpt (u := uₓ) (L := d)
            (if uₓ.atMostOnce = true then some ⟨o, e⟩ else none) (USub.ofRen P.ru))
            d (t :: fs.toList) us args) κ
            (Tuple.append (UEnv.ofDL d (t :: fs.toList) us (args.eval κ ρ))
              (Tuple.cons (e.eval κ ρ) ρ₀)) ρ := by
          refine USub.Agree.ofArgs (USub.Agree.consOpt (USub.Agree.ofRen hP.hu) _ _ ?_) _ _ _ _
          intro p hp
          split at hp
          · cases hp; rfl
          · cases hp
        rw [Term.subst_eval hP.hk hs hP.hj _ h]
        have key : (Tuple.cons (e.eval κ ρ).1 (Fields.toDL fs (e.eval κ ρ).2) :
            DenList (DSig.refDen Δ) (t :: fs.toList)) = args.eval κ ρ := by
          rw [hv]
          simp only [Fields.toDL_ofDL, Tuple.cons_head_tail]
        simp only [CaseJoin.sem, cast_eq]
        rw [key]

theorem JPos.jumpCond?_eval {d : Nat} {Φ₀ : KCtx ks} {Γ₀ : UCtx ks} {js₀ : JCtx ks}
    {σ : Ty ks} {uₓ : Usage01ω} {τ : Ty ks} {Φ : KCtx ks} {Γ : UCtx ks} {js : JCtx ks}
    {C : CaseJoin Δ d Φ₀ Γ₀ σ uₓ τ js₀} {P : JPos Φ₀ Γ₀ js₀ σ Φ Γ js} {κ₀ : KEnv Δ Φ₀}
    {ρ₀ : UEnv Δ Γ₀} {jκ₀ : JEnv Δ τ js₀} {κ : KEnv Δ Φ} {ρ : UEnv Δ Γ} {jκ : JEnv Δ τ js}
    (hP : JPos.Agree C P κ₀ ρ₀ jκ₀ κ ρ jκ) {σ' : Ty ks} (j : JVar js σ') :
    (fuel : Nat) → {o : Lvl} → (e : PExpr Δ Φ Γ σ' o) → {r : (o' : Lvl) × Term Δ d Φ Γ τ js o'} →
    JPos.jumpCond? C P j fuel e = some r → r.2.eval κ ρ jκ = jκ.get j (e.eval κ ρ)
  | 0, _, e, _, h => JPos.jump?_eval hP j e h
  | fuel + 1, _, e, r, h => by
      unfold JPos.jumpCond? at h
      split at h
      · rename_i fuel' _ _ _ c a b heq
        obtain rfl : fuel = fuel' := Nat.succ.inj heq
        split at h
        · rename_i ta tb ha hb
          cases h
          simp only [Term.eval, Branch.eval, PExpr.eval, Neu.eval]
          split
          · exact JPos.jumpCond?_eval hP j fuel a ha
          · exact JPos.jumpCond?_eval hP j fuel b hb
        · cases h
      · exact JPos.jump?_eval hP j _ h

/-! ## Replacing the jumps -/

section Repl
variable {d : Nat} {Φ₀ : KCtx ks} {Γ₀ : UCtx ks} {js₀ : JCtx ks} {σ : Ty ks} {uₓ : Usage01ω}
  {τ : Ty ks} {C : CaseJoin Δ d Φ₀ Γ₀ σ uₓ τ js₀} {κ₀ : KEnv Δ Φ₀} {ρ₀ : UEnv Δ Γ₀}
  {jκ₀ : JEnv Δ τ js₀}

mutual
theorem Term.jcRepl_eval : {Φ : KCtx ks} → {Γ : UCtx ks} → {js : JCtx ks} →
    (P : JPos Φ₀ Γ₀ js₀ σ Φ Γ js) → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → JPos.Agree C P κ₀ ρ₀ jκ₀ κ ρ jκ →
    (t.jcRepl C P).2.eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, .ret _, _, _, _, _ => rfl
  | _, _, _, P, _, .letV u v b, κ, ρ, jκ, hP => by
      simp only [Term.jcRepl, Term.eval]
      exact Term.jcRepl_eval _ b _ ρ jκ (hP.wkK _ _)
  | _, _, _, P, _, .letE u c b, κ, ρ, jκ, hP => by
      simp only [Term.jcRepl, Term.eval]
      exact Term.jcRepl_eval _ b κ _ jκ (hP.wk1 _ _)
  | _, _, _, P, _, .record_casesOn us n b, κ, ρ, jκ, hP => by
      simp only [Term.jcRepl, Term.eval]
      exact Term.jcRepl_eval _ b κ _ jκ (hP.wkN _ _)
  | _, _, _, P, _, .branch br, κ, ρ, jκ, hP => by
      simp only [Term.jcRepl, Term.eval]
      exact Branch.jcRepl_eval P br κ ρ jκ hP
  | _, _, _, P, _, .jump j e, κ, ρ, jκ, hP => by
      simp only [Term.jcRepl]
      cases h : JPos.jumpCond? C P j 8 e with
      | none => rfl
      | some r => exact JPos.jumpCond?_eval hP j 8 e h
  termination_by structural _ _ _ _ _ t => t
theorem Branch.jcRepl_eval : {Φ : KCtx ks} → {Γ : UCtx ks} → {js : JCtx ks} →
    (P : JPos Φ₀ Γ₀ js₀ σ Φ Γ js) → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → JPos.Agree C P κ₀ ρ₀ jκ₀ κ ρ jκ →
    (br.jcRepl C P).2.eval κ ρ jκ = br.eval κ ρ jκ
  | _, _, _, P, _, .ite c t e, κ, ρ, jκ, hP => by
      simp only [Branch.jcRepl, Branch.eval, Term.jcRepl_eval P t κ ρ jκ hP,
        Term.jcRepl_eval P e κ ρ jκ hP]
  | _, _, _, P, _, .enum_casesOn e bs, κ, ρ, jκ, hP => by
      simp only [Branch.jcRepl, Branch.eval]
      exact Term.jcRepl_eval P _ κ ρ jκ hP
  | _, _, _, P, _, .union_casesOn e bs, κ, ρ, jκ, hP => by
      simp only [Branch.jcRepl, Branch.eval]
      exact Branches.jcRepl_eval P bs κ ρ jκ hP _
  | _, _, _, P, _, .join σ' u uₓ' body main, κ, ρ, jκ, hP => by
      simp only [Branch.jcRepl, Branch.eval]
      rw [Branch.jcRepl_eval (P.wkJ _) main κ ρ _ (hP.wkJ _ _)]
      have hf : (fun v => (body.jcRepl C (P.wk1 _)).2.eval κ (Tuple.cons v ρ) jκ) =
          (fun v => body.eval κ (Tuple.cons v ρ) jκ) :=
        funext fun v => Term.jcRepl_eval (P.wk1 _) body κ _ jκ (hP.wk1 _ v)
      rw [hf]
  termination_by structural _ _ _ _ _ t => t
theorem Branches.jcRepl_eval : {Φ : KCtx ks} → {Γ : UCtx ks} → {js : JCtx ks} →
    (P : JPos Φ₀ Γ₀ js₀ σ Φ Γ js) → {bs : List Bool} → {cs : Ctors ks bs} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → JPos.Agree C P κ₀ ρ₀ jκ₀ κ ρ jκ →
    ∀ x, (br.jcRepl C P).2.eval κ ρ jκ x = br.eval κ ρ jκ x
  | _, _, _, P, _, _, _, .two us₁ us₂ b₁ b₂, κ, ρ, jκ, hP, x => by
      simp only [Branches.jcRepl, Branches.eval]
      congr 1
      · funext v; exact Term.jcRepl_eval _ b₁ κ _ jκ (hP.wkN _ _)
      · funext v; exact Term.jcRepl_eval _ b₂ κ _ jκ (hP.wkN _ _)
  | _, _, _, P, _, _, _, .cons us b bs, κ, ρ, jκ, hP, x => by
      simp only [Branches.jcRepl, Branches.eval]
      congr 1
      · funext v; exact Term.jcRepl_eval _ b κ _ jκ (hP.wkN _ _)
      · funext r; exact Branches.jcRepl_eval P bs κ ρ jκ hP r
  termination_by structural _ _ _ _ _ _ _ t => t
end

end Repl

theorem Branch.joinCtor_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {o : Lvl} {ℓ : Nat} (σ : Ty ks) (u : Usage1ω) (uₓ : Usage01ω)
    (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o) (main : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    (Branch.joinCtor σ u uₓ body main).2.eval κ ρ jκ = (Branch.join σ u uₓ body main).eval κ ρ jκ := by
  unfold Branch.joinCtor
  cases hC : body.caseJoin? with
  | none => rfl
  | some C =>
      simp only
      cases hb : (main.jcRepl C JPos.init).2.rename KRen.id URen.id JRen.drop with
      | none => rfl
      | some b =>
          simp only
          by_cases hn : b.numCalls ≤ body.numCalls + main.numCalls
          · rw [ite_eq_left_of_eq_true _ _ (eq_true hn)]
            simp only [Branch.eval]
            rw [Branch.rename_eval (KRen.Agree.id κ) (URen.Agree.id ρ) (JRen.Agree.drop _ jκ) _ hb]
            exact Branch.jcRepl_eval _ main κ ρ _ (JPos.Agree.init body hC κ ρ jκ)
          · rw [ite_eq_right_of_eq_false _ _ (eq_false hn)]

/-! ## A case analysis of a conditional of constructors -/

theorem Term.substFields_eval (d : Nat) {Φ : KCtx ks} {τ : Ty ks} {js : JCtx ks}
    (ts : List (Ty ks)) (us : List Usage01ω) : (fuel : Nat) → {Γ : UCtx ks} → {o oa : Lvl} →
    (t : Term Δ d Φ (UCtx.annot d ts us ++ Γ) τ js o) → (args : Args Δ Φ Γ ts oa) →
    {r : (o' : Lvl) × Term Δ d Φ Γ τ js o'} → Term.substFields d ts us fuel t args = some r →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
    r.2.eval κ ρ jκ = t.eval κ (Tuple.append (UEnv.ofDL d ts us (args.eval κ ρ)) ρ) jκ
  | 0, _, _, _, t, args, _, h, κ, ρ, jκ =>
      Term.subst_eval (KLRen.Agree.id κ)
        (USub.Agree.ofArgs (USub.Agree.ofRen (ULRen.Agree.idL ρ)) d ts us args)
        (JRen.Agree.id jκ) t h
  | fuel + 1, _, _, _, t, args, _, h, κ, ρ, jκ => by
      simp only [Term.substFields] at h
      split at h
      · rename_i r' hs
        cases h
        exact Term.subst_eval (KLRen.Agree.id κ)
          (USub.Agree.ofArgs (USub.Agree.ofRen (ULRen.Agree.idL ρ)) d ts us args)
          (JRen.Agree.id jκ) t hs
      · split at h
        · cases h
        · rename_i τ' ℓn n o'' args' hsf
          split at h
          · cases h
          · rename_i t' hren
            simp only [Option.map_eq_some_iff] at h
            obtain ⟨r', hr', rfl⟩ := h
            have hargs := Args.shareFirst_eval d κ ρ args hsf
            simp only at hargs
            simp only [Term.eval, Comp.eval]
            rw [Term.substFields_eval d ts us fuel t' args' hr', hargs]
            exact Term.rename_eval (KRen.Agree.id κ) (URen.Agree.liftN (URen.Agree.wk1 ρ _) _ _)
              (JRen.Agree.id jκ) t hren

theorem Branches.caseLit?_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool}
    {cs : Ctors ks bs} {h : UnionShape bs} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (brs : Branches Δ d Φ Γ cs τ js o) {o' : Lvl} (e : PExpr Δ Φ Γ (.union cs (h := h)) o')
    {r : (o'' : Lvl) × Term Δ d Φ Γ τ js o''} (hr : brs.caseLit? e = some r)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    r.2.eval κ ρ jκ = brs.eval κ ρ jκ (e.eval κ ρ) := by
  unfold Branches.caseLit? at hr
  split at hr
  · cases hr
  · rename_i b c ix o'' args hl
    rw [Term.substFields_eval d c.binds (brs.select ix).1 _ _ args hr κ ρ jκ,
      PExpr.unionLit?_eval κ ρ e hl, Branches.select_eval]

theorem Branches.caseOf?_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool}
    {cs : Ctors ks bs} {h : UnionShape bs} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (brs : Branches Δ d Φ Γ cs τ js o) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    (fuel : Nat) → {o' : Lvl} → (e : PExpr Δ Φ Γ (.union cs (h := h)) o') →
    {r : (o'' : Lvl) × Term Δ d Φ Γ τ js o''} → brs.caseOf? fuel e = some r →
    r.2.eval κ ρ jκ = brs.eval κ ρ jκ (e.eval κ ρ)
  | 0, _, e, _, hr => Branches.caseLit?_eval brs e hr κ ρ jκ
  | fuel + 1, _, e, r, hr => by
      unfold Branches.caseOf? at hr
      split at hr
      · rename_i fuel' _ _ _ c a b heq
        obtain rfl : fuel = fuel' := Nat.succ.inj heq
        split at hr
        · rename_i ta tb ha hb
          cases hr
          simp only [Term.eval, Branch.eval, PExpr.eval, Neu.eval]
          split
          · exact Branches.caseOf?_eval brs κ ρ jκ fuel a ha
          · exact Branches.caseOf?_eval brs κ ρ jκ fuel b hb
        · cases hr
      · exact Branches.caseLit?_eval brs _ hr κ ρ jκ

theorem Neu.caseCond?_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool}
    {cs : Ctors ks bs} {h : UnionShape bs} {τ : Ty ks} {js : JCtx ks} {o : Lvl} {ℓ : Nat}
    (n : Neu Δ Φ Γ (.union cs (h := h)) ℓ) (brs : Branches Δ d Φ Γ cs τ js o)
    {r : (ℓ' : Nat) × Branch Δ d Φ Γ τ js ℓ'} (hr : n.caseCond? brs = some r)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    r.2.eval κ ρ jκ = brs.eval κ ρ jκ (n.eval κ ρ) := by
  unfold Neu.caseCond? at hr
  split at hr
  · rename_i c a b
    split at hr
    · rename_i ta tb ha hb
      cases hr
      simp only [Branch.eval, Neu.eval]
      split
      · exact Branches.caseOf?_eval brs κ ρ jκ 8 _ ha
      · exact Branches.caseOf?_eval brs κ ρ jκ 8 _ hb
    · cases hr
  · cases hr

theorem Term.underOne_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks}
    {o : Lvl} (us : List Usage01ω) (t : Term Δ d Φ (UCtx.annot d [σ] us ++ Γ) τ js o)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) (v : Ty.Den Δ σ) :
    (Term.underOne us t).2.eval κ (Tuple.cons v ρ) jκ =
      t.eval κ (Tuple.append (UEnv.ofDL d [σ] us (Tuple.cons v PUnit.unit)) ρ) jκ := by
  cases us <;> rfl

theorem CtorIx.twoSecond?_eval {Φ : KCtx ks} {Γ : UCtx ks} {a : Bool} {c₁ : Ctor ks a}
    {σ : Ty ks} (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    {b : Bool} → {c : Ctor ks b} → (ix : CtorIx (.two c₁ (.fields (.one σ))) c) → {o' : Lvl} →
    (args : Args Δ Φ Γ c.binds o') → {r : (o'' : Lvl) × PExpr Δ Φ Γ σ o''} →
    ix.twoSecond? args = some r →
    ix.inject (args.eval κ ρ) =
      CtorIx.inject (cs := .two c₁ (.fields (.one σ))) .two₂ (Tuple.cons (r.2.eval κ ρ) PUnit.unit)
  | _, _, .two₁, _, _, _, hr => nomatch hr
  | _, _, .two₂, _, .cons _ .nil, _, hr => by cases hr; rfl

theorem PExpr.twoSecond?_eval {Φ : KCtx ks} {Γ : UCtx ks} {a : Bool} {c₁ : Ctor ks a}
    {σ : Ty ks} {h : UnionShape [a, true]} (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) {o' : Lvl}
    (e : PExpr Δ Φ Γ (.union (.two c₁ (.fields (.one σ))) (h := h)) o')
    {r : (o'' : Lvl) × PExpr Δ Φ Γ σ o''} (hr : e.twoSecond? = some r) :
    e.eval κ ρ =
      CtorIx.inject (cs := .two c₁ (.fields (.one σ))) .two₂ (Tuple.cons (r.2.eval κ ρ) PUnit.unit) := by
  unfold PExpr.twoSecond? at hr
  cases hl : e.unionLit? with
  | none => rw [hl] at hr; cases hr
  | some l =>
      rw [hl] at hr
      obtain ⟨b, c, ix, o'', args⟩ := l
      rw [PExpr.unionLit?_eval κ ρ e hl]
      exact CtorIx.twoSecond?_eval κ ρ ix args hr

theorem Branches.leafJump?_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {a : Bool}
    {c₁ : Ctor ks a} {σ : Ty ks} {h : UnionShape [a, true]} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (brs : Branches Δ d Φ Γ (.two c₁ (.fields (.one σ))) τ js o) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (jκ : JEnv Δ τ js) (jκ' : JEnv Δ τ (⟨σ, .many⟩ :: js))
    (hj : ∀ v, jκ'.head v = brs.eval κ ρ jκ
      (CtorIx.inject (cs := .two c₁ (.fields (.one σ))) .two₂ (Tuple.cons v PUnit.unit)))
    (ht : jκ'.tail = jκ) {o' : Lvl}
    (e : PExpr Δ Φ Γ (.union (.two c₁ (.fields (.one σ))) (h := h)) o')
    {r : (o'' : Lvl) × Term Δ d Φ Γ τ (⟨σ, .many⟩ :: js) o''} (hr : brs.leafJump? e = some r) :
    r.2.eval κ ρ jκ' = brs.eval κ ρ jκ (e.eval κ ρ) := by
  unfold Branches.leafJump? at hr
  split at hr
  · rename_i x hl
    cases hr
    rw [PExpr.twoSecond?_eval κ ρ e hl]
    exact hj _
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
    obtain ⟨r', hr', t, ht', rfl⟩ := hr
    rw [Term.rename_eval (KRen.Agree.id κ) (URen.Agree.id ρ) (jκ' := jκ') ?_ r'.2 ht',
      Branches.caseLit?_eval brs e hr' κ ρ jκ]
    intro _ x y hxy
    cases hxy
    simp only [JEnv.get, ht]

theorem Branches.joinTree?_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {a : Bool}
    {c₁ : Ctor ks a} {σ : Ty ks} {h : UnionShape [a, true]} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (brs : Branches Δ d Φ Γ (.two c₁ (.fields (.one σ))) τ js o) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (jκ : JEnv Δ τ js) (jκ' : JEnv Δ τ (⟨σ, .many⟩ :: js))
    (hj : ∀ v, jκ'.head v = brs.eval κ ρ jκ
      (CtorIx.inject (cs := .two c₁ (.fields (.one σ))) .two₂ (Tuple.cons v PUnit.unit)))
    (ht : jκ'.tail = jκ) :
    (fuel : Nat) → {o' : Lvl} → (e : PExpr Δ Φ Γ (.union (.two c₁ (.fields (.one σ))) (h := h)) o') →
    {r : (o'' : Lvl) × Term Δ d Φ Γ τ (⟨σ, .many⟩ :: js) o''} → brs.joinTree? fuel e = some r →
    r.2.eval κ ρ jκ' = brs.eval κ ρ jκ (e.eval κ ρ)
  | 0, _, e, _, hr => Branches.leafJump?_eval brs κ ρ jκ jκ' hj ht e hr
  | fuel + 1, _, e, r, hr => by
      unfold Branches.joinTree? at hr
      split at hr
      · rename_i fuel' _ _ _ c x y heq
        obtain rfl : fuel = fuel' := Nat.succ.inj heq
        split at hr
        · rename_i tx ty hx hy
          cases hr
          simp only [Term.eval, Branch.eval, PExpr.eval, Neu.eval]
          split
          · exact Branches.joinTree?_eval brs κ ρ jκ jκ' hj ht fuel x hx
          · exact Branches.joinTree?_eval brs κ ρ jκ jκ' hj ht fuel y hy
        · cases hr
      · exact Branches.leafJump?_eval brs κ ρ jκ jκ' hj ht _ hr

theorem Branches.caseJoin?_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {a : Bool}
    {c₁ : Ctor ks a} {σ : Ty ks} {h : UnionShape [a, true]} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    {ℓ : Nat} (brs : Branches Δ d Φ Γ (.two c₁ (.fields (.one σ))) τ js o)
    (n : Neu Δ Φ Γ (.union (.two c₁ (.fields (.one σ))) (h := h)) ℓ)
    {r : (ℓ' : Nat) × Branch Δ d Φ Γ τ js ℓ'} (hr : brs.caseJoin? n = some r)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    r.2.eval κ ρ jκ = brs.eval κ ρ jκ (n.eval κ ρ) := by
  unfold Branches.caseJoin? at hr
  split at hr
  · rename_i c x y
    split at hr
    · rename_i tx ty hx hy
      cases hr
      simp only [Branch.eval, Neu.eval]
      have hj : ∀ v, (Tuple.cons (fun v => (Term.underOne (brs.select .two₂).1
          (brs.select .two₂).2.2).2.eval κ (Tuple.cons v ρ) jκ) jκ :
          JEnv Δ τ (⟨σ, .many⟩ :: js)).head v = brs.eval κ ρ jκ
          (CtorIx.inject (cs := .two c₁ (.fields (.one σ))) .two₂ (Tuple.cons v PUnit.unit)) := by
        intro v
        rw [Tuple.head_cons]
        exact (Term.underOne_eval _ _ κ ρ jκ v).trans
          (Branches.select_eval brs .two₂ κ ρ jκ (Tuple.cons v PUnit.unit)).symm
      split
      · exact Branches.joinTree?_eval _ κ ρ jκ _ hj (Tuple.tail_cons _ _) 8 x hx
      · exact Branches.joinTree?_eval _ κ ρ jκ _ hj (Tuple.tail_cons _ _) 8 y hy
    · cases hr
  · cases hr

theorem Branch.caseJoinAny?_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} {o : Lvl} {ℓ : Nat} : {bs : List Bool} → {cs : Ctors ks bs} →
    {h : UnionShape bs} → (n : Neu Δ Φ Γ (.union cs (h := h)) ℓ) →
    (brs : Branches Δ d Φ Γ cs τ js o) → {r : (ℓ' : Nat) × Branch Δ d Φ Γ τ js ℓ'} →
    Branch.caseJoinAny? n brs = some r → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
    r.2.eval κ ρ jκ = brs.eval κ ρ jκ (n.eval κ ρ)
  | _, .two _ (.fields (.one _)), _, n, brs, _, hr, κ, ρ, jκ =>
      Branches.caseJoin?_eval brs n hr κ ρ jκ
  | _, .two _ (.fields (.cons _ _)), _, _, _, _, hr, _, _, _ => by simp [Branch.caseJoinAny?] at hr
  | _, .two _ .nullary, _, _, _, _, hr, _, _, _ => by simp [Branch.caseJoinAny?] at hr
  | _, .cons _ _, _, _, _, _, hr, _, _, _ => by simp [Branch.caseJoinAny?] at hr

theorem Branch.caseCond_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool}
    {cs : Ctors ks bs} {h : UnionShape bs} {τ : Ty ks} {js : JCtx ks} {o : Lvl} {ℓ : Nat}
    (n : Neu Δ Φ Γ (.union cs (h := h)) ℓ) (brs : Branches Δ d Φ Γ cs τ js o)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    (Branch.caseCond n brs).2.eval κ ρ jκ = brs.eval κ ρ jκ (n.eval κ ρ) := by
  unfold Branch.caseCond
  cases hc : n.caseCond? brs with
  | none => rfl
  | some r =>
      simp only
      by_cases hn : r.2.numCalls ≤ brs.numCalls
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hn)]; exact Neu.caseCond?_eval n brs hc κ ρ jκ
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hn)]
        cases hj : Branch.caseJoinAny? n brs with
        | none => rfl
        | some r' =>
            simp only
            by_cases hn' : r'.2.numCalls ≤ brs.numCalls
            · rw [ite_eq_left_of_eq_true _ _ (eq_true hn')]
              exact Branch.caseJoinAny?_eval n brs hj κ ρ jκ
            · rw [ite_eq_right_of_eq_false _ _ (eq_false hn')]; rfl

theorem Term.recordCaseOf?_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks}
    {fs : Fields ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl} (us : List Usage01ω)
    (body : Term Δ d Φ (UCtx.annot d (t :: fs.toList) us ++ Γ) τ js o)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    (fuel : Nat) → {o' : Lvl} → (e : PExpr Δ Φ Γ (.record t fs) o') →
    {r : (o'' : Lvl) × Term Δ d Φ Γ τ js o''} → Term.recordCaseOf? us body fuel e = some r →
    r.2.eval κ ρ jκ = body.eval κ (Tuple.append (UEnv.ofDL d (t :: fs.toList) us
      (Tuple.cons (e.eval κ ρ).1 (Fields.toDL fs (e.eval κ ρ).2))) ρ) jκ := by
  have lit : ∀ {o' : Lvl} (e : PExpr Δ Φ Γ (.record t fs) o')
      {r : (o'' : Lvl) × Term Δ d Φ Γ τ js o''},
      (match e.recordLit? with
        | some ⟨_, args⟩ =>
            Term.substFields d (t :: fs.toList) us (t :: fs.toList).length body args
        | none => none) = some r →
      r.2.eval κ ρ jκ = body.eval κ (Tuple.append (UEnv.ofDL d (t :: fs.toList) us
        (Tuple.cons (e.eval κ ρ).1 (Fields.toDL fs (e.eval κ ρ).2))) ρ) jκ := by
    intro o' e r hr
    split at hr
    · rename_i o₂ args hl
      have hv := PExpr.recordLit?_eval κ ρ e hl
      rw [Term.substFields_eval d _ us _ body args hr κ ρ jκ]
      have key : (Tuple.cons (e.eval κ ρ).1 (Fields.toDL fs (e.eval κ ρ).2) :
          DenList (DSig.refDen Δ) (t :: fs.toList)) = args.eval κ ρ := by
        rw [hv]
        simp only [Fields.toDL_ofDL, Tuple.cons_head_tail]
      rw [key]
    · cases hr
  intro fuel
  induction fuel with
  | zero =>
      intro o' e r hr
      unfold Term.recordCaseOf? at hr
      exact lit e hr
  | succ fuel ih =>
      intro o' e r hr
      unfold Term.recordCaseOf? at hr
      split at hr
      · rename_i fuel' _ _ _ c a b heq
        obtain rfl : fuel = fuel' := Nat.succ.inj heq
        split at hr
        · rename_i ta tb ha hb
          cases hr
          simp only [Term.eval, Branch.eval, PExpr.eval, Neu.eval]
          split
          · exact ih a ha
          · exact ih b hb
        · cases hr
      · exact lit _ hr

theorem Term.recordCaseCond_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks}
    {fs : Fields ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl} {ℓ : Nat} (us : List Usage01ω)
    (n : Neu Δ Φ Γ (.record t fs) ℓ)
    (body : Term Δ d Φ (UCtx.annot d (t :: fs.toList) us ++ Γ) τ js o)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    (Term.recordCaseCond us n body).2.eval κ ρ jκ = (Term.record_casesOn us n body).eval κ ρ jκ := by
  unfold Term.recordCaseCond
  cases hc : Term.recordCaseOf? us body 8 (.neu n) with
  | none => rfl
  | some r =>
      simp only
      by_cases hn : r.2.numCalls ≤ body.numCalls
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hn), Term.recordCaseOf?_eval us body κ ρ jκ 8 _ hc]
        rfl
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hn)]

theorem Term.caseCondTop_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    (r : (o : Lvl) × Term Δ d Φ Γ τ js o) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    (Term.caseCondTop r).2.eval κ ρ jκ = r.2.eval κ ρ jκ := by
  obtain ⟨o, t⟩ := r
  cases t with
  | branch br =>
      cases br with
      | union_casesOn n brs =>
          simp only [Term.caseCondTop, Term.eval, Branch.eval]
          exact Branch.caseCond_eval _ _ _ _ _
      | _ => rfl
  | record_casesOn us n body =>
      simp only [Term.caseCondTop]
      exact Term.recordCaseCond_eval us n body κ ρ jκ
  | _ => rfl

theorem Term.shareCase_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks}
    {ℓ : Nat} {o' : Lvl} (u : Usage1ω) (c : Comp Δ d Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (jκ : JEnv Δ τ js) :
    (Term.shareCase u c b).2.eval κ ρ jκ = (Term.letE u c b).eval κ ρ jκ := by
  cases c with
  | share n =>
      simp only [Term.shareCase]
      by_cases hc : (u = .one ∧ n.isCond = true ∧ b.isCaseOnHead = true)
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
        cases hs : b.subst (D' := d) KLRen.id (USub.cons ⟨_, .neu n⟩ (USub.ofRen ULRen.idL))
            JRen.id with
        | none => rfl
        | some r =>
            simp only
            by_cases hn : (Term.caseCondTop r).2.numCalls ≤ b.numCalls
            · rw [ite_eq_left_of_eq_true _ _ (eq_true hn), Term.caseCondTop_eval]
              exact Term.subst_eval (KLRen.Agree.id κ)
                (USub.Agree.cons (USub.Agree.ofRen (ULRen.Agree.idL ρ)) _) (JRen.Agree.id jκ) b hs
            · rw [ite_eq_right_of_eq_false _ _ (eq_false hn)]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
  | _ => rfl

/-! ## The walk -/

mutual
theorem Val.jcWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    v.jcWalk.eval κ ρ = v.eval κ ρ
  | _, _, _, _, _, .lam b, κ, ρ => by
      simp only [Val.jcWalk, Val.eval]; funext x; rw [Body.jcWalk_eval b κ ρ]
  | _, _, _, _, _, .thunk_mk b, κ, ρ => by
      simp only [Val.jcWalk, Val.eval]; rw [Body.jcWalk_eval b κ ρ]
  | _, _, _, _, _, .lazy_mk b, κ, ρ => by
      simp only [Val.jcWalk, Val.eval]; rw [Body.jcWalk_eval b κ ρ]
  | _, _, _, _, _, .record_mk _, _, _ => rfl
  | _, _, _, _, _, .union_mk _ _, _, _ => rfl
  | _, _, _, _, _, .array_mk _, _, _ => rfl
  | _, _, _, _, _, .list_mk _, _, _ => rfl
  | _, _, _, _, _, .data_in _ _ _, _, _ => rfl
  termination_by structural _ _ _ _ _ x => x
theorem Body.jcWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (vs : UEnv Δ bs) → b.jcWalk.eval κ ρ vs = b.eval κ ρ vs
  | _, _, _, _, _, _, .closed t, κ, _, _ => by
      simp only [Body.jcWalk, Body.eval]; exact Term.jcWalk_eval t _ _ _
  | _, _, _, _, _, _, .opened t _, κ, ρ, vs => by
      simp only [Body.jcWalk, Body.eval]
      exact Term.keepLvl_eval t _ κ _ _ (Term.jcWalk_eval t _ _ _)
  termination_by structural _ _ _ _ _ _ x => x
theorem Comp.jcWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    c.jcWalk.eval κ ρ = c.eval κ ρ
  | _, _, _, _, _, .app _ _ _, _, _ => rfl
  | _, _, _, _, _, .share _, _, _ => rfl
  | _, _, _, _, _, .nat_rec n z s _, κ, ρ => by
      simp only [Comp.jcWalk, Comp.eval]
      congr 1; funext k acc; exact Body.jcWalk_eval s κ ρ _
  | _, _, _, _, _, .array_foldl a z s _, κ, ρ => by
      simp only [Comp.jcWalk, Comp.eval]
      congr 1; funext acc x; exact Body.jcWalk_eval s κ ρ _
  | _, _, _, _, _, .data_rec b ρt us brs j e _, κ, ρ => by
      simp only [Comp.jcWalk, Comp.eval]
      congr 1; funext i x; exact Body.jcWalk_eval (brs i) κ ρ _
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, κ, ρ => by
      simp only [Comp.jcWalk, Comp.eval]
      congr 1; funext i x; exact Body.jcWalk_eval (brs i) κ ρ _
  | _, _, _, _, _, .thunk_force _, _, _ => rfl
  | _, _, _, _, _, .lazy_force _, _, _ => rfl
  termination_by structural _ _ _ _ _ x => x
theorem Term.jcWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
    t.jcWalk.2.eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, .ret _, _, _, _ => rfl
  | _, _, _, _, _, _, .letV u v b, κ, ρ, jκ => by
      simp only [Term.jcWalk, Term.eval, Val.jcWalk_eval v κ ρ]
      exact Term.jcWalk_eval b _ ρ jκ
  | _, _, _, _, _, _, .letE u c b, κ, ρ, jκ => by
      simp only [Term.jcWalk]
      rw [Term.shareCase_eval]
      simp only [Term.eval, Comp.jcWalk_eval c κ ρ]
      exact Term.jcWalk_eval b κ _ jκ
  | _, _, _, _, _, _, .record_casesOn us n b, κ, ρ, jκ => by
      simp only [Term.jcWalk]
      rw [Term.recordCaseCond_eval]
      simp only [Term.eval]
      exact Term.jcWalk_eval b κ _ jκ
  | _, _, _, _, _, _, .branch br, κ, ρ, jκ => by
      simp only [Term.jcWalk, Term.eval]
      exact Branch.jcWalk_eval br κ ρ jκ
  | _, _, _, _, _, _, .jump _ _, _, _, _ => rfl
  termination_by structural _ _ _ _ _ _ x => x
theorem Branch.jcWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
    br.jcWalk.2.eval κ ρ jκ = br.eval κ ρ jκ
  | _, _, _, _, _, _, .ite c t e, κ, ρ, jκ => by
      simp only [Branch.jcWalk, Branch.eval, Term.jcWalk_eval t κ ρ jκ, Term.jcWalk_eval e κ ρ jκ]
  | _, _, _, _, _, _, .enum_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.jcWalk, Branch.eval]; exact Term.jcWalk_eval _ κ ρ jκ
  | _, _, _, _, _, _, .union_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.jcWalk, Branch.eval]
      rw [Branch.caseCond_eval]; exact Branches.jcWalk_eval bs κ ρ jκ _
  | _, _, _, _, _, _, .join σ u uₓ body main, κ, ρ, jκ => by
      simp only [Branch.jcWalk]
      rw [Branch.joinCtor_eval]
      simp only [Branch.eval, Branch.jcWalk_eval main κ ρ, Term.jcWalk_eval body κ]
  termination_by structural _ _ _ _ _ _ x => x
theorem Branches.jcWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (jκ : JEnv Δ τ js) → ∀ x, br.jcWalk.2.eval κ ρ jκ x = br.eval κ ρ jκ x
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, κ, ρ, jκ, x => by
      simp only [Branches.jcWalk, Branches.eval, Term.jcWalk_eval b₁ κ, Term.jcWalk_eval b₂ κ]
  | _, _, _, _, _, _, _, _, .cons us b bs, κ, ρ, jκ, x => by
      simp only [Branches.jcWalk, Branches.eval, Term.jcWalk_eval b κ, Branches.jcWalk_eval bs κ ρ jκ]
  termination_by structural _ _ _ _ _ _ _ _ x => x
end

/-- **Writing the join points that take their parameter apart at the jumps passing a
    constructor does not change the value of a statement**, in any environment. -/
theorem Term.joinCtor_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {o : Lvl} (t : Term Δ d Φ Γ τ js o) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    t.joinCtor.eval κ ρ jκ = t.eval κ ρ jκ :=
  Term.keepLvl_eval t _ κ ρ jκ (Term.jcWalk_eval t κ ρ jκ)

end LeanScript

end
