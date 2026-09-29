module

public import LeanScript.Term.Optimize.Fields
public import LeanScript.Term.Optimize.CountDce

@[expose] public section

set_option autoImplicit false

/-!
# The walks of known fields

`Term.widenFields` and `Term.reuseFields` (see `LeanScript.Term.Optimize.Fields`), with the
proofs that they keep the value (`Term.widenFields_eval`, `Term.reuseFields_eval`) and never add
calls (`Term.numCalls_widenFields`, `Term.numCalls_reuseFields`).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Binding every field -/

/-- `record_casesOn us n b`, binding every field (usage `ω`). -/
def Term.widenRecord {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} {fs : Fields ks}
    {τ : Ty ks} {js : JCtx ks} {ℓ : Nat} {o' : Lvl} (us : List Usage01ω)
    (n : Neu Δ Φ Γ (.record t fs) ℓ)
    (b : Term Δ d Φ (UCtx.annot d (t :: fs.toList) us ++ Γ) τ js o') :
    Term Δ d Φ Γ τ js (some (Lvl.meetL ℓ o')) :=
  match b.rename KRen.id (URen.reannot d _ us []) JRen.id with
  | some b' => .record_casesOn [] n b'
  | none => .record_casesOn us n b

theorem Term.widenRecord_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks}
    {fs : Fields ks} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat} {o' : Lvl} (us : List Usage01ω)
    (n : Neu Δ Φ Γ (.record t fs) ℓ)
    (b : Term Δ d Φ (UCtx.annot d (t :: fs.toList) us ++ Γ) τ js o') (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    (Term.widenRecord us n b).eval κ ρ jκ = (Term.record_casesOn us n b).eval κ ρ jκ := by
  unfold Term.widenRecord
  split
  · rename_i b' hb
    simp only [Term.eval]
    exact Term.rename_eval (KRen.Agree.id _) (URen.Agree.reannot ρ d _ us [] _)
      (JRen.Agree.id _) b hb
  · rfl

theorem Term.numCalls_widenRecord {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks}
    {fs : Fields ks} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat} {o' : Lvl} (us : List Usage01ω)
    (n : Neu Δ Φ Γ (.record t fs) ℓ)
    (b : Term Δ d Φ (UCtx.annot d (t :: fs.toList) us ++ Γ) τ js o') :
    (Term.widenRecord us n b).numCalls = b.numCalls := by
  unfold Term.widenRecord
  split
  · rename_i b' hb
    simp only [Term.numCalls]; exact Term.numCalls_rename b hb
  · rfl

mutual
/-- `Term.widenFields` inside the bodies of a value. -/
def Val.widenFields : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ τ o → Val Δ d Φ Γ τ o
  | _, _, _, _, _, .lam b => .lam b.widenFields
  | _, _, _, _, _, .thunk_mk b => .thunk_mk b.widenFields
  | _, _, _, _, _, .lazy_mk b => .lazy_mk b.widenFields
  | _, _, _, _, _, .record_mk args => .record_mk args
  | _, _, _, _, _, .union_mk ix args => .union_mk ix args
  | _, _, _, _, _, .array_mk es => .array_mk es
  | _, _, _, _, _, .list_mk es => .list_mk es
  | _, _, _, _, _, .data_in b j e => .data_in b j e
/-- `Term.widenFields` in a body. -/
def Body.widenFields : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Body Δ d Φ Γ bs τ o → Body Δ d Φ Γ bs τ o
  | _, _, _, _, _, _, .closed t => .closed t.widenFields
  | _, _, _, _, _, _, .opened t h => .opened t.widenFields h
/-- `Term.widenFields` inside the bodies of a computation. -/
def Comp.widenFields : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    Comp Δ d Φ Γ τ ℓ → Comp Δ d Φ Γ τ ℓ
  | _, _, _, _, _, .app f a h => .app f a h
  | _, _, _, _, _, .share n => .share n
  | _, _, _, _, _, .nat_rec n z s h => .nat_rec n z s.widenFields h
  | _, _, _, _, _, .array_foldl a z s h => .array_foldl a z s.widenFields h
  | _, _, _, _, _, .data_rec b ρ us brs j e h =>
      .data_rec b ρ us (fun i => (brs i).widenFields) j e h
  | _, _, _, _, _, .data_brec b ρ k us brs j e h =>
      .data_brec b ρ k us (fun i => (brs i).widenFields) j e h
  | _, _, _, _, _, .thunk_force e => .thunk_force e
  | _, _, _, _, _, .lazy_force e => .lazy_force e
/-- Every record case analysis binds all its fields. -/
def Term.widenFields : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → Term Δ d Φ Γ τ js o → Term Δ d Φ Γ τ js o
  | _, _, _, _, _, _, .ret e => .ret e
  | _, _, _, _, _, _, .letV u v b => .letV u v.widenFields b.widenFields
  | _, _, _, _, _, _, .letE u c b => .letE u c.widenFields b.widenFields
  | _, _, _, _, _, _, .record_casesOn us n b => Term.widenRecord us n b.widenFields
  | _, _, _, _, _, _, .branch br => .branch br.widenFields
  | _, _, _, _, _, _, .jump j e => .jump j e
/-- `Term.widenFields` in a branch. -/
def Branch.widenFields : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → Branch Δ d Φ Γ τ js ℓ
  | _, _, _, _, _, _, .ite c t e => .ite c t.widenFields e.widenFields
  | _, _, _, _, _, _, .enum_casesOn e bs => .enum_casesOn e (fun i => (bs i).widenFields)
  | _, _, _, _, _, _, .union_casesOn e bs => .union_casesOn e bs.widenFields
  | _, _, _, _, _, _, .join σ u uₓ body main =>
      .join σ u uₓ body.widenFields main.widenFields
/-- `Term.widenFields` in the branches of a union's case analysis. -/
def Branches.widenFields : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → Branches Δ d Φ Γ cs τ js o
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ => .two us₁ us₂ b₁.widenFields b₂.widenFields
  | _, _, _, _, _, _, _, _, .cons us b bs => .cons us b.widenFields bs.widenFields
end

mutual
theorem Val.widenFields_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    v.widenFields.eval κ ρ = v.eval κ ρ
  | _, _, _, _, _, .lam b, κ, ρ => by
      simp only [Val.widenFields, Val.eval]; funext x; rw [Body.widenFields_eval b κ ρ]
  | _, _, _, _, _, .thunk_mk b, κ, ρ => by
      simp only [Val.widenFields, Val.eval]; rw [Body.widenFields_eval b κ ρ]
  | _, _, _, _, _, .lazy_mk b, κ, ρ => by
      simp only [Val.widenFields, Val.eval]; rw [Body.widenFields_eval b κ ρ]
  | _, _, _, _, _, .record_mk _, _, _ => rfl
  | _, _, _, _, _, .union_mk _ _, _, _ => rfl
  | _, _, _, _, _, .array_mk _, _, _ => rfl
  | _, _, _, _, _, .list_mk _, _, _ => rfl
  | _, _, _, _, _, .data_in _ _ _, _, _ => rfl
  termination_by structural _ _ _ _ _ x _ _ => x
theorem Body.widenFields_eval : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (vs : UEnv Δ bs) → b.widenFields.eval κ ρ vs = b.eval κ ρ vs
  | _, _, _, _, _, _, .closed t, _, _, _ => by
      simp only [Body.widenFields, Body.eval]; exact Term.widenFields_eval t _ _ _
  | _, _, _, _, _, _, .opened t _, _, _, _ => by
      simp only [Body.widenFields, Body.eval]; exact Term.widenFields_eval t _ _ _
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Comp.widenFields_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    c.widenFields.eval κ ρ = c.eval κ ρ
  | _, _, _, _, _, .app _ _ _, _, _ => rfl
  | _, _, _, _, _, .share _, _, _ => rfl
  | _, _, _, _, _, .nat_rec n z s _, κ, ρ => by
      simp only [Comp.widenFields, Comp.eval]
      congr 1; funext k acc; exact Body.widenFields_eval s κ ρ _
  | _, _, _, _, _, .array_foldl a z s _, κ, ρ => by
      simp only [Comp.widenFields, Comp.eval]
      congr 1; funext acc x; exact Body.widenFields_eval s κ ρ _
  | _, _, _, _, _, .data_rec b ρt us brs j e _, κ, ρ => by
      simp only [Comp.widenFields, Comp.eval]
      congr 1; funext i x; exact Body.widenFields_eval (brs i) κ ρ _
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, κ, ρ => by
      simp only [Comp.widenFields, Comp.eval]
      congr 1; funext i x; exact Body.widenFields_eval (brs i) κ ρ _
  | _, _, _, _, _, .thunk_force _, _, _ => rfl
  | _, _, _, _, _, .lazy_force _, _, _ => rfl
  termination_by structural _ _ _ _ _ x _ _ => x
theorem Term.widenFields_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → t.widenFields.eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, .ret _, _, _, _ => rfl
  | _, _, _, _, _, _, .letV u v b, κ, ρ, jκ => by
      simp only [Term.widenFields, Term.eval, Val.widenFields_eval v, Term.widenFields_eval b]
  | _, _, _, _, _, _, .letE u c b, κ, ρ, jκ => by
      simp only [Term.widenFields, Term.eval, Comp.widenFields_eval c, Term.widenFields_eval b]
  | _, _, _, _, _, _, .record_casesOn us n b, κ, ρ, jκ => by
      simp only [Term.widenFields]
      rw [Term.widenRecord_eval]
      simp only [Term.eval, Term.widenFields_eval b]
  | _, _, _, _, _, _, .branch br, κ, ρ, jκ => by
      simp only [Term.widenFields, Term.eval, Branch.widenFields_eval br]
  | _, _, _, _, _, _, .jump _ _, _, _, _ => rfl
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Branch.widenFields_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → br.widenFields.eval κ ρ jκ = br.eval κ ρ jκ
  | _, _, _, _, _, _, .ite c t e, κ, ρ, jκ => by
      simp only [Branch.widenFields, Branch.eval, Term.widenFields_eval t,
        Term.widenFields_eval e]
  | _, _, _, _, _, _, .enum_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.widenFields, Branch.eval]; exact Term.widenFields_eval _ _ _ _
  | _, _, _, _, _, _, .union_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.widenFields, Branch.eval]; exact Branches.widenFields_eval bs κ ρ jκ _
  | _, _, _, _, _, _, .join σ u uₓ body main, κ, ρ, jκ => by
      simp only [Branch.widenFields, Branch.eval, Branch.widenFields_eval main,
        Term.widenFields_eval body]
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Branches.widenFields_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
      ∀ x, br.widenFields.eval κ ρ jκ x = br.eval κ ρ jκ x
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, κ, ρ, jκ, x => by
      simp only [Branches.widenFields, Branches.eval, Term.widenFields_eval b₁,
        Term.widenFields_eval b₂]
  | _, _, _, _, _, _, _, _, .cons us b bs, κ, ρ, jκ, x => by
      simp only [Branches.widenFields, Branches.eval, Term.widenFields_eval b,
        Branches.widenFields_eval bs]
  termination_by structural _ _ _ _ _ _ _ _ x _ _ _ _ => x
end

mutual
theorem Val.numCalls_widenFields : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → v.widenFields.numCalls = v.numCalls
  | _, _, _, _, _, .lam b => by
      simp only [Val.widenFields, Val.numCalls, Body.numCalls_widenFields b]
  | _, _, _, _, _, .thunk_mk b => by
      simp only [Val.widenFields, Val.numCalls, Body.numCalls_widenFields b]
  | _, _, _, _, _, .lazy_mk b => by
      simp only [Val.widenFields, Val.numCalls, Body.numCalls_widenFields b]
  | _, _, _, _, _, .record_mk _ => rfl
  | _, _, _, _, _, .union_mk _ _ => rfl
  | _, _, _, _, _, .array_mk _ => rfl
  | _, _, _, _, _, .list_mk _ => rfl
  | _, _, _, _, _, .data_in _ _ _ => rfl
  termination_by structural _ _ _ _ _ x => x
theorem Body.numCalls_widenFields : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} →
    {τ : Ty ks} → {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → b.widenFields.numCalls = b.numCalls
  | _, _, _, _, _, _, .closed t => by
      simp only [Body.widenFields, Body.numCalls, Term.numCalls_widenFields t]
  | _, _, _, _, _, _, .opened t _ => by
      simp only [Body.widenFields, Body.numCalls, Term.numCalls_widenFields t]
  termination_by structural _ _ _ _ _ _ x => x
theorem Comp.numCalls_widenFields : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → c.widenFields.numCalls = c.numCalls
  | _, _, _, _, _, .app _ _ _ => rfl
  | _, _, _, _, _, .share _ => rfl
  | _, _, _, _, _, .nat_rec n z s _ => by
      simp only [Comp.widenFields, Comp.numCalls, Body.numCalls_widenFields s]
  | _, _, _, _, _, .array_foldl a z s _ => by
      simp only [Comp.widenFields, Comp.numCalls, Body.numCalls_widenFields s]
  | _, _, _, _, _, .data_rec b ρt us brs j e _ => by
      simp only [Comp.widenFields, Comp.numCalls]
      exact Fin.sumNat_congr _ (fun i => Body.numCalls_widenFields (brs i))
  | _, _, _, _, _, .data_brec b ρt k us brs j e _ => by
      simp only [Comp.widenFields, Comp.numCalls]
      exact Fin.sumNat_congr _ (fun i => Body.numCalls_widenFields (brs i))
  | _, _, _, _, _, .thunk_force _ => rfl
  | _, _, _, _, _, .lazy_force _ => rfl
  termination_by structural _ _ _ _ _ x => x
theorem Term.numCalls_widenFields : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) →
    t.widenFields.numCalls = t.numCalls
  | _, _, _, _, _, _, .ret _ => rfl
  | _, _, _, _, _, _, .letV u v b => by
      simp only [Term.widenFields, Term.numCalls, Val.numCalls_widenFields v,
        Term.numCalls_widenFields b]
  | _, _, _, _, _, _, .letE u c b => by
      simp only [Term.widenFields, Term.numCalls, Comp.numCalls_widenFields c,
        Term.numCalls_widenFields b]
  | _, _, _, _, _, _, .record_casesOn us n b => by
      simp only [Term.widenFields, Term.numCalls_widenRecord, Term.numCalls,
        Term.numCalls_widenFields b]
  | _, _, _, _, _, _, .branch br => by
      simp only [Term.widenFields, Term.numCalls, Branch.numCalls_widenFields br]
  | _, _, _, _, _, _, .jump _ _ => rfl
  termination_by structural _ _ _ _ _ _ x => x
theorem Branch.numCalls_widenFields : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {τ : Ty ks} → {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) →
    br.widenFields.numCalls = br.numCalls
  | _, _, _, _, _, _, .ite c t e => by
      simp only [Branch.widenFields, Branch.numCalls, Term.numCalls_widenFields t,
        Term.numCalls_widenFields e]
  | _, _, _, _, _, _, .enum_casesOn e bs => by
      simp only [Branch.widenFields, Branch.numCalls]
      exact Fin.sumNat_congr _ (fun i => Term.numCalls_widenFields (bs i))
  | _, _, _, _, _, _, .union_casesOn e bs => by
      simp only [Branch.widenFields, Branch.numCalls, Branches.numCalls_widenFields bs]
  | _, _, _, _, _, _, .join σ u uₓ body main => by
      simp only [Branch.widenFields, Branch.numCalls, Term.numCalls_widenFields body,
        Branch.numCalls_widenFields main]
  termination_by structural _ _ _ _ _ _ x => x
theorem Branches.numCalls_widenFields : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → br.widenFields.numCalls = br.numCalls
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ => by
      simp only [Branches.widenFields, Branches.numCalls, Term.numCalls_widenFields b₁,
        Term.numCalls_widenFields b₂]
  | _, _, _, _, _, _, _, _, .cons us b bs => by
      simp only [Branches.widenFields, Branches.numCalls, Term.numCalls_widenFields b,
        Branches.numCalls_widenFields bs]
  termination_by structural _ _ _ _ _ _ _ _ x => x
end

/-! ## Reusing known fields -/

/-- The facts known under a record case analysis of `n` binding the fields with usages `us`:
    the facts known before and, when `n` is an unknown, that its fields are the ones bound. -/
def RecFact.extend {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} {fs : Fields ks} {ℓ : Nat}
    (facts : List (RecFact Γ d)) (us : List Usage01ω) (n : Neu Δ Φ Γ (.record t fs) ℓ) :
    List (RecFact (UCtx.annot d (t :: fs.toList) us ++ Γ) d) :=
  match n with
  | .var y => ⟨y.weakenN _, FieldVars.ofAnnot Γ d _ us⟩ :: facts.map (RecFact.weakenN _)
  | _ => facts.map (RecFact.weakenN _)

theorem RecFact.map_weaken_holds {Γ : UCtx ks} {d : Nat} {b : UBinder ks} (v : Ty.Den Δ b.ty)
    {ρ : UEnv Δ Γ} {facts : List (RecFact Γ d)} (h : ∀ f ∈ facts, f.Holds ρ) :
    ∀ f ∈ facts.map (RecFact.weaken b), f.Holds (Tuple.cons v ρ) := by
  intro f hf
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
  exact RecFact.Holds.weaken v (h g hg)

theorem RecFact.map_weakenN_holds {Γ : UCtx ks} {d : Nat} (bs : UCtx ks) (vs : UEnv Δ bs)
    {ρ : UEnv Δ Γ} {facts : List (RecFact Γ d)} (h : ∀ f ∈ facts, f.Holds ρ) :
    ∀ f ∈ facts.map (RecFact.weakenN bs), f.Holds (Tuple.append vs ρ) := by
  intro f hf
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
  exact RecFact.Holds.weakenN bs vs (h g hg)

theorem RecFact.extend_holds {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks}
    {fs : Fields ks} {ℓ : Nat} (facts : List (RecFact Γ d)) (us : List Usage01ω)
    (n : Neu Δ Φ Γ (.record t fs) ℓ) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (h : ∀ f ∈ facts, f.Holds ρ) :
    ∀ f ∈ RecFact.extend facts us n,
      f.Holds (Tuple.append (UEnv.ofDL d _ us (recordFields (n.eval κ ρ))) ρ) := by
  unfold RecFact.extend
  split
  · rename_i y
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · unfold RecFact.Holds
      simp only [UEnv.get_weakenN]
      exact FieldVars.Holds.ofAnnot ρ d _ us _
    · exact RecFact.map_weakenN_holds _ _ h f hf
  · exact RecFact.map_weakenN_holds _ _ h

/-- `record_casesOn us n b`, dropped when the fields of `n` are known: `b` then reads the known
    ones. -/
def Term.reuseRecord {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} {fs : Fields ks}
    {τ : Ty ks} {js : JCtx ks} {ℓ : Nat} {o' : Lvl} (facts : List (RecFact Γ d))
    (us : List Usage01ω) (n : Neu Δ Φ Γ (.record t fs) ℓ)
    (b : Term Δ d Φ (UCtx.annot d (t :: fs.toList) us ++ Γ) τ js o') :
    Term Δ d Φ Γ τ js (some (Lvl.meetL ℓ o')) :=
  match n with
  | .var y =>
    match RecFact.find? facts y with
    | some fv =>
      match b.rename KRen.id (fv.toRen us) JRen.id with
      | some b' =>
          if ho : o' = some (Lvl.meetL ℓ o') then b'.castLvl ho
          else .record_casesOn us (.var y) b
      | none => .record_casesOn us (.var y) b
    | none => .record_casesOn us (.var y) b
  | n => .record_casesOn us n b

theorem Term.reuseRecord_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks}
    {fs : Fields ks} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat} {o' : Lvl}
    (facts : List (RecFact Γ d)) (us : List Usage01ω) (n : Neu Δ Φ Γ (.record t fs) ℓ)
    (b : Term Δ d Φ (UCtx.annot d (t :: fs.toList) us ++ Γ) τ js o') (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) (h : ∀ f ∈ facts, f.Holds ρ) :
    (Term.reuseRecord facts us n b).eval κ ρ jκ = (Term.record_casesOn us n b).eval κ ρ jκ := by
  unfold Term.reuseRecord
  split
  · rename_i y
    split
    · rename_i fv hfv
      split
      · rename_i b' hb
        split
        · rw [Term.eval_castLvl]
          simp only [Term.eval]
          exact Term.rename_eval (KRen.Agree.id _)
            (FieldVars.Holds.agree fv _ (RecFact.find?_holds facts h hfv) us) (JRen.Agree.id _)
            b hb
        · rfl
      · rfl
    · rfl
  · rfl

theorem Term.numCalls_reuseRecord {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks}
    {fs : Fields ks} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat} {o' : Lvl}
    (facts : List (RecFact Γ d)) (us : List Usage01ω) (n : Neu Δ Φ Γ (.record t fs) ℓ)
    (b : Term Δ d Φ (UCtx.annot d (t :: fs.toList) us ++ Γ) τ js o') :
    (Term.reuseRecord facts us n b).numCalls ≤ b.numCalls := by
  unfold Term.reuseRecord
  split
  · split
    · split
      · rename_i b' hb
        split
        · simp only [Term.numCalls_castLvl, Term.numCalls_rename b hb, Nat.le_refl]
        · exact Nat.le_refl _
      · exact Nat.le_refl _
    · exact Nat.le_refl _
  · exact Nat.le_refl _

mutual
/-- `Term.reuseFields` inside the bodies of a value (which start with no fact). -/
def Val.reuseFields : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ τ o → Val Δ d Φ Γ τ o
  | _, _, _, _, _, .lam b => .lam b.reuseFields
  | _, _, _, _, _, .thunk_mk b => .thunk_mk b.reuseFields
  | _, _, _, _, _, .lazy_mk b => .lazy_mk b.reuseFields
  | _, _, _, _, _, .record_mk args => .record_mk args
  | _, _, _, _, _, .union_mk ix args => .union_mk ix args
  | _, _, _, _, _, .array_mk es => .array_mk es
  | _, _, _, _, _, .list_mk es => .list_mk es
  | _, _, _, _, _, .data_in b j e => .data_in b j e
/-- `Term.reuseFields` in a body, with no fact. -/
def Body.reuseFields : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Body Δ d Φ Γ bs τ o → Body Δ d Φ Γ bs τ o
  | _, _, _, _, _, _, .closed t => .closed (t.reuseFields [])
  | _, _, _, _, _, _, .opened t h => .opened (t.reuseFields []) h
/-- `Term.reuseFields` inside the bodies of a computation. -/
def Comp.reuseFields : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    Comp Δ d Φ Γ τ ℓ → Comp Δ d Φ Γ τ ℓ
  | _, _, _, _, _, .app f a h => .app f a h
  | _, _, _, _, _, .share n => .share n
  | _, _, _, _, _, .nat_rec n z s h => .nat_rec n z s.reuseFields h
  | _, _, _, _, _, .array_foldl a z s h => .array_foldl a z s.reuseFields h
  | _, _, _, _, _, .data_rec b ρ us brs j e h =>
      .data_rec b ρ us (fun i => (brs i).reuseFields) j e h
  | _, _, _, _, _, .data_brec b ρ k us brs j e h =>
      .data_brec b ρ k us (fun i => (brs i).reuseFields) j e h
  | _, _, _, _, _, .thunk_force e => .thunk_force e
  | _, _, _, _, _, .lazy_force e => .lazy_force e
/-- **Reuse known fields**: walk a statement knowing `facts`; a record case analysis of an
    unknown whose fields are known is dropped (`Term.reuseRecord`), and one of an unknown whose
    fields are not known yet makes them known in its body (`RecFact.extend`). -/
def Term.reuseFields : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → List (RecFact Γ d) → Term Δ d Φ Γ τ js o →
    Term Δ d Φ Γ τ js o
  | _, _, _, _, _, _, _, .ret e => .ret e
  | _, _, _, _, _, _, facts, .letV u v b => .letV u v.reuseFields (b.reuseFields facts)
  | _, _, _, _, _, _, facts, .letE u c b =>
      .letE u c.reuseFields (b.reuseFields (facts.map (RecFact.weaken _)))
  | _, _, _, _, _, _, facts, .record_casesOn us n b =>
      Term.reuseRecord facts us n (b.reuseFields (RecFact.extend facts us n))
  | _, _, _, _, _, _, facts, .branch br => .branch (br.reuseFields facts)
  | _, _, _, _, _, _, _, .jump j e => .jump j e
/-- `Term.reuseFields` in a branch. -/
def Branch.reuseFields : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → List (RecFact Γ d) → Branch Δ d Φ Γ τ js ℓ →
    Branch Δ d Φ Γ τ js ℓ
  | _, _, _, _, _, _, facts, .ite c t e => .ite c (t.reuseFields facts) (e.reuseFields facts)
  | _, _, _, _, _, _, facts, .enum_casesOn e bs =>
      .enum_casesOn e (fun i => (bs i).reuseFields facts)
  | _, _, _, _, _, _, facts, .union_casesOn e bs => .union_casesOn e (bs.reuseFields facts)
  | _, _, _, _, _, _, facts, .join σ u uₓ body main =>
      .join σ u uₓ (body.reuseFields (facts.map (RecFact.weaken _))) (main.reuseFields facts)
/-- `Term.reuseFields` in the branches of a union's case analysis. -/
def Branches.reuseFields : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} → List (RecFact Γ d) →
    Branches Δ d Φ Γ cs τ js o → Branches Δ d Φ Γ cs τ js o
  | _, _, _, _, _, _, _, _, facts, .two us₁ us₂ b₁ b₂ =>
      .two us₁ us₂ (b₁.reuseFields (facts.map (RecFact.weakenN _)))
        (b₂.reuseFields (facts.map (RecFact.weakenN _)))
  | _, _, _, _, _, _, _, _, facts, .cons us b bs =>
      .cons us (b.reuseFields (facts.map (RecFact.weakenN _))) (bs.reuseFields facts)
end

mutual
theorem Val.reuseFields_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    v.reuseFields.eval κ ρ = v.eval κ ρ
  | _, _, _, _, _, .lam b, κ, ρ => by
      simp only [Val.reuseFields, Val.eval]; funext x; rw [Body.reuseFields_eval b κ ρ]
  | _, _, _, _, _, .thunk_mk b, κ, ρ => by
      simp only [Val.reuseFields, Val.eval]; rw [Body.reuseFields_eval b κ ρ]
  | _, _, _, _, _, .lazy_mk b, κ, ρ => by
      simp only [Val.reuseFields, Val.eval]; rw [Body.reuseFields_eval b κ ρ]
  | _, _, _, _, _, .record_mk _, _, _ => rfl
  | _, _, _, _, _, .union_mk _ _, _, _ => rfl
  | _, _, _, _, _, .array_mk _, _, _ => rfl
  | _, _, _, _, _, .list_mk _, _, _ => rfl
  | _, _, _, _, _, .data_in _ _ _, _, _ => rfl
  termination_by structural _ _ _ _ _ x _ _ => x
theorem Body.reuseFields_eval : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (vs : UEnv Δ bs) → b.reuseFields.eval κ ρ vs = b.eval κ ρ vs
  | _, _, _, _, _, _, .closed t, _, _, _ => by
      simp only [Body.reuseFields, Body.eval]
      exact Term.reuseFields_eval t [] _ _ _ (fun _ h => nomatch h)
  | _, _, _, _, _, _, .opened t _, _, _, _ => by
      simp only [Body.reuseFields, Body.eval]
      exact Term.reuseFields_eval t [] _ _ _ (fun _ h => nomatch h)
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Comp.reuseFields_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    c.reuseFields.eval κ ρ = c.eval κ ρ
  | _, _, _, _, _, .app _ _ _, _, _ => rfl
  | _, _, _, _, _, .share _, _, _ => rfl
  | _, _, _, _, _, .nat_rec n z s _, κ, ρ => by
      simp only [Comp.reuseFields, Comp.eval]
      congr 1; funext k acc; exact Body.reuseFields_eval s κ ρ _
  | _, _, _, _, _, .array_foldl a z s _, κ, ρ => by
      simp only [Comp.reuseFields, Comp.eval]
      congr 1; funext acc x; exact Body.reuseFields_eval s κ ρ _
  | _, _, _, _, _, .data_rec b ρt us brs j e _, κ, ρ => by
      simp only [Comp.reuseFields, Comp.eval]
      congr 1; funext i x; exact Body.reuseFields_eval (brs i) κ ρ _
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, κ, ρ => by
      simp only [Comp.reuseFields, Comp.eval]
      congr 1; funext i x; exact Body.reuseFields_eval (brs i) κ ρ _
  | _, _, _, _, _, .thunk_force _, _, _ => rfl
  | _, _, _, _, _, .lazy_force _, _, _ => rfl
  termination_by structural _ _ _ _ _ x _ _ => x
theorem Term.reuseFields_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → (facts : List (RecFact Γ d)) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → (∀ f ∈ facts, f.Holds ρ) →
    (t.reuseFields facts).eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, .ret _, _, _, _, _, _ => rfl
  | _, _, _, _, _, _, .letV u v b, facts, κ, ρ, jκ, h => by
      simp only [Term.reuseFields, Term.eval, Val.reuseFields_eval v,
        Term.reuseFields_eval b facts _ ρ jκ h]
  | _, _, _, _, _, _, .letE u c b, facts, κ, ρ, jκ, h => by
      simp only [Term.reuseFields, Term.eval, Comp.reuseFields_eval c]
      exact Term.reuseFields_eval b _ κ _ jκ (RecFact.map_weaken_holds _ h)
  | _, _, _, _, _, _, .record_casesOn us n b, facts, κ, ρ, jκ, h => by
      simp only [Term.reuseFields]
      rw [Term.reuseRecord_eval _ _ _ _ κ ρ jκ h]
      simp only [Term.eval]
      exact Term.reuseFields_eval b _ κ _ jκ (RecFact.extend_holds facts us n κ ρ h)
  | _, _, _, _, _, _, .branch br, facts, κ, ρ, jκ, h => by
      simp only [Term.reuseFields, Term.eval]
      exact Branch.reuseFields_eval br facts κ ρ jκ h
  | _, _, _, _, _, _, .jump _ _, _, _, _, _, _ => rfl
  termination_by structural _ _ _ _ _ _ x _ _ _ _ _ => x
theorem Branch.reuseFields_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → (facts : List (RecFact Γ d)) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → (∀ f ∈ facts, f.Holds ρ) →
    (br.reuseFields facts).eval κ ρ jκ = br.eval κ ρ jκ
  | _, _, _, _, _, _, .ite c t e, facts, κ, ρ, jκ, h => by
      simp only [Branch.reuseFields, Branch.eval, Term.reuseFields_eval t facts κ ρ jκ h,
        Term.reuseFields_eval e facts κ ρ jκ h]
  | _, _, _, _, _, _, .enum_casesOn e bs, facts, κ, ρ, jκ, h => by
      simp only [Branch.reuseFields, Branch.eval]
      exact Term.reuseFields_eval _ facts κ ρ jκ h
  | _, _, _, _, _, _, .union_casesOn e bs, facts, κ, ρ, jκ, h => by
      simp only [Branch.reuseFields, Branch.eval]
      exact Branches.reuseFields_eval bs facts κ ρ jκ h _
  | _, _, _, _, _, _, .join σ u uₓ body main, facts, κ, ρ, jκ, h => by
      simp only [Branch.reuseFields, Branch.eval, Branch.reuseFields_eval main facts κ ρ _ h]
      congr 2
      funext v
      exact Term.reuseFields_eval body _ κ _ jκ (RecFact.map_weaken_holds (b := ⟨σ, uₓ, _⟩) v h)
  termination_by structural _ _ _ _ _ _ x _ _ _ _ _ => x
theorem Branches.reuseFields_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (facts : List (RecFact Γ d)) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → (∀ f ∈ facts, f.Holds ρ) →
      ∀ x, (br.reuseFields facts).eval κ ρ jκ x = br.eval κ ρ jκ x
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, facts, κ, ρ, jκ, h, x => by
      simp only [Branches.reuseFields, Branches.eval]
      congr 1
      · funext v
        exact Term.reuseFields_eval b₁ _ κ _ jκ (RecFact.map_weakenN_holds _ _ h)
      · funext v
        exact Term.reuseFields_eval b₂ _ κ _ jκ (RecFact.map_weakenN_holds _ _ h)
  | _, _, _, _, _, _, _, _, .cons us b bs, facts, κ, ρ, jκ, h, x => by
      simp only [Branches.reuseFields, Branches.eval]
      congr 1
      · funext v
        exact Term.reuseFields_eval b _ κ _ jκ (RecFact.map_weakenN_holds _ _ h)
      · funext r
        exact Branches.reuseFields_eval bs facts κ ρ jκ h r
  termination_by structural _ _ _ _ _ _ _ _ x _ _ _ _ _ => x
end

mutual
theorem Val.numCalls_reuseFields : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → v.reuseFields.numCalls ≤ v.numCalls
  | _, _, _, _, _, .lam b => by
      simp only [Val.reuseFields, Val.numCalls]; exact Body.numCalls_reuseFields b
  | _, _, _, _, _, .thunk_mk b => by
      simp only [Val.reuseFields, Val.numCalls]; exact Body.numCalls_reuseFields b
  | _, _, _, _, _, .lazy_mk b => by
      simp only [Val.reuseFields, Val.numCalls]; exact Body.numCalls_reuseFields b
  | _, _, _, _, _, .record_mk _ => Nat.le_refl _
  | _, _, _, _, _, .union_mk _ _ => Nat.le_refl _
  | _, _, _, _, _, .array_mk _ => Nat.le_refl _
  | _, _, _, _, _, .list_mk _ => Nat.le_refl _
  | _, _, _, _, _, .data_in _ _ _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
theorem Body.numCalls_reuseFields : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} →
    {τ : Ty ks} → {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → b.reuseFields.numCalls ≤ b.numCalls
  | _, _, _, _, _, _, .closed t => by
      simp only [Body.reuseFields, Body.numCalls]; exact Term.numCalls_reuseFields t []
  | _, _, _, _, _, _, .opened t _ => by
      simp only [Body.reuseFields, Body.numCalls]; exact Term.numCalls_reuseFields t []
  termination_by structural _ _ _ _ _ _ x => x
theorem Comp.numCalls_reuseFields : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → c.reuseFields.numCalls ≤ c.numCalls
  | _, _, _, _, _, .app _ _ _ => Nat.le_refl _
  | _, _, _, _, _, .share _ => Nat.le_refl _
  | _, _, _, _, _, .nat_rec n z s _ => by
      simp only [Comp.reuseFields, Comp.numCalls]; exact Body.numCalls_reuseFields s
  | _, _, _, _, _, .array_foldl a z s _ => by
      simp only [Comp.reuseFields, Comp.numCalls]; exact Body.numCalls_reuseFields s
  | _, _, _, _, _, .data_rec b ρt us brs j e _ => by
      simp only [Comp.reuseFields, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_reuseFields (brs i))
  | _, _, _, _, _, .data_brec b ρt k us brs j e _ => by
      simp only [Comp.reuseFields, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_reuseFields (brs i))
  | _, _, _, _, _, .thunk_force _ => Nat.le_refl _
  | _, _, _, _, _, .lazy_force _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
theorem Term.numCalls_reuseFields : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → (facts : List (RecFact Γ d)) →
    (t.reuseFields facts).numCalls ≤ t.numCalls
  | _, _, _, _, _, _, .ret _, _ => Nat.le_refl _
  | _, _, _, _, _, _, .letV u v b, facts => by
      have h₁ := Val.numCalls_reuseFields v
      have h₂ := Term.numCalls_reuseFields b facts
      simp only [Term.reuseFields, Term.numCalls]; omega
  | _, _, _, _, _, _, .letE u c b, facts => by
      have h₁ := Comp.numCalls_reuseFields c
      have h₂ := Term.numCalls_reuseFields b (facts.map (RecFact.weaken _))
      simp only [Term.reuseFields, Term.numCalls]; omega
  | _, _, _, _, _, _, .record_casesOn us n b, facts => by
      have h₁ := Term.numCalls_reuseRecord facts us n (b.reuseFields (RecFact.extend facts us n))
      have h₂ := Term.numCalls_reuseFields b (RecFact.extend facts us n)
      simp only [Term.reuseFields, Term.numCalls]; omega
  | _, _, _, _, _, _, .branch br, facts => by
      simp only [Term.reuseFields, Term.numCalls]; exact Branch.numCalls_reuseFields br facts
  | _, _, _, _, _, _, .jump _ _, _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ _ x _ => x
theorem Branch.numCalls_reuseFields : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {τ : Ty ks} → {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) →
    (facts : List (RecFact Γ d)) → (br.reuseFields facts).numCalls ≤ br.numCalls
  | _, _, _, _, _, _, .ite c t e, facts => by
      have h₁ := Term.numCalls_reuseFields t facts
      have h₂ := Term.numCalls_reuseFields e facts
      simp only [Branch.reuseFields, Branch.numCalls]; omega
  | _, _, _, _, _, _, .enum_casesOn e bs, facts => by
      simp only [Branch.reuseFields, Branch.numCalls]
      exact Fin.sumNat_le _ (fun i => Term.numCalls_reuseFields (bs i) facts)
  | _, _, _, _, _, _, .union_casesOn e bs, facts => by
      simp only [Branch.reuseFields, Branch.numCalls]; exact Branches.numCalls_reuseFields bs facts
  | _, _, _, _, _, _, .join σ u uₓ body main, facts => by
      have h₁ := Term.numCalls_reuseFields body (facts.map (RecFact.weaken _))
      have h₂ := Branch.numCalls_reuseFields main facts
      simp only [Branch.reuseFields, Branch.numCalls]; omega
  termination_by structural _ _ _ _ _ _ x _ => x
theorem Branches.numCalls_reuseFields : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (facts : List (RecFact Γ d)) →
    (br.reuseFields facts).numCalls ≤ br.numCalls
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, facts => by
      have h₁ := Term.numCalls_reuseFields b₁ (facts.map (RecFact.weakenN _))
      have h₂ := Term.numCalls_reuseFields b₂ (facts.map (RecFact.weakenN _))
      simp only [Branches.reuseFields, Branches.numCalls]; omega
  | _, _, _, _, _, _, _, _, .cons us b bs, facts => by
      have h₁ := Term.numCalls_reuseFields b (facts.map (RecFact.weakenN _))
      have h₂ := Branches.numCalls_reuseFields bs facts
      simp only [Branches.reuseFields, Branches.numCalls]; omega
  termination_by structural _ _ _ _ _ _ _ _ x _ => x
end

end LeanScript

end
