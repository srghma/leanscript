module

public import LeanScript.Term.Optimize.ShareTest
public import LeanScript.Term.Optimize.InlineBlockEval
public import LeanScript.Term.Optimize.CountDce

@[expose] public section

set_option autoImplicit false

/-!
# A test is pushed into the answers when both arms of an `if` test the same things

`Term.zipTest fuel p t e`: when the two arms `t` and `e` of `if p then t else e` make **the same
tests in the same order** (the same conditions, `Neu.same`, and the same record case analyses,
of the same scrutinee), and differ only in their answers, the statement is the common decision
tree whose answers are `p ? a : b` (or just `a` when the answers `a` and `b` are the same):

```
if p then (let ⟨x, y⟩ := r;               let ⟨x, y⟩ := r
           if x == 1 then (y == 2 ? 1 : 3)   if x == 1 then
           else 3)                    ⟹       if y == 2 then (p ? 1 : 2) else (p ? 3 : 4)
     else (let ⟨x, y⟩ := r;                  else (p ? 3 : 4)
           if x == 1 then (y == 2 ? 2 : 4)
           else 4)
```

The language is pure and total, so the test `p` can be moved below the others.  On every path
the rewritten statement makes exactly the tests the original made (the shared tests, then `p`),
or fewer (when both answers are the same, `p` is not tested); the shared tests and case analyses
are written once instead of twice.  This is the order the compiled `match` of
purescript-backend-optimizer tests a row whose leading columns are wildcards: in
`| {a := {b := 1, c := 2}, d := {e := 1, f := 2}} => 1 | {a := {c := 2}, d := {e := 1, f := 2}} => 2
 | {a := {b := 1, c := 2}} => 3`, the column `d` is tested before the column `b`.

The rewrite is proved to preserve the value (`Term.zipTest_eval`); its result makes no call
(`Term.zipTest_numCalls`).  `Term.zipTestWalk` applies it at every `if` whose arms are not both
answers, bottom-up, when it keeps the level of the statement (`Term.zipTestWalk_eval`,
`Term.numCalls_zipTestWalk`).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

section Zip
variable {d : Nat} {Φ : KCtx ks} {τ : Ty ks} {js : JCtx ks}

/-- A statement moved along an equality of contexts of unknowns. -/
def Term.castCtx {Γ Γ' : UCtx ks} {o : Lvl} (h : Γ = Γ') (t : Term Δ d Φ Γ τ js o) :
    Term Δ d Φ Γ' τ js o := h ▸ t

@[simp] theorem Term.castCtx_rfl {Γ : UCtx ks} {o : Lvl} (h : Γ = Γ) (t : Term Δ d Φ Γ τ js o) :
    t.castCtx h = t := rfl

/-- The fields bound by two record case analyses of the same type, with the same usages. -/
theorem UCtx.annot_record_eq {Γ : UCtx ks} {t₁ t₂ : Ty ks} {fs₁ fs₂ : Fields ks}
    {us₁ us₂ : List Usage01ω} (h : (Ty.record t₂ fs₂ : Ty ks) = Ty.record t₁ fs₁)
    (hu : us₂ = us₁) :
    UCtx.annot d (t₂ :: fs₂.toList) us₂ ++ Γ = UCtx.annot d (t₁ :: fs₁.toList) us₁ ++ Γ := by
  cases h; cases hu; rfl

/-- `if p then t else e` as one decision tree, when `t` and `e` make the same tests (the same
    conditions and the same record case analyses, in the same order) and differ only in their
    answers: the answers become `p ? a : b` (`a` when `a` and `b` are the same).  `none` when
    the arms do not have the same shape (or the fuel runs out). -/
def Term.zipTest : Nat → {Γ : UCtx ks} → {ℓ : Nat} → {o₁ o₂ : Lvl} → Neu Δ Φ Γ .bool ℓ →
    Term Δ d Φ Γ τ js o₁ → Term Δ d Φ Γ τ js o₂ → Option ((o : Lvl) × Term Δ d Φ Γ τ js o)
  | 0, _, _, _, _, _, _, _ => none
  | fuel + 1, Γ, _, _, _, p, t, e =>
    let viaTest : Option ((o : Lvl) × Term Δ d Φ Γ τ js o) :=
      match t.testView?, e.testView? with
      | some vt, some ve =>
        if vt.q.same ve.q then
          match Term.zipTest fuel p vt.t ve.t, Term.zipTest fuel p vt.e ve.e with
          | some r₁, some r₂ => some ⟨_, .branch (.ite vt.q r₁.2 r₂.2)⟩
          | _, _ => none
        else none
      | _, _ => none
    match viaTest with
    | some r => some r
    | none =>
      match t, e with
      | .ret a, .ret b =>
        if a.same b then some ⟨_, .ret a⟩ else some ⟨_, .ret (.neu (.cond p a b))⟩
      | .record_casesOn (t := t₁) (fs := fs₁) us₁ n₁ b₁,
        .record_casesOn us₂ n₂ b₂ =>
        if hs : n₂.same n₁ = true then
          if hu : us₂ = us₁ then
            match p.rename KRen.id (URen.wkN (UCtx.annot d (t₁ :: fs₁.toList) us₁)) with
            | some p' =>
              match Term.zipTest fuel p' b₁
                  (b₂.castCtx (UCtx.annot_record_eq (Neu.same_eval n₂ n₁ hs).1 hu)) with
              | some r => some ⟨_, .record_casesOn us₁ n₁ r.2⟩
              | none => none
            | none => none
          else none
        else none
      | _, _ => none

/-- **Pushing the test into the answers preserves the value.** -/
theorem Term.zipTest_eval : (fuel : Nat) → {Γ : UCtx ks} → {ℓ : Nat} → {o₁ o₂ : Lvl} →
    (p : Neu Δ Φ Γ .bool ℓ) → (t : Term Δ d Φ Γ τ js o₁) → (e : Term Δ d Φ Γ τ js o₂) →
    (r : (o : Lvl) × Term Δ d Φ Γ τ js o) → Term.zipTest fuel p t e = some r →
    ∀ (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js),
      r.2.eval κ ρ jκ = (Branch.ite p t e).eval κ ρ jκ
  | 0, _, _, _, _, _, _, _, _, h, _, _, _ => by simp [Term.zipTest] at h
  | fuel + 1, Γ, _, _, _, p, t, e, r, h, κ, ρ, jκ => by
    simp only [Term.zipTest] at h
    split at h
    · -- through a shared test
      rename_i r' hv
      cases h
      split at hv
      · rename_i vt ve hvt hve
        have et := Term.testView?_eval t vt hvt κ ρ jκ
        have ee := Term.testView?_eval e ve hve κ ρ jκ
        split at hv
        · rename_i hq
          have eq : (vt.q.eval κ ρ : Bool) = ve.q.eval κ ρ :=
            eq_of_heq ((Neu.same_eval vt.q ve.q hq).2 κ ρ)
          split at hv
          · rename_i r₁ r₂ h₁ h₂
            cases hv
            have e₁ := Term.zipTest_eval fuel p vt.t ve.t r₁ h₁ κ ρ jκ
            have e₂ := Term.zipTest_eval fuel p vt.e ve.e r₂ h₂ κ ρ jκ
            simp only [Branch.eval] at et ee e₁ e₂ ⊢
            simp only [Term.eval, Branch.eval]
            rw [et, ee, ← eq]
            revert e₁ e₂
            cases (p.eval κ ρ : Bool) <;> cases (vt.q.eval κ ρ : Bool) <;> intro e₁ e₂ <;>
              simp only [e₁, e₂]
          · cases hv
        · cases hv
      · cases hv
    · split at h
      · -- two answers
        rename_i b a _
        split at h
        · rename_i hab
          cases h
          have := eq_of_heq ((PExpr.same_eval a b hab).2 κ ρ)
          simp only [Term.eval, Branch.eval]
          cases (p.eval κ ρ : Bool) <;> simp [this]
        · cases h
          simp only [Term.eval, Branch.eval, PExpr.eval, Neu.eval]
      · -- two record case analyses
        rename_i t₁ fs₁ ℓ₁ o₁' us₁ n₁ b₁ t₂ fs₂ ℓ₂ o₂' us₂ n₂ b₂ _
        split at h
        · rename_i hs
          split at h
          · rename_i hu
            split at h
            · rename_i p' hp'
              split at h
              · rename_i r' hr
                cases h
                have hty := (Neu.same_eval n₂ n₁ hs).1
                have hn := (Neu.same_eval n₂ n₁ hs).2 κ ρ
                cases hty
                cases hu
                simp only [Term.castCtx_rfl] at hr
                have hn' : n₂.eval κ ρ = n₁.eval κ ρ := eq_of_heq hn
                simp only [Term.eval]
                rw [Term.zipTest_eval fuel p' b₁ b₂ r' hr κ _ jκ]
                have hpe := Neu.rename_eval (KRen.Agree.id κ)
                  (URen.Agree.wkN ρ (UCtx.annot d (t₁ :: fs₁.toList) us₁)
                    (UEnv.ofDL d _ us₁ (Tuple.cons (n₁.eval κ ρ).1
                      (Fields.toDL fs₁ (n₁.eval κ ρ).2)))) p hp'
                simp only [Branch.eval, hpe]
                cases (p.eval κ ρ : Bool) <;> simp only [Term.eval, hn']
              · cases h
            · cases h
          · cases h
        · cases h
      · cases h

/-- The statement `Term.zipTest` builds makes no call. -/
theorem Term.zipTest_numCalls : (fuel : Nat) → {Γ : UCtx ks} → {ℓ : Nat} → {o₁ o₂ : Lvl} →
    (p : Neu Δ Φ Γ .bool ℓ) → (t : Term Δ d Φ Γ τ js o₁) → (e : Term Δ d Φ Γ τ js o₂) →
    (r : (o : Lvl) × Term Δ d Φ Γ τ js o) → Term.zipTest fuel p t e = some r →
    r.2.numCalls = 0
  | 0, _, _, _, _, _, _, _, _, h => by simp [Term.zipTest] at h
  | fuel + 1, Γ, _, _, _, p, t, e, r, h => by
    simp only [Term.zipTest] at h
    split at h
    · rename_i r' hv
      cases h
      split at hv
      · split at hv
        · split at hv
          · rename_i r₁ r₂ h₁ h₂
            cases hv
            simp only [Term.numCalls, Branch.numCalls,
              Term.zipTest_numCalls fuel p _ _ r₁ h₁,
              Term.zipTest_numCalls fuel p _ _ r₂ h₂]
          · cases hv
        · cases hv
      · cases hv
    · split at h
      · split at h
        · cases h; rfl
        · cases h; rfl
      · split at h
        · split at h
          · split at h
            · rename_i p' _
              split at h
              · rename_i r' hr
                cases h
                simp only [Term.numCalls]
                exact Term.zipTest_numCalls fuel p' _ _ r' hr
              · cases h
            · cases h
          · cases h
        · cases h
      · cases h

/-- Is the statement an answer `ret a`? -/
def Term.isRet {Γ : UCtx ks} {o : Lvl} : Term Δ d Φ Γ τ js o → Bool
  | .ret _ => true
  | _ => false

/-- How deep `Term.zipTest` looks. -/
def Term.zipFuel : Nat := 64

/-- A branch as a statement, with `Term.zipTest` applied when it is an `if` whose arms are not
    both answers, and when it keeps the level. -/
def Term.zipBranch {Γ : UCtx ks} {ℓ : Nat} : Branch Δ d Φ Γ τ js ℓ → Term Δ d Φ Γ τ js (some ℓ)
  | .ite p t e =>
    if t.isRet && e.isRet then .branch (.ite p t e) else
    match Term.zipTest Term.zipFuel p t e with
    | some r => if h : r.1 = _ then r.2.castLvl h else .branch (.ite p t e)
    | none => .branch (.ite p t e)
  | br => .branch br

theorem Term.zipBranch_eval {Γ : UCtx ks} {ℓ : Nat} (br : Branch Δ d Φ Γ τ js ℓ)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    (Term.zipBranch br).eval κ ρ jκ = br.eval κ ρ jκ := by
  unfold Term.zipBranch
  split
  · rename_i p t e
    split
    · rfl
    · split
      · rename_i r hr
        split
        · rw [Term.eval_castLvl]
          exact Term.zipTest_eval _ p t e r hr κ ρ jκ
        · rfl
      · rfl
  · rfl

theorem Term.numCalls_zipBranch {Γ : UCtx ks} {ℓ : Nat} (br : Branch Δ d Φ Γ τ js ℓ) :
    (Term.zipBranch br).numCalls ≤ br.numCalls := by
  unfold Term.zipBranch
  split
  · rename_i p t e
    split
    · exact Nat.le_refl _
    · split
      · rename_i r hr
        split
        · rw [Term.numCalls_castLvl, Term.zipTest_numCalls _ p t e r hr]
          exact Nat.zero_le _
        · exact Nat.le_refl _
      · exact Nat.le_refl _
  · exact Nat.le_refl _

end Zip

/-! ## The walk -/

mutual
/-- `Term.zipTestWalk` in a value. -/
def Val.zipTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ τ o → Val Δ d Φ Γ τ o
  | _, _, _, _, _, .lam b => .lam b.zipTestWalk
  | _, _, _, _, _, .thunk_mk b => .thunk_mk b.zipTestWalk
  | _, _, _, _, _, .lazy_mk b => .lazy_mk b.zipTestWalk
  | _, _, _, _, _, .record_mk args => .record_mk args
  | _, _, _, _, _, .union_mk ix args => .union_mk ix args
  | _, _, _, _, _, .array_mk es => .array_mk es
  | _, _, _, _, _, .list_mk es => .list_mk es
  | _, _, _, _, _, .data_in b j e => .data_in b j e
/-- `Term.zipTestWalk` in a body. -/
def Body.zipTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → Body Δ d Φ Γ bs τ o → Body Δ d Φ Γ bs τ o
  | _, _, _, _, _, _, .closed t => .closed t.zipTestWalk
  | _, _, _, _, _, _, .opened t h => .opened t.zipTestWalk h
/-- `Term.zipTestWalk` in a computation. -/
def Comp.zipTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    Comp Δ d Φ Γ τ ℓ → Comp Δ d Φ Γ τ ℓ
  | _, _, _, _, _, .app f a h => .app f a h
  | _, _, _, _, _, .share n => .share n
  | _, _, _, _, _, .nat_rec n z s h => .nat_rec n z s.zipTestWalk h
  | _, _, _, _, _, .array_foldl a z s h => .array_foldl a z s.zipTestWalk h
  | _, _, _, _, _, .data_rec b ρ us brs j e h =>
      .data_rec b ρ us (fun i => (brs i).zipTestWalk) j e h
  | _, _, _, _, _, .data_brec b ρ k us brs j e h =>
      .data_brec b ρ k us (fun i => (brs i).zipTestWalk) j e h
  | _, _, _, _, _, .thunk_force e => .thunk_force e
  | _, _, _, _, _, .lazy_force e => .lazy_force e
/-- **A test is pushed into the answers when both arms of an `if` make the same tests**
    (`Term.zipTest`), at every `if` of a statement, bottom-up. -/
def Term.zipTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → Term Δ d Φ Γ τ js o → Term Δ d Φ Γ τ js o
  | _, _, _, _, _, _, .ret e => .ret e
  | _, _, _, _, _, _, .letV u v b => .letV u v.zipTestWalk b.zipTestWalk
  | _, _, _, _, _, _, .letE u c b => .letE u c.zipTestWalk b.zipTestWalk
  | _, _, _, _, _, _, .record_casesOn us n b => .record_casesOn us n b.zipTestWalk
  | _, _, _, _, _, _, .branch br => Term.zipBranch br.zipTestWalk
  | _, _, _, _, _, _, .jump j e => .jump j e
/-- `Term.zipTestWalk` in a branch. -/
def Branch.zipTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → Branch Δ d Φ Γ τ js ℓ
  | _, _, _, _, _, _, .ite c t e => .ite c t.zipTestWalk e.zipTestWalk
  | _, _, _, _, _, _, .enum_casesOn e bs => .enum_casesOn e (fun i => (bs i).zipTestWalk)
  | _, _, _, _, _, _, .union_casesOn e bs => .union_casesOn e bs.zipTestWalk
  | _, _, _, _, _, _, .join σ u uₓ body main =>
      .join σ u uₓ body.zipTestWalk main.zipTestWalk
/-- `Term.zipTestWalk` in the branches of a union's case analysis. -/
def Branches.zipTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → Branches Δ d Φ Γ cs τ js o
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ =>
      .two us₁ us₂ b₁.zipTestWalk b₂.zipTestWalk
  | _, _, _, _, _, _, _, _, .cons us b bs => .cons us b.zipTestWalk bs.zipTestWalk
end

mutual
theorem Val.zipTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    v.zipTestWalk.eval κ ρ = v.eval κ ρ
  | _, _, _, _, _, .lam b, κ, ρ => by
      simp only [Val.zipTestWalk, Val.eval]; funext x; rw [Body.zipTestWalk_eval b κ ρ]
  | _, _, _, _, _, .thunk_mk b, κ, ρ => by
      simp only [Val.zipTestWalk, Val.eval]; rw [Body.zipTestWalk_eval b κ ρ]
  | _, _, _, _, _, .lazy_mk b, κ, ρ => by
      simp only [Val.zipTestWalk, Val.eval]; rw [Body.zipTestWalk_eval b κ ρ]
  | _, _, _, _, _, .record_mk _, _, _ => rfl
  | _, _, _, _, _, .union_mk _ _, _, _ => rfl
  | _, _, _, _, _, .array_mk _, _, _ => rfl
  | _, _, _, _, _, .list_mk _, _, _ => rfl
  | _, _, _, _, _, .data_in _ _ _, _, _ => rfl
  termination_by structural _ _ _ _ _ x _ _ => x
theorem Body.zipTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (vs : UEnv Δ bs) → b.zipTestWalk.eval κ ρ vs = b.eval κ ρ vs
  | _, _, _, _, _, _, .closed t, _, _, _ => by
      simp only [Body.zipTestWalk, Body.eval]; exact Term.zipTestWalk_eval t _ _ _
  | _, _, _, _, _, _, .opened t _, _, _, _ => by
      simp only [Body.zipTestWalk, Body.eval]; exact Term.zipTestWalk_eval t _ _ _
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Comp.zipTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    c.zipTestWalk.eval κ ρ = c.eval κ ρ
  | _, _, _, _, _, .app _ _ _, _, _ => rfl
  | _, _, _, _, _, .share _, _, _ => rfl
  | _, _, _, _, _, .nat_rec n z s _, κ, ρ => by
      simp only [Comp.zipTestWalk, Comp.eval]
      congr 1; funext k acc; exact Body.zipTestWalk_eval s κ ρ _
  | _, _, _, _, _, .array_foldl a z s _, κ, ρ => by
      simp only [Comp.zipTestWalk, Comp.eval]
      congr 1; funext acc x; exact Body.zipTestWalk_eval s κ ρ _
  | _, _, _, _, _, .data_rec b ρt us brs j e _, κ, ρ => by
      simp only [Comp.zipTestWalk, Comp.eval]
      congr 1; funext i x; exact Body.zipTestWalk_eval (brs i) κ ρ _
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, κ, ρ => by
      simp only [Comp.zipTestWalk, Comp.eval]
      congr 1; funext i x; exact Body.zipTestWalk_eval (brs i) κ ρ _
  | _, _, _, _, _, .thunk_force _, _, _ => rfl
  | _, _, _, _, _, .lazy_force _, _, _ => rfl
  termination_by structural _ _ _ _ _ x _ _ => x
/-- **Pushing a test into the answers when both arms of an `if` make the same tests does not
    change the value of a statement.** -/
theorem Term.zipTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → t.zipTestWalk.eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, .ret _, _, _, _ => rfl
  | _, _, _, _, _, _, .letV u v b, κ, ρ, jκ => by
      simp only [Term.zipTestWalk, Term.eval, Val.zipTestWalk_eval v, Term.zipTestWalk_eval b]
  | _, _, _, _, _, _, .letE u c b, κ, ρ, jκ => by
      simp only [Term.zipTestWalk, Term.eval, Comp.zipTestWalk_eval c, Term.zipTestWalk_eval b]
  | _, _, _, _, _, _, .record_casesOn us n b, κ, ρ, jκ => by
      simp only [Term.zipTestWalk, Term.eval, Term.zipTestWalk_eval b]
  | _, _, _, _, _, _, .branch br, κ, ρ, jκ => by
      simp only [Term.zipTestWalk]
      rw [Term.zipBranch_eval]
      simp only [Term.eval, Branch.zipTestWalk_eval br]
  | _, _, _, _, _, _, .jump _ _, _, _, _ => rfl
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Branch.zipTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → br.zipTestWalk.eval κ ρ jκ = br.eval κ ρ jκ
  | _, _, _, _, _, _, .ite c t e, κ, ρ, jκ => by
      simp only [Branch.zipTestWalk, Branch.eval, Term.zipTestWalk_eval t, Term.zipTestWalk_eval e]
  | _, _, _, _, _, _, .enum_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.zipTestWalk, Branch.eval]
      exact Term.zipTestWalk_eval _ _ _ _
  | _, _, _, _, _, _, .union_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.zipTestWalk, Branch.eval]
      exact Branches.zipTestWalk_eval bs κ ρ jκ _
  | _, _, _, _, _, _, .join σ u uₓ body main, κ, ρ, jκ => by
      simp only [Branch.zipTestWalk, Branch.eval, Branch.zipTestWalk_eval main,
        Term.zipTestWalk_eval body]
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Branches.zipTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
      ∀ x, br.zipTestWalk.eval κ ρ jκ x = br.eval κ ρ jκ x
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, κ, ρ, jκ, x => by
      simp only [Branches.zipTestWalk, Branches.eval, Term.zipTestWalk_eval b₁,
        Term.zipTestWalk_eval b₂]
  | _, _, _, _, _, _, _, _, .cons us b bs, κ, ρ, jκ, x => by
      simp only [Branches.zipTestWalk, Branches.eval, Term.zipTestWalk_eval b,
        Branches.zipTestWalk_eval bs]
  termination_by structural _ _ _ _ _ _ _ _ x _ _ _ _ => x
end

/-! ## No call is added -/

mutual
theorem Val.numCalls_zipTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → v.zipTestWalk.numCalls ≤ v.numCalls
  | _, _, _, _, _, .lam b => by
      simp only [Val.zipTestWalk, Val.numCalls]; exact Body.numCalls_zipTestWalk b
  | _, _, _, _, _, .thunk_mk b => by
      simp only [Val.zipTestWalk, Val.numCalls]; exact Body.numCalls_zipTestWalk b
  | _, _, _, _, _, .lazy_mk b => by
      simp only [Val.zipTestWalk, Val.numCalls]; exact Body.numCalls_zipTestWalk b
  | _, _, _, _, _, .record_mk _ => Nat.le_refl _
  | _, _, _, _, _, .union_mk _ _ => Nat.le_refl _
  | _, _, _, _, _, .array_mk _ => Nat.le_refl _
  | _, _, _, _, _, .list_mk _ => Nat.le_refl _
  | _, _, _, _, _, .data_in _ _ _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
theorem Body.numCalls_zipTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} →
    {τ : Ty ks} → {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → b.zipTestWalk.numCalls ≤ b.numCalls
  | _, _, _, _, _, _, .closed t => by
      simp only [Body.zipTestWalk, Body.numCalls]; exact Term.numCalls_zipTestWalk t
  | _, _, _, _, _, _, .opened t _ => by
      simp only [Body.zipTestWalk, Body.numCalls]; exact Term.numCalls_zipTestWalk t
  termination_by structural _ _ _ _ _ _ x => x
theorem Comp.numCalls_zipTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → c.zipTestWalk.numCalls ≤ c.numCalls
  | _, _, _, _, _, .app _ _ _ => Nat.le_refl _
  | _, _, _, _, _, .share _ => Nat.le_refl _
  | _, _, _, _, _, .nat_rec _ _ s _ => by
      simp only [Comp.zipTestWalk, Comp.numCalls]; exact Body.numCalls_zipTestWalk s
  | _, _, _, _, _, .array_foldl _ _ s _ => by
      simp only [Comp.zipTestWalk, Comp.numCalls]; exact Body.numCalls_zipTestWalk s
  | _, _, _, _, _, .data_rec _ _ _ brs _ _ _ => by
      simp only [Comp.zipTestWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_zipTestWalk (brs i))
  | _, _, _, _, _, .data_brec _ _ _ _ brs _ _ _ => by
      simp only [Comp.zipTestWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_zipTestWalk (brs i))
  | _, _, _, _, _, .thunk_force _ => Nat.le_refl _
  | _, _, _, _, _, .lazy_force _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
/-- **Pushing a test into the answers adds no call.** -/
theorem Term.numCalls_zipTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) →
    t.zipTestWalk.numCalls ≤ t.numCalls
  | _, _, _, _, _, _, .ret _ => Nat.le_refl _
  | _, _, _, _, _, _, .letV u v b => by
      simp only [Term.zipTestWalk, Term.numCalls]
      have := Val.numCalls_zipTestWalk v; have := Term.numCalls_zipTestWalk b; omega
  | _, _, _, _, _, _, .letE u c b => by
      simp only [Term.zipTestWalk, Term.numCalls]
      have := Comp.numCalls_zipTestWalk c; have := Term.numCalls_zipTestWalk b; omega
  | _, _, _, _, _, _, .record_casesOn us n b => by
      simp only [Term.zipTestWalk, Term.numCalls]; exact Term.numCalls_zipTestWalk b
  | _, _, _, _, _, _, .branch br => by
      simp only [Term.zipTestWalk]
      have := Term.numCalls_zipBranch br.zipTestWalk
      have := Branch.numCalls_zipTestWalk br
      simp only [Term.numCalls]; omega
  | _, _, _, _, _, _, .jump _ _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ _ x => x
theorem Branch.numCalls_zipTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {τ : Ty ks} → {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) →
    br.zipTestWalk.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, .ite c t e => by
      simp only [Branch.zipTestWalk, Branch.numCalls]
      have := Term.numCalls_zipTestWalk t; have := Term.numCalls_zipTestWalk e; omega
  | _, _, _, _, _, _, .enum_casesOn e bs => by
      simp only [Branch.zipTestWalk, Branch.numCalls]
      exact Fin.sumNat_le _ (fun i => Term.numCalls_zipTestWalk (bs i))
  | _, _, _, _, _, _, .union_casesOn e bs => by
      simp only [Branch.zipTestWalk, Branch.numCalls]; exact Branches.numCalls_zipTestWalk bs
  | _, _, _, _, _, _, .join σ u uₓ body main => by
      simp only [Branch.zipTestWalk, Branch.numCalls]
      have := Term.numCalls_zipTestWalk body; have := Branch.numCalls_zipTestWalk main; omega
  termination_by structural _ _ _ _ _ _ x => x
theorem Branches.numCalls_zipTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → br.zipTestWalk.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ => by
      simp only [Branches.zipTestWalk, Branches.numCalls]
      have := Term.numCalls_zipTestWalk b₁; have := Term.numCalls_zipTestWalk b₂; omega
  | _, _, _, _, _, _, _, _, .cons us b bs => by
      simp only [Branches.zipTestWalk, Branches.numCalls]
      have := Term.numCalls_zipTestWalk b; have := Branches.numCalls_zipTestWalk bs; omega
  termination_by structural _ _ _ _ _ _ _ _ x => x
end

end LeanScript

end
