module

public import LeanScript.Term.RenameEval
public import LeanScript.Term.Occ

@[expose] public section

set_option autoImplicit false

/-!
# Dead-code elimination and usage annotation

`Term.dce t` recounts the usage of every `letV`, `letE`, closure parameter and join point of
`t` (`LeanScript.Term.Occ`), bottom-up, and

* **drops** every `letV`, `letE` and join point that is used `0` times, as long as this does
  not change the level of the statement (a dead binding that is the only mention of an outer
  unknown is kept: dropping it could make an open body closed, and so turn operands that are
  open into closed ones, which only the normaliser may evaluate).  The language is pure and
  total, so dropping a computation only changes the running time;
* **re-annotates** the others with their usage `1` or `ω` (`Usage1ω`), and closure parameters
  with `0`, `1` or `ω`.

The binder of a dropped or re-annotated variable is changed by a partial renaming
(`LeanScript.Term.Rename`), which cannot fail when the count is right; when it does fail, the
binding is kept as it was.  So `dce` never changes the value: `Term.dce_eval`.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-- Change the level index of a statement along an equation. -/
def Term.castLvl {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o o' : Lvl}
    (h : o = o') (t : Term Δ d Φ Γ τ js o) : Term Δ d Φ Γ τ js o' :=
  h ▸ t

/-- Change the level index of a branch along an equation. -/
def Branch.castLvl {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {ℓ ℓ' : Nat}
    (h : ℓ = ℓ') (br : Branch Δ d Φ Γ τ js ℓ) : Branch Δ d Φ Γ τ js ℓ' :=
  h ▸ br

@[simp] theorem Term.eval_castLvl {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} {o o' : Lvl} (h : o = o') (t : Term Δ d Φ Γ τ js o) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) : (t.castLvl h).eval κ ρ jκ = t.eval κ ρ jκ := by
  subst h; rfl

@[simp] theorem Branch.eval_castLvl {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} {ℓ ℓ' : Nat} (h : ℓ = ℓ') (br : Branch Δ d Φ Γ τ js ℓ) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) : (br.castLvl h).eval κ ρ jκ = br.eval κ ρ jκ := by
  subst h; rfl

/-- Re-annotate the parameter of a body with one parameter. -/
def Body.reuse1 {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {u : Usage01ω} {ℓ : Nat}
    {o : Lvl} (u' : Usage01ω) :
    Body Δ d Φ Γ [⟨σ, u, ℓ⟩] τ o → Option (Body Δ d Φ Γ [⟨σ, u', ℓ⟩] τ o)
  | .closed t => (t.rename KRen.id (URen.reuse u') JRen.id).map .closed
  | .opened t h => (t.rename KRen.id (URen.reuse u') JRen.id).map (fun t => .opened t h)

/-- The occurrences of the parameter of a body with one parameter. -/
def Body.countParam {d : Nat} {Φ : KCtx ks} {Γ bs : UCtx ks} {τ : Ty ks} {o : Lvl} :
    Body Δ d Φ Γ bs τ o → Usage01ω
  | .closed t => t.countU 0
  | .opened t _ => t.countU 0

mutual
/-- Dead-code elimination in a value. -/
def Val.dce : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ τ o → Val Δ d Φ Γ τ o
  | _, _, _, _, _, .lam b =>
      let b := b.dce
      match b.reuse1 b.countParam with
      | some b' => .lam b'
      | none => .lam b
  | _, _, _, _, _, .thunk_mk b => .thunk_mk b.dce
  | _, _, _, _, _, .lazy_mk b => .lazy_mk b.dce
  | _, _, _, _, _, .record_mk args => .record_mk args
  | _, _, _, _, _, .union_mk ix args => .union_mk ix args
  | _, _, _, _, _, .array_mk es => .array_mk es
  | _, _, _, _, _, .list_mk es => .list_mk es
  | _, _, _, _, _, .data_in b j e => .data_in b j e
/-- Dead-code elimination in a body. -/
def Body.dce : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Body Δ d Φ Γ bs τ o → Body Δ d Φ Γ bs τ o
  | _, _, _, _, _, _, .closed t => .closed t.dce
  | _, _, _, _, _, _, .opened t h => .opened t.dce h
/-- Dead-code elimination in a computation. -/
def Comp.dce : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    Comp Δ d Φ Γ τ ℓ → Comp Δ d Φ Γ τ ℓ
  | _, _, _, _, _, .app f a h => .app f a h
  | _, _, _, _, _, .share n => .share n
  | _, _, _, _, _, .nat_rec n z s h => .nat_rec n z s.dce h
  | _, _, _, _, _, .array_foldl a z s h => .array_foldl a z s.dce h
  | _, _, _, _, _, .data_rec b ρ us brs j e h => .data_rec b ρ us (fun i => (brs i).dce) j e h
  | _, _, _, _, _, .data_brec b ρ k us brs j e h =>
      .data_brec b ρ k us (fun i => (brs i).dce) j e h
  | _, _, _, _, _, .thunk_force e => .thunk_force e
  | _, _, _, _, _, .lazy_force e => .lazy_force e
/-- Dead-code elimination in a statement. -/
def Term.dce : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {o : Lvl} → Term Δ d Φ Γ τ js o → Term Δ d Φ Γ τ js o
  | _, _, _, _, _, _, .ret e => .ret e
  | _, _, _, _, _, _, .letV (o := o) (o' := o') u v b =>
      let v := v.dce
      let b := b.dce
      let n := b.countK 0
      if hn : n = .zero then
        if ho : o' = Lvl.meet o o' then
          match b.rename KRen.drop URen.id JRen.id with
          | some b' => b'.castLvl ho
          | none => .letV u v b
        else .letV u v b
      else
        match b.rename (KRen.reuse (n.toUsage1ω hn)) URen.id JRen.id with
        | some b' => .letV (n.toUsage1ω hn) v b'
        | none => .letV u v b
  | _, _, _, _, _, _, .letE (ℓ := ℓ) (o' := o') u c b =>
      let c := c.dce
      let b := b.dce
      let n := b.countU 0
      if hn : n = .zero then
        if ho : o' = some (Lvl.meetL ℓ o') then
          match b.rename KRen.id URen.drop JRen.id with
          | some b' => b'.castLvl ho
          | none => .letE u c b
        else .letE u c b
      else
        match b.rename KRen.id (URen.reuse (n.toUsage1ω hn).toUsage01ω) JRen.id with
        | some b' => .letE (n.toUsage1ω hn) c b'
        | none => .letE u c b
  | _, _, _, _, _, _, .record_casesOn us n b => .record_casesOn us n b.dce
  | _, _, _, _, _, _, .branch br => .branch br.dce
  | _, _, _, _, _, _, .jump j e => .jump j e
/-- Dead-code elimination in a branch; a join point that is never jumped to is dropped. -/
def Branch.dce : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → Branch Δ d Φ Γ τ js ℓ
  | _, _, _, _, _, _, .ite c t e => .ite c t.dce e.dce
  | _, _, _, _, _, _, .enum_casesOn e bs => .enum_casesOn e (fun i => (bs i).dce)
  | _, _, _, _, _, _, .union_casesOn e bs => .union_casesOn e bs.dce
  | _, _, _, _, _, _, .join (o := o) (ℓ := ℓ) σ u uₓ body main =>
      let body := body.dce
      let main := main.dce
      let n := main.countJ 0
      if hn : n = .zero then
        if ho : ℓ = Lvl.meetL ℓ o then
          match main.rename KRen.id URen.id JRen.drop with
          | some main' => main'.castLvl ho
          | none => .join σ u uₓ body main
        else .join σ u uₓ body main
      else
        let nₓ := body.countU 0
        match main.rename KRen.id URen.id (JRen.reuse (n.toUsage1ω hn)),
            body.rename KRen.id (URen.reuse nₓ) JRen.id with
        | some main', some body' => .join σ (n.toUsage1ω hn) nₓ body' main'
        | some main', none => .join σ (n.toUsage1ω hn) uₓ body main'
        | none, _ => .join σ u uₓ body main
/-- Dead-code elimination in the branches of a union's case analysis. -/
def Branches.dce : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → Branches Δ d Φ Γ cs τ js o
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ => .two us₁ us₂ b₁.dce b₂.dce
  | _, _, _, _, _, _, _, _, .cons us b bs => .cons us b.dce bs.dce
end

/-! ## `dce` preserves the value -/

theorem Body.reuse1_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {u : Usage01ω}
    {ℓ : Nat} {o : Lvl} {u' : Usage01ω} {b : Body Δ d Φ Γ [⟨σ, u, ℓ⟩] τ o}
    {b' : Body Δ d Φ Γ [⟨σ, u', ℓ⟩] τ o}
    (h : b.reuse1 u' = some b') (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (v : Ty.Den Δ σ) :
    b'.eval κ ρ (Tuple.cons v Tuple.nil) = b.eval κ ρ (Tuple.cons v Tuple.nil) := by
  cases b with
  | closed t =>
      simp only [Body.reuse1, Option.map_eq_some_iff] at h
      obtain ⟨t', ht, rfl⟩ := h
      exact Term.rename_eval (KRen.Agree.id _) (URen.Agree.reuse u' v _) (JRen.Agree.id _) t ht
  | opened t =>
      simp only [Body.reuse1, Option.map_eq_some_iff] at h
      obtain ⟨t', ht, rfl⟩ := h
      exact Term.rename_eval (KRen.Agree.id _) (URen.Agree.reuse u' v _) (JRen.Agree.id _) t ht

mutual
theorem Val.dce_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    (v : Val Δ d Φ Γ τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → v.dce.eval κ ρ = v.eval κ ρ
  | _, _, _, _, _, .lam b, κ, ρ => by
      simp only [Val.dce]
      split
      · rename_i b' hb
        simp only [Val.eval]
        funext x
        rw [Body.reuse1_eval hb κ ρ x, Body.dce_eval b κ ρ]
      · simp only [Val.eval]
        funext x
        rw [Body.dce_eval b κ ρ]
  | _, _, _, _, _, .thunk_mk b, κ, ρ => by
      simp only [Val.dce, Val.eval]; rw [Body.dce_eval b κ ρ]
  | _, _, _, _, _, .lazy_mk b, κ, ρ => by
      simp only [Val.dce, Val.eval]; rw [Body.dce_eval b κ ρ]
  | _, _, _, _, _, .record_mk _, _, _ => rfl
  | _, _, _, _, _, .union_mk _ _, _, _ => rfl
  | _, _, _, _, _, .array_mk _, _, _ => rfl
  | _, _, _, _, _, .list_mk _, _, _ => rfl
  | _, _, _, _, _, .data_in _ _ _, _, _ => rfl
  termination_by structural _ _ _ _ _ x _ _ => x
theorem Body.dce_eval : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (vs : UEnv Δ bs) → b.dce.eval κ ρ vs = b.eval κ ρ vs
  | _, _, _, _, _, _, .closed t, κ, _, vs => by
      simp only [Body.dce, Body.eval]; exact Term.dce_eval t _ _ _
  | _, _, _, _, _, _, .opened t _, κ, ρ, vs => by
      simp only [Body.dce, Body.eval]; exact Term.dce_eval t _ _ _
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Comp.dce_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    (c : Comp Δ d Φ Γ τ ℓ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → c.dce.eval κ ρ = c.eval κ ρ
  | _, _, _, _, _, .app _ _ _, _, _ => rfl
  | _, _, _, _, _, .share _, _, _ => rfl
  | _, _, _, _, _, .nat_rec n z s _, κ, ρ => by
      simp only [Comp.dce, Comp.eval]
      congr 1; funext k acc; exact Body.dce_eval s κ ρ _
  | _, _, _, _, _, .array_foldl a z s _, κ, ρ => by
      simp only [Comp.dce, Comp.eval]
      congr 1; funext acc x; exact Body.dce_eval s κ ρ _
  | _, _, _, _, _, .data_rec b ρt us brs j e _, κ, ρ => by
      simp only [Comp.dce, Comp.eval]
      congr 1; funext i x; exact Body.dce_eval (brs i) κ ρ _
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, κ, ρ => by
      simp only [Comp.dce, Comp.eval]
      congr 1; funext i x; exact Body.dce_eval (brs i) κ ρ _
  | _, _, _, _, _, .thunk_force _, _, _ => rfl
  | _, _, _, _, _, .lazy_force _, _, _ => rfl
  termination_by structural _ _ _ _ _ x _ _ => x
theorem Term.dce_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → t.dce.eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, .ret _, _, _, _ => rfl
  | _, _, _, _, _, _, .letV u v b, κ, ρ, jκ => by
      simp only [Term.dce]
      split
      · split
        · split
          · rename_i b' hb
            rw [Term.eval_castLvl, Term.rename_eval (KRen.Agree.drop (b := ⟨_, u, _, true⟩) (v.eval κ ρ) κ)
              (URen.Agree.id _) (JRen.Agree.id _) _ hb]
            simp only [Term.eval, Term.dce_eval b]
          · simp only [Term.eval, Term.dce_eval b, Val.dce_eval v]
        · simp only [Term.eval, Term.dce_eval b, Val.dce_eval v]
      · split
        · rename_i b' hb
          simp only [Term.eval]
          rw [Term.rename_eval (KRen.Agree.reuse _ _ _) (URen.Agree.id _) (JRen.Agree.id _) _ hb]
          simp only [Term.dce_eval b, Val.dce_eval v]
        · simp only [Term.eval, Term.dce_eval b, Val.dce_eval v]
  | _, _, _, _, _, _, .letE u c b, κ, ρ, jκ => by
      simp only [Term.dce]
      split
      · split
        · split
          · rename_i b' hb
            rw [Term.eval_castLvl, Term.rename_eval (KRen.Agree.id _)
              (URen.Agree.drop (c.eval κ ρ) ρ) (JRen.Agree.id _) _ hb]
            simp only [Term.eval, Term.dce_eval b]
          · simp only [Term.eval, Term.dce_eval b, Comp.dce_eval c]
        · simp only [Term.eval, Term.dce_eval b, Comp.dce_eval c]
      · split
        · rename_i b' hb
          simp only [Term.eval]
          rw [Term.rename_eval (KRen.Agree.id _) (URen.Agree.reuse _ _ _) (JRen.Agree.id _) _ hb]
          simp only [Term.dce_eval b, Comp.dce_eval c]
        · simp only [Term.eval, Term.dce_eval b, Comp.dce_eval c]
  | _, _, _, _, _, _, .record_casesOn us n b, κ, ρ, jκ => by
      simp only [Term.dce, Term.eval, Term.dce_eval b]
  | _, _, _, _, _, _, .branch br, κ, ρ, jκ => by
      simp only [Term.dce, Term.eval, Branch.dce_eval br]
  | _, _, _, _, _, _, .jump _ _, _, _, _ => rfl
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Branch.dce_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → br.dce.eval κ ρ jκ = br.eval κ ρ jκ
  | _, _, _, _, _, _, .ite c t e, κ, ρ, jκ => by
      simp only [Branch.dce, Branch.eval, Term.dce_eval t, Term.dce_eval e]
  | _, _, _, _, _, _, .enum_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.dce, Branch.eval]; exact Term.dce_eval _ _ _ _
  | _, _, _, _, _, _, .union_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.dce, Branch.eval]; exact Branches.dce_eval bs κ ρ jκ _
  | _, _, _, _, _, _, .join σ u uₓ body main, κ, ρ, jκ => by
      simp only [Branch.dce]
      split
      · split
        · split
          · rename_i main' hm
            rw [Branch.eval_castLvl, Branch.rename_eval (KRen.Agree.id _) (URen.Agree.id _)
              (JRen.Agree.drop (fun v => body.eval κ (Tuple.cons v ρ) jκ) jκ) _ hm]
            simp only [Branch.eval, Branch.dce_eval main]
          · simp only [Branch.eval, Branch.dce_eval main, Term.dce_eval body]
        · simp only [Branch.eval, Branch.dce_eval main, Term.dce_eval body]
      · split
        · rename_i main' body' hm hb
          simp only [Branch.eval]
          rw [Branch.rename_eval (KRen.Agree.id _) (URen.Agree.id _) (JRen.Agree.reuse _ _ _) _ hm]
          have hf : (fun v => body'.eval κ (Tuple.cons v ρ) jκ) =
              (fun v => body.dce.eval κ (Tuple.cons v ρ) jκ) :=
            funext fun v => Term.rename_eval (KRen.Agree.id _) (URen.Agree.reuse _ _ _)
              (JRen.Agree.id _) _ hb
          rw [hf]
          simp only [Branch.dce_eval main, Term.dce_eval body]
        · rename_i main' hm _
          simp only [Branch.eval]
          rw [Branch.rename_eval (KRen.Agree.id _) (URen.Agree.id _) (JRen.Agree.reuse _ _ _) _ hm]
          simp only [Branch.dce_eval main, Term.dce_eval body]
        · simp only [Branch.eval, Branch.dce_eval main, Term.dce_eval body]
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Branches.dce_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
      ∀ x, br.dce.eval κ ρ jκ x = br.eval κ ρ jκ x
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, κ, ρ, jκ, x => by
      simp only [Branches.dce, Branches.eval, Term.dce_eval b₁, Term.dce_eval b₂]
  | _, _, _, _, _, _, _, _, .cons us b bs, κ, ρ, jκ, x => by
      simp only [Branches.dce, Branches.eval, Term.dce_eval b, Branches.dce_eval bs]
  termination_by structural _ _ _ _ _ _ _ _ x _ _ _ _ => x
end

/-- **Dead-code elimination preserves the value of a program.** -/
theorem Term.dce_run {τ : Ty ks} {o : Lvl} (t : Term Δ 0 [] [] τ [] o) : t.dce.run = t.run :=
  t.dce_eval _ _ _

end LeanScript

end
