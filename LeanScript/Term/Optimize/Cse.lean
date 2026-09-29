module

public import LeanScript.Term.Optimize.Atom

@[expose] public section

set_option autoImplicit false

/-!
# Common subexpressions, identical branches and trivial join points

Three rewrites of normal-form terms, each proved to preserve the value (`Term.eval`):

* **Common subexpression elimination** (`Term.cseLetE`): in `let x := c; b`, where `c` is a
  simple computation (`f a`, `t ()`, `force t` on atoms, `SimpleComp`), every `let y := c'; b'`
  inside `b`, at the same depth, whose computation is the same (`SimpleComp.key`) becomes `b'`
  with `y` renamed to `x`.  The language is pure and total, so the second computation always
  gives the value of the first.  (Computations inside closures, delays and loop bodies are
  not shared with the ones outside: they run at another depth.)
* **Identical branches** (`Term.mkBranch`): `if c then ret a else ret a`, `a` an atom, is
  `ret a` (the condition is pure, it need not be computed); `if c then ret a else ret b` is
  `ret (c ? a : b)` (`Neu.cond`, printed as a conditional expression) when neither `a` nor `b`
  is a conditional already.
* **Trivial join points** (`Branch.mkJoin`): a join point whose body is `ret a`, `a` an atom
  that is not its parameter, or `ret x`, `x` its parameter, is inlined: every `jump j v` to
  it becomes `ret a` (resp. `ret v`), and the join point, now unused, is dropped (`Branch.dce`).

A rewrite can change the level index of the statements it rewrites (it removes mentions of
unknowns); the traversals return the new level (`(o' : Lvl) × Term …`), and the rewrite is
kept only where the level of the enclosing statement comes out the same (decided on the spot,
as in `Term.dce`).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Weakening an unknown -/

/-- The unknown under more binders. -/
def UVar.wkN {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} : (bs : UCtx ks) → UVar Γ τ ℓ → UVar (bs ++ Γ) τ ℓ
  | [], x => x
  | _ :: bs, x => .tail (UVar.wkN bs x)

theorem UVar.wkN_get {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} :
    (bs : UCtx ks) → (x : UVar Γ τ ℓ) → (ρ : UEnv Δ Γ) → (vs : UEnv Δ bs) →
    UEnv.get (Tuple.append vs ρ) (x.wkN bs) = ρ.get x
  | [], _, _, _ => rfl
  | _ :: bs, x, ρ, vs => by
      rw [UVar.wkN, Tuple.append_cons, UEnv.get_cons_tail, UVar.wkN_get bs x ρ vs.tail]

/-- Two join points of the same type at the same position are the same. -/
theorem JVar.eq_of_index_eq : {js : JCtx ks} → {σ : Ty ks} → (x y : JVar js σ) →
    x.index = y.index → x = y
  | _ :: _, _, .head, .head, _ => rfl
  | _ :: _, _, .tail x, .tail y, h => by
      rw [JVar.eq_of_index_eq x y (by simpa [JVar.index] using h)]
  | _ :: _, _, .head, .tail _, h => by simp [JVar.index] at h
  | _ :: _, _, .tail _, .head, h => by simp [JVar.index] at h

/-! ## Common subexpression elimination -/

section Cse
variable {σ : Ty ks}

mutual
/-- Replace the computations of `s` (whose value is the unknown `x`) inside a statement at the
    same depth by `x`. -/
def Term.cse : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {o : Lvl} → UVar Γ σ d → SimpleComp Φ Γ σ → Term Δ d Φ Γ τ js o →
    (o' : Lvl) × Term Δ d Φ Γ τ js o'
  | _, _, _, _, _, _, _, _, .ret e => ⟨_, .ret e⟩
  | _, _, _, _, _, _, x, s, .letV u v b => ⟨_, .letV u v (Term.cse x (s.wkK _) b).2⟩
  | _, _, _, _, _, _, x, s, .letE (σ := σ') u c b =>
      let r := Term.cse x.tail (s.wkU _) b
      match SimpleComp.ofComp? c with
      | some s' =>
        if h : σ' = σ ∧ s'.key = s.key then
          match r.2.rename KRen.id (URen.subst (h.1 ▸ x) rfl) JRen.id with
          | some b' => ⟨_, b'⟩
          | none => ⟨_, .letE u c r.2⟩
        else ⟨_, .letE u c r.2⟩
      | none => ⟨_, .letE u c r.2⟩
  | _, _, _, _, _, _, x, s, .record_casesOn us n b =>
      ⟨_, .record_casesOn us n (Term.cse (x.wkN _) (s.wkUN _) b).2⟩
  | _, _, _, _, _, _, x, s, .branch br => ⟨_, .branch (Branch.cse x s br).2⟩
  | _, _, _, _, _, _, _, _, .jump j e => ⟨_, .jump j e⟩
/-- `Term.cse` in a branch. -/
def Branch.cse : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {ℓ : Nat} → UVar Γ σ d → SimpleComp Φ Γ σ → Branch Δ d Φ Γ τ js ℓ →
    (ℓ' : Nat) × Branch Δ d Φ Γ τ js ℓ'
  | _, _, _, _, _, _, x, s, .ite c t e => ⟨_, .ite c (Term.cse x s t).2 (Term.cse x s e).2⟩
  | _, _, _, _, _, _, x, s, .enum_casesOn e bs =>
      ⟨_, .enum_casesOn e (fun i => (Term.cse x s (bs i)).2)⟩
  | _, _, _, _, _, _, x, s, .union_casesOn e bs => ⟨_, .union_casesOn e (Branches.cse x s bs).2⟩
  | _, _, _, _, _, _, x, s, .join σ' u uₓ body main =>
      ⟨_, .join σ' u uₓ (Term.cse x.tail (s.wkU _) body).2 (Branch.cse x s main).2⟩
/-- `Term.cse` in the branches of a union's case analysis. -/
def Branches.cse : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    UVar Γ σ d → SimpleComp Φ Γ σ → Branches Δ d Φ Γ cs τ js o →
    (o' : Lvl) × Branches Δ d Φ Γ cs τ js o'
  | _, _, _, _, _, _, _, _, x, s, .two us₁ us₂ b₁ b₂ =>
      ⟨_, .two us₁ us₂ (Term.cse (x.wkN _) (s.wkUN _) b₁).2 (Term.cse (x.wkN _) (s.wkUN _) b₂).2⟩
  | _, _, _, _, _, _, _, _, x, s, .cons us b bs =>
      ⟨_, .cons us (Term.cse (x.wkN _) (s.wkUN _) b).2 (Branches.cse x s bs).2⟩
end

theorem Term.cse_letE_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ' τ : Ty ks} {js : JCtx ks}
    {ℓ : Nat} {o' : Lvl} (x : UVar Γ σ d) (s : SimpleComp Φ Γ σ) (u : Usage1ω)
    (c : Comp Δ d Φ Γ σ' ℓ) (b : Term Δ d Φ (⟨σ', u.toUsage01ω, d⟩ :: Γ) τ js o')
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) (hx : ρ.get x = s.eval κ ρ)
    (ih : (Term.cse x.tail (s.wkU _) b).2.eval κ (Tuple.cons (c.eval κ ρ) ρ) jκ =
      b.eval κ (Tuple.cons (c.eval κ ρ) ρ) jκ) :
    (Term.cse x s (.letE u c b)).2.eval κ ρ jκ = (Term.letE u c b).eval κ ρ jκ := by
  simp only [Term.cse]
  cases hs' : SimpleComp.ofComp? c with
  | none => simp only [Term.eval]; exact ih
  | some s' =>
    simp only
    by_cases h : σ' = σ ∧ s'.key = s.key
    · rw [dite_eq_left h]
      obtain ⟨h1, h2⟩ := h
      subst h1
      split
      · rename_i b' hb'
        rw [Term.rename_eval (KRen.Agree.id κ) (URen.Agree.subst x rfl ρ) (JRen.Agree.id jκ) _ hb']
        have hc : ρ.get x = c.eval κ ρ := by
          rw [hx, ← SimpleComp.ofComp?_eval c hs' κ ρ]
          exact eq_of_heq (SimpleComp.eval_eq_of_key_eq s s' h2.symm κ ρ)
        simp only [Term.eval]
        rw [hc]; exact ih
      · simp only [Term.eval]; exact ih
    · rw [dite_eq_right h]; simp only [Term.eval]; exact ih

mutual
theorem Term.cse_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (x : UVar Γ σ d) → (s : SimpleComp Φ Γ σ) →
    (t : Term Δ d Φ Γ τ js o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
    ρ.get x = s.eval κ ρ → (Term.cse x s t).2.eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, _, _, .ret _, _, _, _, _ => rfl
  | _, _, _, _, _, _, x, s, .letV u v b, κ, ρ, jκ, hx => by
      simp only [Term.cse, Term.eval]
      exact Term.cse_eval x (s.wkK _) b _ ρ jκ (by simp [hx])
  | _, _, _, _, _, _, x, s, .letE u c b, κ, ρ, jκ, hx =>
      Term.cse_letE_eval x s u c b κ ρ jκ hx
        (Term.cse_eval x.tail (s.wkU _) b κ _ jκ (by simp [hx]))
  | _, _, _, _, _, _, x, s, .record_casesOn us n b, κ, ρ, jκ, hx => by
      simp only [Term.cse, Term.eval]
      exact Term.cse_eval (x.wkN _) (s.wkUN _) b κ _ jκ
        (by rw [UVar.wkN_get, SimpleComp.wkUN_eval, hx])
  | _, _, _, _, _, _, x, s, .branch br, κ, ρ, jκ, hx => by
      simp only [Term.cse, Term.eval]
      exact Branch.cse_eval x s br κ ρ jκ hx
  | _, _, _, _, _, _, _, _, .jump _ _, _, _, _, _ => rfl
  termination_by structural _ _ _ _ _ _ _ _ t => t
theorem Branch.cse_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (x : UVar Γ σ d) → (s : SimpleComp Φ Γ σ) →
    (br : Branch Δ d Φ Γ τ js ℓ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
    ρ.get x = s.eval κ ρ → (Branch.cse x s br).2.eval κ ρ jκ = br.eval κ ρ jκ
  | _, _, _, _, _, _, x, s, .ite c t e, κ, ρ, jκ, hx => by
      simp only [Branch.cse, Branch.eval, Term.cse_eval x s t κ ρ jκ hx,
        Term.cse_eval x s e κ ρ jκ hx]
  | _, _, _, _, _, _, x, s, .enum_casesOn e bs, κ, ρ, jκ, hx => by
      simp only [Branch.cse, Branch.eval]
      exact Term.cse_eval x s _ κ ρ jκ hx
  | _, _, _, _, _, _, x, s, .union_casesOn e bs, κ, ρ, jκ, hx => by
      simp only [Branch.cse, Branch.eval]
      exact Branches.cse_eval x s bs κ ρ jκ hx _
  | _, _, _, _, _, _, x, s, .join σ' u uₓ body main, κ, ρ, jκ, hx => by
      simp only [Branch.cse, Branch.eval]
      rw [Branch.cse_eval x s main κ ρ _ hx]
      congr 2
      funext v
      exact Term.cse_eval x.tail (s.wkU _) body κ _ jκ (by simp [hx])
  termination_by structural _ _ _ _ _ _ _ _ br => br
theorem Branches.cse_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (x : UVar Γ σ d) → (s : SimpleComp Φ Γ σ) → (br : Branches Δ d Φ Γ cs τ js o) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → ρ.get x = s.eval κ ρ →
    ∀ v, (Branches.cse x s br).2.eval κ ρ jκ v = br.eval κ ρ jκ v
  | _, _, _, _, _, _, _, _, x, s, .two us₁ us₂ b₁ b₂, κ, ρ, jκ, hx, v => by
      simp only [Branches.cse, Branches.eval]
      congr 1 <;> funext w <;>
        exact Term.cse_eval (x.wkN _) (s.wkUN _) _ κ _ jκ
          (by rw [UVar.wkN_get, SimpleComp.wkUN_eval, hx])
  | _, _, _, _, _, _, _, _, x, s, .cons us b bs, κ, ρ, jκ, hx, v => by
      simp only [Branches.cse, Branches.eval]
      congr 1
      · funext w
        exact Term.cse_eval (x.wkN _) (s.wkUN _) _ κ _ jκ
          (by rw [UVar.wkN_get, SimpleComp.wkUN_eval, hx])
      · funext r
        exact Branches.cse_eval x s bs κ ρ jκ hx r
  termination_by structural _ _ _ _ _ _ _ _ _ _ br => br
end

end Cse

/-- `let x := c; b`, sharing the repetitions of `c` in `b` (when `c` is a simple computation),
    then with the rewrites of `Term.mkLetE`. -/
def Term.cseLetE {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks} {ℓ : Nat}
    {o' : Lvl} (u : Usage1ω) (c : Comp Δ d Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') :
    Term Δ d Φ Γ τ js (some (Lvl.meetL ℓ o')) :=
  match SimpleComp.ofComp? c with
  | some s =>
    let r := Term.cse (.head (Usage1ω.toUsage01ω_ne_zero u)) (s.wkU _) b
    if h : Lvl.meetL ℓ r.1 = Lvl.meetL ℓ o' then (Term.letE u c r.2).castLvl (by rw [h])
    else .letE u c b
  | none => .letE u c b

theorem Term.cseLetE_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks}
    {ℓ : Nat} {o' : Lvl} (u : Usage1ω) (c : Comp Δ d Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (jκ : JEnv Δ τ js) :
    (Term.cseLetE u c b).eval κ ρ jκ = (Term.letE u c b).eval κ ρ jκ := by
  unfold Term.cseLetE
  cases hs : SimpleComp.ofComp? c with
  | none => rfl
  | some s =>
    simp only
    split
    · rw [Term.eval_castLvl]
      simp only [Term.eval]
      exact Term.cse_eval _ _ b κ _ jκ
        (by simp [SimpleComp.ofComp?_eval c hs κ ρ])
    · rfl

/-! ## Identical branches -/

/-- Is the pure expression a conditional (`Neu.cond`)? -/
def PExpr.isCond {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl} : PExpr Δ Φ Γ τ o → Bool
  | .neu (.cond ..) => true
  | _ => false

/-- `ret (c ? a : b)` for `if c then ret a else ret b`, unless `a` or `b` is a conditional
    already (so that no chain of conditionals is built). -/
def Term.condRet {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat}
    {o₁ o₂ : Lvl} (c : Neu Δ Φ Γ .bool ℓ) (a : PExpr Δ Φ Γ τ o₁) (b : PExpr Δ Φ Γ τ o₂) :
    Term Δ d Φ Γ τ js (some (Lvl.meetL ℓ (Lvl.meet o₁ o₂))) :=
  if a.isCond || b.isCond then .branch (.ite c (.ret a) (.ret b)) else .ret (.neu (.cond c a b))

theorem Term.condRet_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {ℓ : Nat} {o₁ o₂ : Lvl} (c : Neu Δ Φ Γ .bool ℓ) (a : PExpr Δ Φ Γ τ o₁)
    (b : PExpr Δ Φ Γ τ o₂) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    (Term.condRet (d := d) c a b).eval κ ρ jκ =
      (Term.branch (d := d) (.ite c (.ret a) (.ret b))).eval κ ρ jκ := by
  unfold Term.condRet
  split
  · rfl
  · simp only [Term.eval, Branch.eval, PExpr.eval, Neu.eval]

/-- `if c then t else e`, which is `t` when both are `ret a` for the same atom `a` (and the
    level comes out the same), and otherwise, when both are `ret`s, `ret (c ? a : b)`: the
    pure conditional (`Neu.cond`), which has exactly the level of the branch
    (`Term.condRet`). -/
def Term.mkIte {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat}
    {o₁ o₂ : Lvl} (c : Neu Δ Φ Γ .bool ℓ) (t : Term Δ d Φ Γ τ js o₁)
    (e : Term Δ d Φ Γ τ js o₂) : Term Δ d Φ Γ τ js (some (Lvl.meetL ℓ (Lvl.meet o₁ o₂))) :=
  match t, e with
  | .ret a, .ret b =>
    match Atom.ofPExpr? a, Atom.ofPExpr? b with
    | some a', some b' =>
      if h : a'.key = b'.key ∧ o₁ = some (Lvl.meetL ℓ (Lvl.meet o₁ o₂)) then
        (Term.ret a).castLvl h.2
      else Term.condRet c a b
    | _, _ => Term.condRet c a b
  | t, e => .branch (.ite c t e)

theorem Term.mkIte_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {ℓ : Nat} {o₁ o₂ : Lvl} (c : Neu Δ Φ Γ .bool ℓ) (t : Term Δ d Φ Γ τ js o₁)
    (e : Term Δ d Φ Γ τ js o₂) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    (Term.mkIte c t e).eval κ ρ jκ = (Term.branch (.ite c t e)).eval κ ρ jκ := by
  unfold Term.mkIte
  split
  · rename_i a b
    split
    · rename_i a' b' ha hb
      split
      · rename_i h
        rw [Term.eval_castLvl]
        have hab : b.eval κ ρ = a.eval κ ρ := by
          rw [← Atom.ofPExpr?_eval a ha, ← Atom.ofPExpr?_eval b hb]
          exact (eq_of_heq ((Atom.eq_of_key_eq (Δ := Δ) a' b' h.1).2 κ ρ)).symm
        simp only [Term.eval, Branch.eval]
        cases (c.eval κ ρ : Bool) <;> simp [hab]
      · exact Term.condRet_eval c a b κ ρ jκ
    · exact Term.condRet_eval c a b κ ρ jκ
  · rfl

/-- A branch in tail position, with the rewrite of `Term.mkIte`. -/
def Term.mkBranch {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat} :
    Branch Δ d Φ Γ τ js ℓ → Term Δ d Φ Γ τ js (some ℓ)
  | .ite c t e => Term.mkIte c t e
  | .enum_casesOn e bs => .branch (.enum_casesOn e bs)
  | .union_casesOn e bs => .branch (.union_casesOn e bs)
  | .join σ u uₓ body main => .branch (.join σ u uₓ body main)

theorem Term.mkBranch_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {ℓ : Nat} (br : Branch Δ d Φ Γ τ js ℓ) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    (Term.mkBranch br).eval κ ρ jκ = (Term.branch br).eval κ ρ jκ := by
  cases br with
  | ite c t e => exact Term.mkIte_eval c t e κ ρ jκ
  | _ => rfl

/-! ## Trivial join points -/

/-- What the jumps to a trivial join point (parameter of type `σ`, statements of type `τ`)
    are replaced by: the argument itself (a join point `ret x`), or an atom (`ret a`). -/
inductive Repl (Φ : KCtx ks) (Γ : UCtx ks) (σ τ : Ty ks) : Type where
  | ident (h : σ = τ)
  | const (a : Atom Φ Γ τ)

namespace Repl
variable {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks}

/-- The value of a jump with the argument `v`. -/
def eval : Repl Φ Γ σ τ → KEnv Δ Φ → UEnv Δ Γ → Ty.Den Δ σ → Ty.Den Δ τ
  | .ident h, _, _, v => h ▸ v
  | .const a, κ, ρ, _ => a.eval κ ρ

/-- Under one more unknown. -/
def wkU (b : UBinder ks) : Repl Φ Γ σ τ → Repl Φ (b :: Γ) σ τ
  | .ident h => .ident h
  | .const a => .const (a.wkU b)

/-- Under more unknowns. -/
def wkUN (bs : UCtx ks) : Repl Φ Γ σ τ → Repl Φ (bs ++ Γ) σ τ
  | .ident h => .ident h
  | .const a => .const (a.wkUN bs)

/-- Under one more known value. -/
def wkK (b : KBinder ks) : Repl Φ Γ σ τ → Repl (b :: Φ) Γ σ τ
  | .ident h => .ident h
  | .const a => .const (a.wkK b)

@[simp] theorem wkU_eval (b : UBinder ks) (r : Repl Φ Γ σ τ) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (w : Ty.Den Δ b.ty) (v : Ty.Den Δ σ) : (r.wkU b).eval κ (Tuple.cons w ρ) v = r.eval κ ρ v := by
  cases r <;> simp [wkU, eval]

theorem wkUN_eval (bs : UCtx ks) (r : Repl Φ Γ σ τ) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (vs : UEnv Δ bs) (v : Ty.Den Δ σ) : (r.wkUN bs).eval κ (Tuple.append vs ρ) v = r.eval κ ρ v := by
  cases r <;> simp [wkUN, eval, Atom.wkUN_eval]

@[simp] theorem wkK_eval (b : KBinder ks) (r : Repl Φ Γ σ τ) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (w : Ty.Den Δ b.ty) (v : Ty.Den Δ σ) : (r.wkK b).eval (Tuple.cons w κ) ρ v = r.eval κ ρ v := by
  cases r <;> simp [wkK, eval]

/-- The statement a jump with the argument `e` is replaced by. -/
def term {d : Nat} {js : JCtx ks} {o : Lvl} : Repl Φ Γ σ τ → PExpr Δ Φ Γ σ o →
    (o' : Lvl) × Term Δ d Φ Γ τ js o'
  | .ident h, e => ⟨o, .ret (h ▸ e)⟩
  | .const a, _ => ⟨a.lvl, .ret a.toPExpr⟩

theorem term_eval {d : Nat} {js : JCtx ks} {o : Lvl} (r : Repl Φ Γ σ τ) (e : PExpr Δ Φ Γ σ o)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    (r.term (d := d) e).2.eval κ ρ jκ = r.eval κ ρ (e.eval κ ρ) := by
  cases r with
  | ident h => cases h; rfl
  | const a => simp [term, eval, Term.eval]

end Repl

/-- An atom at the position of the innermost unknown is its value. -/
theorem Atom.eval_of_key_zero {Φ : KCtx ks} {Γ : UCtx ks} {b : UBinder ks} {τ : Ty ks}
    (a : Atom Φ (b :: Γ) τ) (h : a.key = .u 0) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (v : Ty.Den Δ b.ty) : HEq (a.eval κ (Tuple.cons v ρ)) v := by
  cases a with
  | u x =>
      cases x with
      | head => simp [Atom.eval]
      | tail x => simp [Atom.key, UVar.index] at h
  | k x => simp [Atom.key] at h
  | bool b => simp [Atom.key] at h

/-- The replacement of the jumps to a join point whose body is trivial: `ret a` for an atom
    `a` that is not the parameter, or `ret x` for the parameter `x`. -/
def Repl.ofBody? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks}
    {u : Usage01ω} {o : Lvl} : Term Δ d Φ (⟨σ, u, d⟩ :: Γ) τ js o → Option (Repl Φ Γ σ τ)
  | .ret e =>
    match Atom.ofPExpr? e with
    | some a =>
      match a.strengthen? with
      | some a' => some (.const a')
      | none => if h : σ = τ ∧ a.key = .u 0 then some (.ident h.1) else none
    | none => none
  | _ => none

theorem Repl.ofBody?_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks}
    {u : Usage01ω} {o : Lvl} (body : Term Δ d Φ (⟨σ, u, d⟩ :: Γ) τ js o) {r : Repl Φ Γ σ τ}
    (h : Repl.ofBody? body = some r) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js)
    (v : Ty.Den Δ σ) : body.eval κ (Tuple.cons v ρ) jκ = r.eval κ ρ v := by
  cases body with
  | ret e =>
      simp only [Repl.ofBody?] at h
      split at h
      · rename_i a ha
        split at h
        · rename_i a' ha'
          cases h
          simp only [Term.eval, Repl.eval]
          rw [← Atom.ofPExpr?_eval e ha]
          exact Atom.strengthen?_eval a ha' κ ρ v
        · split at h
          · rename_i hk
            cases h
            obtain ⟨h1, h2⟩ := hk
            subst h1
            simp only [Term.eval, Repl.eval]
            rw [← Atom.ofPExpr?_eval e ha]
            exact eq_of_heq (Atom.eval_of_key_zero a h2 κ ρ v)
          · cases h
      · cases h
  | _ => simp [Repl.ofBody?] at h

section Inline
variable {σ τ : Ty ks}

mutual
/-- Replace the jumps to the join point `jt` by the statements `r` gives. -/
def Term.inl : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {js : JCtx ks} → {o : Lvl} →
    JVar js σ → Repl Φ Γ σ τ → Term Δ d Φ Γ τ js o → (o' : Lvl) × Term Δ d Φ Γ τ js o'
  | _, _, _, _, _, _, _, .ret e => ⟨_, .ret e⟩
  | _, _, _, _, _, jt, r, .letV u v b => ⟨_, .letV u v (Term.inl jt (r.wkK _) b).2⟩
  | _, _, _, _, _, jt, r, .letE u c b => ⟨_, .letE u c (Term.inl jt (r.wkU _) b).2⟩
  | _, _, _, _, _, jt, r, .record_casesOn us n b =>
      ⟨_, .record_casesOn us n (Term.inl jt (r.wkUN _) b).2⟩
  | _, _, _, _, _, jt, r, .branch br => ⟨_, .branch (Branch.inl jt r br).2⟩
  | _, _, _, _, _, jt, r, .jump (σ := σ') j e =>
      if h : σ' = σ ∧ j.index = jt.index then r.term (h.1 ▸ e) else ⟨_, .jump j e⟩
/-- `Term.inl` in a branch. -/
def Branch.inl : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {js : JCtx ks} → {ℓ : Nat} →
    JVar js σ → Repl Φ Γ σ τ → Branch Δ d Φ Γ τ js ℓ → (ℓ' : Nat) × Branch Δ d Φ Γ τ js ℓ'
  | _, _, _, _, _, jt, r, .ite c t e => ⟨_, .ite c (Term.inl jt r t).2 (Term.inl jt r e).2⟩
  | _, _, _, _, _, jt, r, .enum_casesOn e bs =>
      ⟨_, .enum_casesOn e (fun i => (Term.inl jt r (bs i)).2)⟩
  | _, _, _, _, _, jt, r, .union_casesOn e bs => ⟨_, .union_casesOn e (Branches.inl jt r bs).2⟩
  | _, _, _, _, _, jt, r, .join σ' u uₓ body main =>
      ⟨_, .join σ' u uₓ (Term.inl jt (r.wkU _) body).2 (Branch.inl jt.tail r main).2⟩
/-- `Term.inl` in the branches of a union's case analysis. -/
def Branches.inl : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {js : JCtx ks} → {o : Lvl} →
    JVar js σ → Repl Φ Γ σ τ → Branches Δ d Φ Γ cs τ js o →
    (o' : Lvl) × Branches Δ d Φ Γ cs τ js o'
  | _, _, _, _, _, _, _, jt, r, .two us₁ us₂ b₁ b₂ =>
      ⟨_, .two us₁ us₂ (Term.inl jt (r.wkUN _) b₁).2 (Term.inl jt (r.wkUN _) b₂).2⟩
  | _, _, _, _, _, _, _, jt, r, .cons us b bs =>
      ⟨_, .cons us (Term.inl jt (r.wkUN _) b).2 (Branches.inl jt r bs).2⟩
end

mutual
theorem Term.inl_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {js : JCtx ks} →
    {o : Lvl} → (jt : JVar js σ) → (r : Repl Φ Γ σ τ) → (t : Term Δ d Φ Γ τ js o) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
    (∀ v, jκ.get jt v = r.eval κ ρ v) → (Term.inl jt r t).2.eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, _, .ret _, _, _, _, _ => rfl
  | _, _, _, _, _, jt, r, .letV u v b, κ, ρ, jκ, hj => by
      simp only [Term.inl, Term.eval]
      exact Term.inl_eval jt (r.wkK _) b _ ρ jκ (by simp [hj])
  | _, _, _, _, _, jt, r, .letE u c b, κ, ρ, jκ, hj => by
      simp only [Term.inl, Term.eval]
      exact Term.inl_eval jt (r.wkU _) b κ _ jκ (by simp [hj])
  | _, _, _, _, _, jt, r, .record_casesOn us n b, κ, ρ, jκ, hj => by
      simp only [Term.inl, Term.eval]
      exact Term.inl_eval jt (r.wkUN _) b κ _ jκ (by simp [Repl.wkUN_eval, hj])
  | _, _, _, _, _, jt, r, .branch br, κ, ρ, jκ, hj => by
      simp only [Term.inl, Term.eval]
      exact Branch.inl_eval jt r br κ ρ jκ hj
  | _, _, _, _, _, jt, r, .jump (σ := σ') j e, κ, ρ, jκ, hj => by
      simp only [Term.inl]
      by_cases h : σ' = σ ∧ j.index = jt.index
      · rw [dite_eq_left h]
        obtain ⟨h1, h2⟩ := h
        subst h1
        have hjt := JVar.eq_of_index_eq j jt h2
        subst hjt
        rw [Repl.term_eval]
        exact (hj _).symm
      · rw [dite_eq_right h]
  termination_by structural _ _ _ _ _ _ _ t => t
theorem Branch.inl_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {js : JCtx ks} →
    {ℓ : Nat} → (jt : JVar js σ) → (r : Repl Φ Γ σ τ) → (br : Branch Δ d Φ Γ τ js ℓ) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
    (∀ v, jκ.get jt v = r.eval κ ρ v) → (Branch.inl jt r br).2.eval κ ρ jκ = br.eval κ ρ jκ
  | _, _, _, _, _, jt, r, .ite c t e, κ, ρ, jκ, hj => by
      simp only [Branch.inl, Branch.eval, Term.inl_eval jt r t κ ρ jκ hj,
        Term.inl_eval jt r e κ ρ jκ hj]
  | _, _, _, _, _, jt, r, .enum_casesOn e bs, κ, ρ, jκ, hj => by
      simp only [Branch.inl, Branch.eval]
      exact Term.inl_eval jt r _ κ ρ jκ hj
  | _, _, _, _, _, jt, r, .union_casesOn e bs, κ, ρ, jκ, hj => by
      simp only [Branch.inl, Branch.eval]
      exact Branches.inl_eval jt r bs κ ρ jκ hj _
  | _, _, _, _, _, jt, r, .join σ' u uₓ body main, κ, ρ, jκ, hj => by
      simp only [Branch.inl, Branch.eval]
      have hb : (fun v => (Term.inl jt (r.wkU _) body).2.eval κ (Tuple.cons v ρ) jκ) =
          (fun v => body.eval κ (Tuple.cons v ρ) jκ) := by
        funext v
        exact Term.inl_eval jt (r.wkU _) body κ _ jκ (by simp [hj])
      rw [hb]
      exact Branch.inl_eval jt.tail r main κ ρ _ (by simp [hj])
  termination_by structural _ _ _ _ _ _ _ br => br
theorem Branches.inl_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {js : JCtx ks} → {o : Lvl} →
    (jt : JVar js σ) → (r : Repl Φ Γ σ τ) → (br : Branches Δ d Φ Γ cs τ js o) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
    (∀ v, jκ.get jt v = r.eval κ ρ v) →
    ∀ v, (Branches.inl jt r br).2.eval κ ρ jκ v = br.eval κ ρ jκ v
  | _, _, _, _, _, _, _, jt, r, .two us₁ us₂ b₁ b₂, κ, ρ, jκ, hj, v => by
      simp only [Branches.inl, Branches.eval]
      congr 1 <;> funext w <;>
        exact Term.inl_eval jt (r.wkUN _) _ κ _ jκ (by simp [Repl.wkUN_eval, hj])
  | _, _, _, _, _, _, _, jt, r, .cons us b bs, κ, ρ, jκ, hj, v => by
      simp only [Branches.inl, Branches.eval]
      congr 1
      · funext w
        exact Term.inl_eval jt (r.wkUN _) _ κ _ jκ (by simp [Repl.wkUN_eval, hj])
      · funext w
        exact Branches.inl_eval jt r bs κ ρ jκ hj w
  termination_by structural _ _ _ _ _ _ _ _ _ br => br
end

end Inline

/-- `join j x := body; main`, where a trivial join point (`Repl.ofBody?`) is inlined into
    `main` and then dropped (`Branch.dce`), when the level comes out the same. -/
def Branch.mkJoin {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    {ℓ : Nat} (σ : Ty ks) (u : Usage1ω) (uₓ : Usage01ω) (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o)
    (main : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ) : Branch Δ d Φ Γ τ js (Lvl.meetL ℓ o) :=
  match Repl.ofBody? body with
  | some r =>
    let m := Branch.inl .head r main
    if h : Lvl.meetL m.1 o = Lvl.meetL ℓ o then ((Branch.join σ u uₓ body m.2).castLvl h).dce
    else .join σ u uₓ body main
  | none => .join σ u uₓ body main

theorem Branch.mkJoin_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {o : Lvl} {ℓ : Nat} (σ : Ty ks) (u : Usage1ω) (uₓ : Usage01ω)
    (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o) (main : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    (Branch.mkJoin σ u uₓ body main).eval κ ρ jκ = (Branch.join σ u uₓ body main).eval κ ρ jκ := by
  unfold Branch.mkJoin
  cases hr : Repl.ofBody? body with
  | none => rfl
  | some r =>
    simp only
    split
    · rw [Branch.dce_eval, Branch.eval_castLvl]
      simp only [Branch.eval]
      exact Branch.inl_eval .head r main κ ρ _
        (fun v => by simp [Repl.ofBody?_eval body hr κ ρ jκ v])
    · rfl

end LeanScript

end
