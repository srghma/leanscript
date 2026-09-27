module

public import LeanScript.Eval

@[expose] public section

set_option autoImplicit false

/-!
# Renaming and substitution of the variables of a term

On each of the three layers (`PExpr`, `Comp`, `Term`):

* `rename r e` renames the variables of `e` along `r : DeBruijn.Ren Γ Γ'`;
  `weaken e` moves `e` under one more binder, `shift n e` under `n` more binders.
* `subst σ e` replaces each variable `x : Var Γ τ` of `e` by the **pure expression** `σ x` in
  `Γ'`; `subst1 b a` fills the innermost variable of `b` with `a`.  Only pure expressions are
  substituted: they are closed under their own operations, so a substitution instance of an
  A-normal term is again A-normal.

Both commute with evaluation (`Term.eval_rename`, `Term.eval_subst`, and the same for the two
other layers), so a `let` of a shared pure value and a β-redex mean what their substitution
instance means (`Term.eval_letE_share_eq_subst1`, `Comp.eval_app_lam_eq_subst1`).  Renaming
and substitution act on variables only: the join points of a statement are untouched.
Everything is structural recursion on the term.
-/

namespace LeanScript

open DeBruijn (Ren)

section Rename
variable {ks : List Nat} {Δ : DSig ks}

mutual
/-- Rename the variables of a pure expression. -/
def PExpr.rename {Γ Γ' : Ctx ks} (r : Ren Γ Γ') : {τ : Ty ks} → PExpr Δ Γ τ → PExpr Δ Γ' τ
  | _, .var x => .var (r x)
  | _, .lit p v => .lit p v
  | _, .enum_mk s i => .enum_mk s i
  | _, .record_mk as => .record_mk (as.rename r)
  | _, .union_mk ix as => .union_mk ix (as.rename r)
  | _, .array_mk es => .array_mk (es.rename r)
  | _, .data_in b j e => .data_in b j (e.rename r)
  | _, .data_out b j e => .data_out b j (e.rename r)
  | _, .cond c a b => .cond (c.rename r) (a.rename r) (b.rename r)
  | _, .extern name f as => .extern name f (as.rename r)
  termination_by structural _ e => e
/-- `PExpr.rename` on arguments. -/
def Args.rename {Γ Γ' : Ctx ks} (r : Ren Γ Γ') : {σs : List (Ty ks)} → Args Δ Γ σs →
    Args Δ Γ' σs
  | _, .nil => .nil
  | _, .cons a as => .cons (a.rename r) (as.rename r)
  termination_by structural _ a => a
/-- `PExpr.rename` on the elements of an array literal. -/
def Elems.rename {Γ Γ' : Ctx ks} (r : Ren Γ Γ') : {t : Ty ks} → Elems Δ Γ t → Elems Δ Γ' t
  | _, .nil => .nil
  | _, .cons e es => .cons (e.rename r) (es.rename r)
  termination_by structural _ e => e
end

mutual
/-- Rename the variables of a computation. -/
def Comp.rename : {Γ Γ' : Ctx ks} → {τ : Ty ks} → Ren Γ Γ' → Comp Δ Γ τ → Comp Δ Γ' τ
  | _, _, _, r, .app f a => .app (f.rename r) (a.rename r)
  | _, _, _, r, .lam b => .lam (b.rename (Ren.lift r))
  | _, _, _, r, .share e => .share (e.rename r)
  | _, _, _, r, .extern n f as => .extern n f (as.rename r)
  | _, _, _, r, .nat_rec n z s =>
      .nat_rec (n.rename r) (z.rename r) (s.rename (Ren.lift (Ren.lift r)))
  | _, _, _, r, .array_foldl a z s =>
      .array_foldl (a.rename r) (z.rename r) (s.rename (Ren.lift (Ren.lift r)))
  | _, _, _, r, .data_rec b ρ brs j e =>
      .data_rec b ρ (fun i => (brs i).rename (Ren.lift r)) j (e.rename r)
  | _, _, _, r, .data_brec b ρ k brs j e =>
      .data_brec b ρ k (fun i => (brs i).rename (Ren.lift r)) j (e.rename r)
  | _, _, _, r, .thunk_mk e => .thunk_mk (e.rename r)
  | _, _, _, r, .thunk_force e => .thunk_force (e.rename r)
  | _, _, _, r, .lazy_mk e => .lazy_mk (e.rename r)
  | _, _, _, r, .lazy_force e => .lazy_force (e.rename r)
  termination_by structural _ _ _ _ c => c
/-- Rename the variables of a statement. -/
def Term.rename : {Γ Γ' : Ctx ks} → {τ : Ty ks} → {js : JCtx ks} → Ren Γ Γ' →
    Term Δ Γ τ js → Term Δ Γ' τ js
  | _, _, _, _, r, .ret e => .ret (e.rename r)
  | _, _, _, _, r, .letE c b => .letE (c.rename r) (b.rename (Ren.lift r))
  | _, _, _, _, r, .record_casesOn e body =>
      .record_casesOn (e.rename r) (body.rename (Ren.liftN r _))
  | _, _, _, _, r, .ite c t e => .ite (c.rename r) (t.rename r) (e.rename r)
  | _, _, _, _, r, .enum_casesOn e bs => .enum_casesOn (e.rename r) (fun i => (bs i).rename r)
  | _, _, _, _, r, .union_casesOn e bs => .union_casesOn (e.rename r) (bs.rename r)
  | _, _, _, _, r, .join σ body main => .join σ (body.rename (Ren.lift r)) (main.rename r)
  | _, _, _, _, r, .jump j e => .jump j (e.rename r)
  termination_by structural _ _ _ _ _ t => t
/-- `Term.rename` on the branches of a case analysis. -/
def Branches.rename : {Γ Γ' : Ctx ks} → {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} →
    {js : JCtx ks} → Ren Γ Γ' → Branches Δ Γ cs τ js → Branches Δ Γ' cs τ js
  | _, _, _, _, _, _, r, .two bc bd =>
      .two (bc.rename (Ren.liftN r _)) (bd.rename (Ren.liftN r _))
  | _, _, _, _, _, _, r, .cons b bs => .cons (b.rename (Ren.liftN r _)) (bs.rename r)
  termination_by structural _ _ _ _ _ _ _ b => b
end

/-- A pure expression under one more (innermost) binder. -/
abbrev PExpr.weaken {Γ : Ctx ks} {σ τ : Ty ks} (e : PExpr Δ Γ τ) : PExpr Δ (σ :: Γ) τ :=
  e.rename Ren.weaken

/-- A computation under one more (innermost) binder. -/
abbrev Comp.weaken {Γ : Ctx ks} {σ τ : Ty ks} (c : Comp Δ Γ τ) : Comp Δ (σ :: Γ) τ :=
  c.rename Ren.weaken

/-- A statement under one more (innermost) binder. -/
abbrev Term.weaken {Γ : Ctx ks} {σ τ : Ty ks} {js : JCtx ks} (t : Term Δ Γ τ js) :
    Term Δ (σ :: Γ) τ js :=
  t.rename Ren.weaken

/-- A pure expression under `n` more binders: the first `n` entries of `Γ'` are new. -/
abbrev PExpr.shift {Γ Γ' : Ctx ks} {τ : Ty ks} (n : Nat) (e : PExpr Δ Γ τ)
    (h : Γ'.drop n = Γ := by rfl) : PExpr Δ Γ' τ :=
  e.rename (Ren.dropN n h)

/-- A computation under `n` more binders: the first `n` entries of `Γ'` are new. -/
abbrev Comp.shift {Γ Γ' : Ctx ks} {τ : Ty ks} (n : Nat) (c : Comp Δ Γ τ)
    (h : Γ'.drop n = Γ := by rfl) : Comp Δ Γ' τ :=
  c.rename (Ren.dropN n h)

/-- A statement under `n` more binders: the first `n` entries of `Γ'` are new. -/
abbrev Term.shift {Γ Γ' : Ctx ks} {τ : Ty ks} {js : JCtx ks} (n : Nat) (t : Term Δ Γ τ js)
    (h : Γ'.drop n = Γ := by rfl) : Term Δ Γ' τ js :=
  t.rename (Ren.dropN n h)

end Rename

/-! ## Substitution -/

/-- A substitution: a pure expression in `Γ'` for every variable of `Γ`. -/
abbrev Subst {ks : List Nat} (Δ : DSig ks) (Γ Γ' : Ctx ks) : Type :=
  ∀ {τ : Ty ks}, Var Γ τ → PExpr Δ Γ' τ

namespace Subst
variable {ks : List Nat} {Δ : DSig ks}

/-- A substitution under one more binder. -/
def lift {Γ Γ' : Ctx ks} {σ : Ty ks} (s : Subst Δ Γ Γ') : Subst Δ (σ :: Γ) (σ :: Γ')
  | _, .head => .var .head
  | _, .tail x => (s x).weaken

/-- A substitution under the binders `zs`. -/
def liftN {Γ Γ' : Ctx ks} (s : Subst Δ Γ Γ') : (zs : Ctx ks) → Subst Δ (zs ++ Γ) (zs ++ Γ')
  | [] => s
  | _ :: zs => lift (liftN s zs)

/-- The identity substitution. -/
abbrev id {Γ : Ctx ks} : Subst Δ Γ Γ := fun x => .var x

/-- Fill the innermost variable with `a`, keep the others. -/
def single {Γ : Ctx ks} {σ : Ty ks} (a : PExpr Δ Γ σ) : Subst Δ (σ :: Γ) Γ
  | _, .head => a
  | _, .tail x => .var x

end Subst

section SubstDef
variable {ks : List Nat} {Δ : DSig ks}

mutual
/-- Replace every variable `x` of a pure expression by `s x`. -/
def PExpr.subst {Γ Γ' : Ctx ks} (s : Subst Δ Γ Γ') : {τ : Ty ks} → PExpr Δ Γ τ → PExpr Δ Γ' τ
  | _, .var x => s x
  | _, .lit p v => .lit p v
  | _, .enum_mk sc i => .enum_mk sc i
  | _, .record_mk as => .record_mk (as.subst s)
  | _, .union_mk ix as => .union_mk ix (as.subst s)
  | _, .array_mk es => .array_mk (es.subst s)
  | _, .data_in b j e => .data_in b j (e.subst s)
  | _, .data_out b j e => .data_out b j (e.subst s)
  | _, .cond c a b => .cond (c.subst s) (a.subst s) (b.subst s)
  | _, .extern name f as => .extern name f (as.subst s)
  termination_by structural _ e => e
/-- `PExpr.subst` on arguments. -/
def Args.subst {Γ Γ' : Ctx ks} (s : Subst Δ Γ Γ') : {σs : List (Ty ks)} → Args Δ Γ σs →
    Args Δ Γ' σs
  | _, .nil => .nil
  | _, .cons a as => .cons (a.subst s) (as.subst s)
  termination_by structural _ a => a
/-- `PExpr.subst` on the elements of an array literal. -/
def Elems.subst {Γ Γ' : Ctx ks} (s : Subst Δ Γ Γ') : {t : Ty ks} → Elems Δ Γ t → Elems Δ Γ' t
  | _, .nil => .nil
  | _, .cons e es => .cons (e.subst s) (es.subst s)
  termination_by structural _ e => e
end

mutual
/-- Replace every variable `x` of a computation by `s x`. -/
def Comp.subst : {Γ Γ' : Ctx ks} → {τ : Ty ks} → Subst Δ Γ Γ' → Comp Δ Γ τ → Comp Δ Γ' τ
  | _, _, _, s, .app f a => .app (f.subst s) (a.subst s)
  | _, _, _, s, .lam b => .lam (b.subst (Subst.lift s))
  | _, _, _, s, .share e => .share (e.subst s)
  | _, _, _, s, .extern n f as => .extern n f (as.subst s)
  | _, _, _, s, .nat_rec n z st =>
      .nat_rec (n.subst s) (z.subst s) (st.subst (Subst.lift (Subst.lift s)))
  | _, _, _, s, .array_foldl a z st =>
      .array_foldl (a.subst s) (z.subst s) (st.subst (Subst.lift (Subst.lift s)))
  | _, _, _, s, .data_rec b ρ brs j e =>
      .data_rec b ρ (fun i => (brs i).subst (Subst.lift s)) j (e.subst s)
  | _, _, _, s, .data_brec b ρ k brs j e =>
      .data_brec b ρ k (fun i => (brs i).subst (Subst.lift s)) j (e.subst s)
  | _, _, _, s, .thunk_mk e => .thunk_mk (e.subst s)
  | _, _, _, s, .thunk_force e => .thunk_force (e.subst s)
  | _, _, _, s, .lazy_mk e => .lazy_mk (e.subst s)
  | _, _, _, s, .lazy_force e => .lazy_force (e.subst s)
  termination_by structural _ _ _ _ c => c
/-- Replace every variable `x` of a statement by `s x`. -/
def Term.subst : {Γ Γ' : Ctx ks} → {τ : Ty ks} → {js : JCtx ks} → Subst Δ Γ Γ' →
    Term Δ Γ τ js → Term Δ Γ' τ js
  | _, _, _, _, s, .ret e => .ret (e.subst s)
  | _, _, _, _, s, .letE c b => .letE (c.subst s) (b.subst (Subst.lift s))
  | _, _, _, _, s, .record_casesOn e body =>
      .record_casesOn (e.subst s) (body.subst (Subst.liftN s _))
  | _, _, _, _, s, .ite c t e => .ite (c.subst s) (t.subst s) (e.subst s)
  | _, _, _, _, s, .enum_casesOn e bs => .enum_casesOn (e.subst s) (fun i => (bs i).subst s)
  | _, _, _, _, s, .union_casesOn e bs => .union_casesOn (e.subst s) (bs.subst s)
  | _, _, _, _, s, .join σ body main => .join σ (body.subst (Subst.lift s)) (main.subst s)
  | _, _, _, _, s, .jump j e => .jump j (e.subst s)
  termination_by structural _ _ _ _ _ t => t
/-- `Term.subst` on the branches of a case analysis. -/
def Branches.subst : {Γ Γ' : Ctx ks} → {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} →
    {js : JCtx ks} → Subst Δ Γ Γ' → Branches Δ Γ cs τ js → Branches Δ Γ' cs τ js
  | _, _, _, _, _, _, s, .two bc bd =>
      .two (bc.subst (Subst.liftN s _)) (bd.subst (Subst.liftN s _))
  | _, _, _, _, _, _, s, .cons b bs => .cons (b.subst (Subst.liftN s _)) (bs.subst s)
  termination_by structural _ _ _ _ _ _ _ b => b
end

/-- Fill the innermost variable of a pure expression `b` with `a`. -/
abbrev PExpr.subst1 {Γ : Ctx ks} {σ τ : Ty ks} (b : PExpr Δ (σ :: Γ) τ) (a : PExpr Δ Γ σ) :
    PExpr Δ Γ τ :=
  b.subst (Subst.single a)

/-- Fill the innermost variable of a computation `b` with `a`. -/
abbrev Comp.subst1 {Γ : Ctx ks} {σ τ : Ty ks} (b : Comp Δ (σ :: Γ) τ) (a : PExpr Δ Γ σ) :
    Comp Δ Γ τ :=
  b.subst (Subst.single a)

/-- Fill the innermost variable of a statement `b` with `a`. -/
abbrev Term.subst1 {Γ : Ctx ks} {σ τ : Ty ks} {js : JCtx ks} (b : Term Δ (σ :: Γ) τ js)
    (a : PExpr Δ Γ σ) : Term Δ Γ τ js :=
  b.subst (Subst.single a)

end SubstDef

/-! ## Evaluation commutes with renaming -/

section EvalRename
variable {ks : List Nat} {Δ : DSig ks}

/-- `ρ'` gives each renamed variable `r x` the value `ρ` gives `x`. -/
def EnvRen {Γ Γ' : Ctx ks} (r : Ren Γ Γ') (ρ' : Env Δ Γ') (ρ : Env Δ Γ) : Prop :=
  ∀ {τ : Ty ks} (x : Var Γ τ), ρ'.get (r x) = ρ.get x

theorem EnvRen.lift {Γ Γ' : Ctx ks} {σ : Ty ks} {r : Ren Γ Γ'} {ρ' : Env Δ Γ'} {ρ : Env Δ Γ}
    (h : EnvRen r ρ' ρ) (v : Ty.Den Δ σ) : EnvRen (Ren.lift r) (Tuple.cons v ρ' : Env Δ (σ :: Γ'))
      (Tuple.cons v ρ : Env Δ (σ :: Γ)) := by
  intro τ x
  cases x with
  | head => exact (Tuple.head_cons _ _).trans (Tuple.head_cons _ _).symm
  | tail x =>
      show (Tuple.cons v ρ').tail.get (r x) = (Tuple.cons v ρ).tail.get x
      rw [Tuple.tail_cons, Tuple.tail_cons]
      exact h x

theorem EnvRen.liftN {Γ Γ' : Ctx ks} {r : Ren Γ Γ'} {ρ' : Env Δ Γ'} {ρ : Env Δ Γ}
    (h : EnvRen r ρ' ρ) : (zs : Ctx ks) → (vs : DenList (DSig.refDen Δ) zs) →
      EnvRen (Ren.liftN r zs) (DenList.append vs ρ') (DenList.append vs ρ)
  | [], _ => h
  | _ :: zs, vs => fun x => by
      cases x with
      | head => exact EnvRen.lift (EnvRen.liftN h zs vs.tail) vs.head .head
      | tail x => exact EnvRen.lift (EnvRen.liftN h zs vs.tail) vs.head (.tail x)

theorem EnvRen.weaken {Γ : Ctx ks} {σ : Ty ks} (v : Ty.Den Δ σ) (ρ : Env Δ Γ) :
    EnvRen (Ren.weaken (y := σ)) (Tuple.cons v ρ : Env Δ (σ :: Γ)) ρ := fun x => by
  show (Tuple.cons v ρ).tail.get x = ρ.get x
  rw [Tuple.tail_cons]

mutual
/-- Evaluating a renamed pure expression in an environment related by the renaming gives the
    same value. -/
theorem PExpr.eval_rename {Γ Γ' : Ctx ks} (r : Ren Γ Γ') (ρ' : Env Δ Γ') (ρ : Env Δ Γ)
    (h : EnvRen r ρ' ρ) : {τ : Ty ks} → (e : PExpr Δ Γ τ) → (e.rename r).eval ρ' = e.eval ρ
  | _, .var x => h x
  | _, .lit _ _ => rfl
  | _, .enum_mk _ _ => rfl
  | _, .record_mk as => by
      simp only [PExpr.rename, PExpr.eval]
      rw [Args.eval_rename r ρ' ρ h as]
  | _, .union_mk _ as => by
      simp only [PExpr.rename, PExpr.eval]
      rw [Args.eval_rename r ρ' ρ h as]
  | _, .array_mk es => by
      simp only [PExpr.rename, PExpr.eval]
      rw [Elems.eval_rename r ρ' ρ h es]
  | _, .data_in _ _ e => by
      simp only [PExpr.rename, PExpr.eval]
      rw [PExpr.eval_rename r ρ' ρ h e]
  | _, .data_out _ _ e => by
      simp only [PExpr.rename, PExpr.eval]
      rw [PExpr.eval_rename r ρ' ρ h e]
  | _, .cond c a b => by
      simp only [PExpr.rename, PExpr.eval]
      rw [PExpr.eval_rename r ρ' ρ h c, PExpr.eval_rename r ρ' ρ h a,
        PExpr.eval_rename r ρ' ρ h b]
  | _, .extern _ _ as => by
      simp only [PExpr.rename, PExpr.eval]
      rw [Args.eval_rename r ρ' ρ h as]
  termination_by structural _ e => e
theorem Args.eval_rename {Γ Γ' : Ctx ks} (r : Ren Γ Γ') (ρ' : Env Δ Γ') (ρ : Env Δ Γ)
    (h : EnvRen r ρ' ρ) : {σs : List (Ty ks)} → (as : Args Δ Γ σs) →
    (as.rename r).eval ρ' = as.eval ρ
  | _, .nil => rfl
  | _, .cons a as => by
      simp only [Args.rename, Args.eval]
      rw [PExpr.eval_rename r ρ' ρ h a, Args.eval_rename r ρ' ρ h as]
  termination_by structural _ a => a
theorem Elems.eval_rename {Γ Γ' : Ctx ks} (r : Ren Γ Γ') (ρ' : Env Δ Γ') (ρ : Env Δ Γ)
    (h : EnvRen r ρ' ρ) : {t : Ty ks} → (es : Elems Δ Γ t) →
    (es.rename r).eval ρ' = es.eval ρ
  | _, .nil => rfl
  | _, .cons e es => by
      simp only [Elems.rename, Elems.eval]
      rw [PExpr.eval_rename r ρ' ρ h e, Elems.eval_rename r ρ' ρ h es]
  termination_by structural _ e => e
end

mutual
/-- Evaluating a renamed computation in an environment related by the renaming gives the same
    value. -/
theorem Comp.eval_rename : {Γ Γ' : Ctx ks} → {τ : Ty ks} → (c : Comp Δ Γ τ) → (r : Ren Γ Γ') →
    (ρ' : Env Δ Γ') → (ρ : Env Δ Γ) → EnvRen r ρ' ρ → (c.rename r).eval ρ' = c.eval ρ
  | _, _, _, .app f a, r, ρ', ρ, h => by
      simp only [Comp.rename, Comp.eval]
      rw [PExpr.eval_rename r ρ' ρ h f, PExpr.eval_rename r ρ' ρ h a]
  | _, _, _, .lam b, r, ρ', ρ, h => by
      simp only [Comp.rename, Comp.eval]
      funext v
      exact Term.eval_rename b _ _ _ (h.lift v) _
  | _, _, _, .share e, r, ρ', ρ, h => by
      simp only [Comp.rename, Comp.eval]
      exact PExpr.eval_rename r ρ' ρ h e
  | _, _, _, .extern _ _ as, r, ρ', ρ, h => by
      simp only [Comp.rename, Comp.eval]
      rw [Args.eval_rename r ρ' ρ h as]
  | _, _, _, .nat_rec n z st, r, ρ', ρ, h => by
      simp only [Comp.rename, Comp.eval]
      rw [PExpr.eval_rename r ρ' ρ h n, PExpr.eval_rename r ρ' ρ h z]
      congr 1
      funext k acc
      exact Term.eval_rename st _ _ _ (EnvRen.lift (EnvRen.lift (σ := .nat) h k) acc) _
  | _, _, _, .array_foldl a z st, r, ρ', ρ, h => by
      simp only [Comp.rename, Comp.eval]
      rw [PExpr.eval_rename r ρ' ρ h a, PExpr.eval_rename r ρ' ρ h z]
      congr 1
      funext acc x
      exact Term.eval_rename st _ _ _ (EnvRen.lift (EnvRen.lift h acc) x) _
  | _, _, _, .data_rec b ρt brs j e, r, ρ', ρ, h => by
      simp only [Comp.rename, Comp.eval]
      rw [PExpr.eval_rename r ρ' ρ h e]
      congr 1
      funext i x
      exact Term.eval_rename (brs i) _ _ _ (h.lift x) _
  | _, _, _, .data_brec b ρt k brs j e, r, ρ', ρ, h => by
      simp only [Comp.rename, Comp.eval]
      rw [PExpr.eval_rename r ρ' ρ h e]
      congr 1
      funext i x
      exact Term.eval_rename (brs i) _ _ _ (h.lift x) _
  | _, _, _, .thunk_mk e, r, ρ', ρ, h => by
      simp only [Comp.rename, Comp.eval]
      congr 1
      exact Term.eval_rename e r ρ' ρ h _
  | _, _, _, .thunk_force e, r, ρ', ρ, h => by
      simp only [Comp.rename, Comp.eval]
      rw [PExpr.eval_rename r ρ' ρ h e]
  | _, _, _, .lazy_mk e, r, ρ', ρ, h => by
      simp only [Comp.rename, Comp.eval]
      congr 1
      exact Term.eval_rename e r ρ' ρ h _
  | _, _, _, .lazy_force e, r, ρ', ρ, h => by
      simp only [Comp.rename, Comp.eval]
      rw [PExpr.eval_rename r ρ' ρ h e]
  termination_by structural _ _ _ c => c
/-- Evaluating a renamed statement in an environment related by the renaming gives the same
    value, with the same join points. -/
theorem Term.eval_rename : {Γ Γ' : Ctx ks} → {τ : Ty ks} → {js : JCtx ks} →
    (t : Term Δ Γ τ js) → (r : Ren Γ Γ') → (ρ' : Env Δ Γ') → (ρ : Env Δ Γ) → EnvRen r ρ' ρ →
    (κ : JEnv Δ τ js) → (t.rename r).eval ρ' κ = t.eval ρ κ
  | _, _, _, _, .ret e, r, ρ', ρ, h, κ => by
      simp only [Term.rename, Term.eval]
      exact PExpr.eval_rename r ρ' ρ h e
  | _, _, _, _, .letE c b, r, ρ', ρ, h, κ => by
      simp only [Term.rename, Term.eval]
      rw [Comp.eval_rename c r ρ' ρ h]
      exact Term.eval_rename b _ _ _ (h.lift _) κ
  | _, _, _, _, .record_casesOn e body, r, ρ', ρ, h, κ => by
      simp only [Term.rename, Term.eval]
      rw [PExpr.eval_rename r ρ' ρ h e]
      exact Term.eval_rename body _ _ _ (h.liftN _ _) κ
  | _, _, _, _, .ite c t e, r, ρ', ρ, h, κ => by
      simp only [Term.rename, Term.eval]
      rw [PExpr.eval_rename r ρ' ρ h c, Term.eval_rename t r ρ' ρ h κ,
        Term.eval_rename e r ρ' ρ h κ]
  | _, _, _, _, .enum_casesOn e bs, r, ρ', ρ, h, κ => by
      simp only [Term.rename, Term.eval]
      rw [PExpr.eval_rename r ρ' ρ h e]
      exact Term.eval_rename (bs _) r ρ' ρ h κ
  | _, _, _, _, .union_casesOn e bs, r, ρ', ρ, h, κ => by
      simp only [Term.rename, Term.eval]
      rw [PExpr.eval_rename r ρ' ρ h e]
      exact Branches.eval_rename bs r ρ' ρ h κ _
  | _, _, _, _, .join _ body main, r, ρ', ρ, h, κ => by
      simp only [Term.rename, Term.eval]
      have hb : (fun v => (body.rename (Ren.lift r)).eval (Tuple.cons v ρ') κ) =
          (fun v => body.eval (Tuple.cons v ρ) κ) := by
        funext v; exact Term.eval_rename body _ _ _ (h.lift v) κ
      rw [hb]
      exact Term.eval_rename main r ρ' ρ h _
  | _, _, _, _, .jump j e, r, ρ', ρ, h, κ => by
      simp only [Term.rename, Term.eval]
      rw [PExpr.eval_rename r ρ' ρ h e]
  termination_by structural _ _ _ _ t => t
theorem Branches.eval_rename : {Γ Γ' : Ctx ks} → {bs : List Bool} → {cs : Ctors ks bs} →
    {τ : Ty ks} → {js : JCtx ks} → (brs : Branches Δ Γ cs τ js) → (r : Ren Γ Γ') →
    (ρ' : Env Δ Γ') → (ρ : Env Δ Γ) → EnvRen r ρ' ρ → (κ : JEnv Δ τ js) →
    (x : Ctors.den (DSig.refDen Δ) cs) → (brs.rename r).eval ρ' κ x = brs.eval ρ κ x
  | _, _, _, _, _, _, .two bc bd, r, ρ', ρ, h, κ, x => by
      simp only [Branches.rename, Branches.eval]
      congr 1
      · funext v; exact Term.eval_rename bc _ _ _ (h.liftN _ v) κ
      · funext v; exact Term.eval_rename bd _ _ _ (h.liftN _ v) κ
  | _, _, _, _, _, _, .cons b bs, r, ρ', ρ, h, κ, x => by
      simp only [Branches.rename, Branches.eval]
      congr 1
      · funext v; exact Term.eval_rename b _ _ _ (h.liftN _ v) κ
      · funext y; exact Branches.eval_rename bs r ρ' ρ h κ y
  termination_by structural _ _ _ _ _ _ b => b
end

/-- A weakened pure expression ignores the value of the new variable. -/
theorem PExpr.eval_weaken {Γ : Ctx ks} {σ τ : Ty ks} (e : PExpr Δ Γ τ) (v : Ty.Den Δ σ)
    (ρ : Env Δ Γ) : (e.weaken (σ := σ)).eval (Tuple.cons v ρ : Env Δ (σ :: Γ)) = e.eval ρ :=
  PExpr.eval_rename _ _ _ (EnvRen.weaken v ρ) e

/-- A weakened computation ignores the value of the new variable. -/
theorem Comp.eval_weaken {Γ : Ctx ks} {σ τ : Ty ks} (c : Comp Δ Γ τ) (v : Ty.Den Δ σ)
    (ρ : Env Δ Γ) : (c.weaken (σ := σ)).eval (Tuple.cons v ρ : Env Δ (σ :: Γ)) = c.eval ρ :=
  Comp.eval_rename c _ _ _ (EnvRen.weaken v ρ)

/-- A weakened statement ignores the value of the new variable. -/
theorem Term.eval_weaken {Γ : Ctx ks} {σ τ : Ty ks} {js : JCtx ks} (t : Term Δ Γ τ js)
    (v : Ty.Den Δ σ) (ρ : Env Δ Γ) (κ : JEnv Δ τ js) :
    (t.weaken (σ := σ)).eval (Tuple.cons v ρ : Env Δ (σ :: Γ)) κ = t.eval ρ κ :=
  Term.eval_rename t _ _ _ (EnvRen.weaken v ρ) κ

end EvalRename

/-! ## Evaluation commutes with substitution -/

section EvalSubst
variable {ks : List Nat} {Δ : DSig ks}

/-- In `ρ'`, each substituted pure expression `s x` has the value `ρ` gives `x`. -/
def EnvSub {Γ Γ' : Ctx ks} (s : Subst Δ Γ Γ') (ρ' : Env Δ Γ') (ρ : Env Δ Γ) : Prop :=
  ∀ {τ : Ty ks} (x : Var Γ τ), (s x).eval ρ' = ρ.get x

theorem EnvSub.lift {Γ Γ' : Ctx ks} {σ : Ty ks} {s : Subst Δ Γ Γ'} {ρ' : Env Δ Γ'}
    {ρ : Env Δ Γ} (h : EnvSub s ρ' ρ) (v : Ty.Den Δ σ) :
    EnvSub (Subst.lift s) (Tuple.cons v ρ' : Env Δ (σ :: Γ')) (Tuple.cons v ρ : Env Δ (σ :: Γ)) := fun x => by
  cases x with
  | head => exact (Tuple.head_cons _ _).trans (Tuple.head_cons _ _).symm
  | tail x =>
      show (s x).weaken.eval (Tuple.cons v ρ') = (Tuple.cons v ρ).tail.get x
      rw [Tuple.tail_cons]
      exact (PExpr.eval_weaken _ _ _).trans (h x)

theorem EnvSub.liftN {Γ Γ' : Ctx ks} {s : Subst Δ Γ Γ'} {ρ' : Env Δ Γ'} {ρ : Env Δ Γ}
    (h : EnvSub s ρ' ρ) : (zs : Ctx ks) → (vs : DenList (DSig.refDen Δ) zs) →
      EnvSub (Subst.liftN s zs) (DenList.append vs ρ') (DenList.append vs ρ)
  | [], _ => h
  | _ :: zs, vs => EnvSub.lift (EnvSub.liftN h zs vs.tail) vs.head

theorem EnvSub.single {Γ : Ctx ks} {σ : Ty ks} (a : PExpr Δ Γ σ) (ρ : Env Δ Γ) :
    EnvSub (Subst.single a) ρ (Tuple.cons (a.eval ρ) ρ : Env Δ (σ :: Γ)) := fun x => by
  cases x with
  | head => exact (Tuple.head_cons _ _).symm
  | tail x =>
      show ρ.get x = (Tuple.cons (a.eval ρ) ρ).tail.get x
      rw [Tuple.tail_cons]

theorem EnvSub.id {Γ : Ctx ks} (ρ : Env Δ Γ) : EnvSub (Subst.id (Δ := Δ)) ρ ρ := fun _ => rfl

mutual
/-- Evaluating a substituted pure expression in an environment related by the substitution
    gives the same value. -/
theorem PExpr.eval_subst {Γ Γ' : Ctx ks} (s : Subst Δ Γ Γ') (ρ' : Env Δ Γ') (ρ : Env Δ Γ)
    (h : EnvSub s ρ' ρ) : {τ : Ty ks} → (e : PExpr Δ Γ τ) → (e.subst s).eval ρ' = e.eval ρ
  | _, .var x => h x
  | _, .lit _ _ => rfl
  | _, .enum_mk _ _ => rfl
  | _, .record_mk as => by
      simp only [PExpr.subst, PExpr.eval]
      rw [Args.eval_subst s ρ' ρ h as]
  | _, .union_mk _ as => by
      simp only [PExpr.subst, PExpr.eval]
      rw [Args.eval_subst s ρ' ρ h as]
  | _, .array_mk es => by
      simp only [PExpr.subst, PExpr.eval]
      rw [Elems.eval_subst s ρ' ρ h es]
  | _, .data_in _ _ e => by
      simp only [PExpr.subst, PExpr.eval]
      rw [PExpr.eval_subst s ρ' ρ h e]
  | _, .data_out _ _ e => by
      simp only [PExpr.subst, PExpr.eval]
      rw [PExpr.eval_subst s ρ' ρ h e]
  | _, .cond c a b => by
      simp only [PExpr.subst, PExpr.eval]
      rw [PExpr.eval_subst s ρ' ρ h c, PExpr.eval_subst s ρ' ρ h a,
        PExpr.eval_subst s ρ' ρ h b]
  | _, .extern _ _ as => by
      simp only [PExpr.subst, PExpr.eval]
      rw [Args.eval_subst s ρ' ρ h as]
  termination_by structural _ e => e
theorem Args.eval_subst {Γ Γ' : Ctx ks} (s : Subst Δ Γ Γ') (ρ' : Env Δ Γ') (ρ : Env Δ Γ)
    (h : EnvSub s ρ' ρ) : {σs : List (Ty ks)} → (as : Args Δ Γ σs) →
    (as.subst s).eval ρ' = as.eval ρ
  | _, .nil => rfl
  | _, .cons a as => by
      simp only [Args.subst, Args.eval]
      rw [PExpr.eval_subst s ρ' ρ h a, Args.eval_subst s ρ' ρ h as]
  termination_by structural _ a => a
theorem Elems.eval_subst {Γ Γ' : Ctx ks} (s : Subst Δ Γ Γ') (ρ' : Env Δ Γ') (ρ : Env Δ Γ)
    (h : EnvSub s ρ' ρ) : {t : Ty ks} → (es : Elems Δ Γ t) →
    (es.subst s).eval ρ' = es.eval ρ
  | _, .nil => rfl
  | _, .cons e es => by
      simp only [Elems.subst, Elems.eval]
      rw [PExpr.eval_subst s ρ' ρ h e, Elems.eval_subst s ρ' ρ h es]
  termination_by structural _ e => e
end

mutual
/-- Evaluating a substituted computation in an environment related by the substitution gives
    the same value. -/
theorem Comp.eval_subst : {Γ Γ' : Ctx ks} → {τ : Ty ks} → (c : Comp Δ Γ τ) →
    (s : Subst Δ Γ Γ') → (ρ' : Env Δ Γ') → (ρ : Env Δ Γ) → EnvSub s ρ' ρ →
    (c.subst s).eval ρ' = c.eval ρ
  | _, _, _, .app f a, s, ρ', ρ, h => by
      simp only [Comp.subst, Comp.eval]
      rw [PExpr.eval_subst s ρ' ρ h f, PExpr.eval_subst s ρ' ρ h a]
  | _, _, _, .lam b, s, ρ', ρ, h => by
      simp only [Comp.subst, Comp.eval]
      funext v
      exact Term.eval_subst b _ _ _ (h.lift v) _
  | _, _, _, .share e, s, ρ', ρ, h => by
      simp only [Comp.subst, Comp.eval]
      exact PExpr.eval_subst s ρ' ρ h e
  | _, _, _, .extern _ _ as, s, ρ', ρ, h => by
      simp only [Comp.subst, Comp.eval]
      rw [Args.eval_subst s ρ' ρ h as]
  | _, _, _, .nat_rec n z st, s, ρ', ρ, h => by
      simp only [Comp.subst, Comp.eval]
      rw [PExpr.eval_subst s ρ' ρ h n, PExpr.eval_subst s ρ' ρ h z]
      congr 1
      funext k acc
      exact Term.eval_subst st _ _ _ (EnvSub.lift (EnvSub.lift (σ := .nat) h k) acc) _
  | _, _, _, .array_foldl a z st, s, ρ', ρ, h => by
      simp only [Comp.subst, Comp.eval]
      rw [PExpr.eval_subst s ρ' ρ h a, PExpr.eval_subst s ρ' ρ h z]
      congr 1
      funext acc x
      exact Term.eval_subst st _ _ _ (EnvSub.lift (EnvSub.lift h acc) x) _
  | _, _, _, .data_rec b ρt brs j e, s, ρ', ρ, h => by
      simp only [Comp.subst, Comp.eval]
      rw [PExpr.eval_subst s ρ' ρ h e]
      congr 1
      funext i x
      exact Term.eval_subst (brs i) _ _ _ (h.lift x) _
  | _, _, _, .data_brec b ρt k brs j e, s, ρ', ρ, h => by
      simp only [Comp.subst, Comp.eval]
      rw [PExpr.eval_subst s ρ' ρ h e]
      congr 1
      funext i x
      exact Term.eval_subst (brs i) _ _ _ (h.lift x) _
  | _, _, _, .thunk_mk e, s, ρ', ρ, h => by
      simp only [Comp.subst, Comp.eval]
      congr 1
      exact Term.eval_subst e s ρ' ρ h _
  | _, _, _, .thunk_force e, s, ρ', ρ, h => by
      simp only [Comp.subst, Comp.eval]
      rw [PExpr.eval_subst s ρ' ρ h e]
  | _, _, _, .lazy_mk e, s, ρ', ρ, h => by
      simp only [Comp.subst, Comp.eval]
      congr 1
      exact Term.eval_subst e s ρ' ρ h _
  | _, _, _, .lazy_force e, s, ρ', ρ, h => by
      simp only [Comp.subst, Comp.eval]
      rw [PExpr.eval_subst s ρ' ρ h e]
  termination_by structural _ _ _ c => c
/-- Evaluating a substituted statement in an environment related by the substitution gives the
    same value, with the same join points. -/
theorem Term.eval_subst : {Γ Γ' : Ctx ks} → {τ : Ty ks} → {js : JCtx ks} →
    (t : Term Δ Γ τ js) → (s : Subst Δ Γ Γ') → (ρ' : Env Δ Γ') → (ρ : Env Δ Γ) →
    EnvSub s ρ' ρ → (κ : JEnv Δ τ js) → (t.subst s).eval ρ' κ = t.eval ρ κ
  | _, _, _, _, .ret e, s, ρ', ρ, h, κ => by
      simp only [Term.subst, Term.eval]
      exact PExpr.eval_subst s ρ' ρ h e
  | _, _, _, _, .letE c b, s, ρ', ρ, h, κ => by
      simp only [Term.subst, Term.eval]
      rw [Comp.eval_subst c s ρ' ρ h]
      exact Term.eval_subst b _ _ _ (h.lift _) κ
  | _, _, _, _, .record_casesOn e body, s, ρ', ρ, h, κ => by
      simp only [Term.subst, Term.eval]
      rw [PExpr.eval_subst s ρ' ρ h e]
      exact Term.eval_subst body _ _ _ (h.liftN _ _) κ
  | _, _, _, _, .ite c t e, s, ρ', ρ, h, κ => by
      simp only [Term.subst, Term.eval]
      rw [PExpr.eval_subst s ρ' ρ h c, Term.eval_subst t s ρ' ρ h κ,
        Term.eval_subst e s ρ' ρ h κ]
  | _, _, _, _, .enum_casesOn e bs, s, ρ', ρ, h, κ => by
      simp only [Term.subst, Term.eval]
      rw [PExpr.eval_subst s ρ' ρ h e]
      exact Term.eval_subst (bs _) s ρ' ρ h κ
  | _, _, _, _, .union_casesOn e bs, s, ρ', ρ, h, κ => by
      simp only [Term.subst, Term.eval]
      rw [PExpr.eval_subst s ρ' ρ h e]
      exact Branches.eval_subst bs s ρ' ρ h κ _
  | _, _, _, _, .join _ body main, s, ρ', ρ, h, κ => by
      simp only [Term.subst, Term.eval]
      have hb : (fun v => (body.subst (Subst.lift s)).eval (Tuple.cons v ρ') κ) =
          (fun v => body.eval (Tuple.cons v ρ) κ) := by
        funext v; exact Term.eval_subst body _ _ _ (h.lift v) κ
      rw [hb]
      exact Term.eval_subst main s ρ' ρ h _
  | _, _, _, _, .jump j e, s, ρ', ρ, h, κ => by
      simp only [Term.subst, Term.eval]
      rw [PExpr.eval_subst s ρ' ρ h e]
  termination_by structural _ _ _ _ t => t
theorem Branches.eval_subst : {Γ Γ' : Ctx ks} → {bs : List Bool} → {cs : Ctors ks bs} →
    {τ : Ty ks} → {js : JCtx ks} → (brs : Branches Δ Γ cs τ js) → (s : Subst Δ Γ Γ') →
    (ρ' : Env Δ Γ') → (ρ : Env Δ Γ) → EnvSub s ρ' ρ → (κ : JEnv Δ τ js) →
    (x : Ctors.den (DSig.refDen Δ) cs) → (brs.subst s).eval ρ' κ x = brs.eval ρ κ x
  | _, _, _, _, _, _, .two bc bd, s, ρ', ρ, h, κ, x => by
      simp only [Branches.subst, Branches.eval]
      congr 1
      · funext v; exact Term.eval_subst bc _ _ _ (h.liftN _ v) κ
      · funext v; exact Term.eval_subst bd _ _ _ (h.liftN _ v) κ
  | _, _, _, _, _, _, .cons b bs, s, ρ', ρ, h, κ, x => by
      simp only [Branches.subst, Branches.eval]
      congr 1
      · funext v; exact Term.eval_subst b _ _ _ (h.liftN _ v) κ
      · funext y; exact Branches.eval_subst bs s ρ' ρ h κ y
  termination_by structural _ _ _ _ _ _ b => b
end

/-- Filling the innermost variable of `b` with `a` means evaluating `b` with the value of `a`
    bound to it. -/
theorem Term.eval_subst1 {Γ : Ctx ks} {σ τ : Ty ks} {js : JCtx ks} (b : Term Δ (σ :: Γ) τ js)
    (a : PExpr Δ Γ σ) (ρ : Env Δ Γ) (κ : JEnv Δ τ js) :
    (b.subst1 a).eval ρ κ = b.eval (Tuple.cons (a.eval ρ) ρ : Env Δ (σ :: Γ)) κ :=
  Term.eval_subst b _ _ _ (EnvSub.single a ρ) κ

/-- A `let` of a shared pure value means its substitution instance. -/
theorem Term.eval_letE_share_eq_subst1 {Γ : Ctx ks} {σ τ : Ty ks} {js : JCtx ks}
    (a : PExpr Δ Γ σ) (b : Term Δ (σ :: Γ) τ js) (ρ : Env Δ Γ) (κ : JEnv Δ τ js) :
    (Term.letE (.share a) b).eval ρ κ = (b.subst1 a).eval ρ κ :=
  (Term.eval_subst1 b a ρ κ).symm

/-- β: a closure applied to an argument means its body with the argument substituted. -/
theorem Comp.eval_app_lam_eq_subst1 {Γ : Ctx ks} {σ τ : Ty ks} (b : Term Δ (σ :: Γ) τ [])
    (a : PExpr Δ Γ σ) (ρ : Env Δ Γ) :
    (Comp.lam b).eval ρ (a.eval ρ) = (b.subst1 a).eval ρ PUnit.unit :=
  (Term.eval_subst1 b a ρ PUnit.unit).symm

/-- The identity substitution does not change the value. -/
theorem Term.eval_subst_id {Γ : Ctx ks} {τ : Ty ks} {js : JCtx ks} (t : Term Δ Γ τ js)
    (ρ : Env Δ Γ) (κ : JEnv Δ τ js) : (t.subst Subst.id).eval ρ κ = t.eval ρ κ :=
  Term.eval_subst t _ _ _ (EnvSub.id ρ) κ

end EvalSubst

/-! ## Binding the value of a statement: `Term.retJump`

A statement `t : Term Δ Γ σ []` in operand position is bound by a join point for the rest of
the computation, to which every answer of `t` jumps: `Term.join σ rest t.retJump`.  This keeps
the term A-normal and B-normal (no statement is ever nested in a computation). -/

section RetJump
variable {ks : List Nat} {Δ : DSig ks}

mutual
/-- Every answer `ret p` of a statement becomes a jump with `p` to the join point just past its
    own join points; its type becomes that of the join point's statement. -/
def Term.retJump {τ : Ty ks} {js : JCtx ks} : {Γ : Ctx ks} → {σ : Ty ks} → {js' : JCtx ks} →
    Term Δ Γ σ js' → Term Δ Γ τ (js' ++ σ :: js)
  | _, _, js', .ret p => .jump (DeBruijn.atLength js') p
  | _, _, _, .letE c b => .letE c b.retJump
  | _, _, _, .record_casesOn p b => .record_casesOn p b.retJump
  | _, _, _, .ite c a b => .ite c a.retJump b.retJump
  | _, _, _, .enum_casesOn p bs => .enum_casesOn p (fun i => (bs i).retJump)
  | _, _, _, .union_casesOn p brs => .union_casesOn p brs.retJump
  | _, _, _, .join s b m => .join s b.retJump m.retJump
  | _, _, _, .jump j p => .jump j.appendRight p
  termination_by structural _ _ _ t => t
/-- `Term.retJump` on the branches of a case analysis. -/
def Branches.retJump {τ : Ty ks} {js : JCtx ks} : {Γ : Ctx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {σ : Ty ks} → {js' : JCtx ks} →
    Branches Δ Γ cs σ js' → Branches Δ Γ cs τ (js' ++ σ :: js)
  | _, _, _, _, _, .two a b => .two a.retJump b.retJump
  | _, _, _, _, _, .cons b bs => .cons b.retJump bs.retJump
  termination_by structural _ _ _ _ _ b => b
end

/-- The join points of `t.retJump`: its own join points, each finished by `k`, then `k`. -/
def JEnv.RetJump {τ σ : Ty ks} {js' js : JCtx ks} (k : Ty.Den Δ σ → Ty.Den Δ τ)
    (κ' : JEnv Δ σ js') (κ : JEnv Δ τ (js' ++ σ :: js)) : Prop :=
  κ.get (DeBruijn.atLength js') = k ∧
    ∀ {s : Ty ks} (j : JVar js' s) (v : Ty.Den Δ s), κ.get j.appendRight v = k (κ'.get j v)

mutual
/-- `t.retJump` gives the answer of `t` to the join point past its own. -/
theorem Term.eval_retJump {τ : Ty ks} {js : JCtx ks} : {Γ : Ctx ks} → {σ : Ty ks} →
    {js' : JCtx ks} → (t : Term Δ Γ σ js') → (ρ : Env Δ Γ) → (k : Ty.Den Δ σ → Ty.Den Δ τ) →
    (κ' : JEnv Δ σ js') → (κ : JEnv Δ τ (js' ++ σ :: js)) → JEnv.RetJump k κ' κ →
    (t.retJump (τ := τ) (js := js)).eval ρ κ = k (t.eval ρ κ')
  | _, _, _, .ret p, ρ, k, κ', κ, h => by
      simp only [Term.retJump, Term.eval]
      rw [h.1]
  | _, _, _, .letE c b, ρ, k, κ', κ, h => by
      simp only [Term.retJump, Term.eval]
      exact Term.eval_retJump b _ k κ' κ h
  | _, _, _, .record_casesOn p b, ρ, k, κ', κ, h => by
      simp only [Term.retJump, Term.eval]
      exact Term.eval_retJump b _ k κ' κ h
  | _, _, _, .ite c a b, ρ, k, κ', κ, h => by
      simp only [Term.retJump, Term.eval]
      cases (c.eval ρ : Bool)
      · exact Term.eval_retJump b ρ k κ' κ h
      · exact Term.eval_retJump a ρ k κ' κ h
  | _, _, _, .enum_casesOn p bs, ρ, k, κ', κ, h => by
      simp only [Term.retJump, Term.eval]
      exact Term.eval_retJump (bs _) ρ k κ' κ h
  | _, _, _, .union_casesOn p brs, ρ, k, κ', κ, h => by
      simp only [Term.retJump, Term.eval]
      exact Branches.eval_retJump brs ρ k κ' κ h _
  | _, _, _, .join s b m, ρ, k, κ', κ, h => by
      simp only [Term.retJump, Term.eval]
      refine Term.eval_retJump m ρ k _ _ ⟨?_, ?_⟩
      · simp only [JEnv.get, DeBruijn.atLength, Tuple.get_cons_tail]
        exact h.1
      intro s' j v
      cases j with
      | head =>
          simp only [JEnv.get, DeBruijn.appendRight, Tuple.get_cons_head]
          exact Term.eval_retJump b _ k κ' κ h
      | tail j =>
          simp only [JEnv.get, DeBruijn.appendRight, Tuple.get_cons_tail]
          exact h.2 j v
  | _, _, _, .jump j p, ρ, k, κ', κ, h => by
      simp only [Term.retJump, Term.eval]
      exact h.2 j _
  termination_by structural _ _ _ t => t
theorem Branches.eval_retJump {τ : Ty ks} {js : JCtx ks} : {Γ : Ctx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {σ : Ty ks} → {js' : JCtx ks} → (brs : Branches Δ Γ cs σ js') →
    (ρ : Env Δ Γ) → (k : Ty.Den Δ σ → Ty.Den Δ τ) → (κ' : JEnv Δ σ js') →
    (κ : JEnv Δ τ (js' ++ σ :: js)) → JEnv.RetJump k κ' κ →
    (x : Ctors.den (DSig.refDen Δ) cs) →
    (brs.retJump (τ := τ) (js := js)).eval ρ κ x = k (brs.eval ρ κ' x)
  | _, _, _, _, _, .two (c := c) (d := d) a b, ρ, k, κ', κ, h, x => by
      simp only [Branches.retJump, Branches.eval]
      rw [show (fun v => a.retJump.eval (DenList.append v ρ) κ) =
          (fun v => k (a.eval (DenList.append v ρ) κ')) from
            funext fun v => Term.eval_retJump a _ k κ' κ h,
        show (fun v => b.retJump.eval (DenList.append v ρ) κ) =
          (fun v => k (b.eval (DenList.append v ρ) κ')) from
            funext fun v => Term.eval_retJump b _ k κ' κ h]
      cases c <;> cases d <;> simp only [Ctor.twoCase] <;> split <;> rfl
  | _, _, _, _, _, .cons (c := c) b bs, ρ, k, κ', κ, h, x => by
      simp only [Branches.retJump, Branches.eval]
      rw [show (fun v => b.retJump.eval (DenList.append v ρ) κ) =
          (fun v => k (b.eval (DenList.append v ρ) κ')) from
            funext fun v => Term.eval_retJump b _ k κ' κ h,
        show (fun r => bs.retJump.eval ρ κ r) = (fun r => k (bs.eval ρ κ' r)) from
            funext fun r => Branches.eval_retJump bs ρ k κ' κ h r]
      cases c <;> simp only [Ctor.consCase] <;> split <;> rfl
  termination_by structural _ _ _ _ _ b => b
end

/-- Binding the value of a statement `t` with no join point by a join point for the rest `k`
    means evaluating `k` with the value of `t` bound. -/
theorem Term.eval_join_retJump {Γ : Ctx ks} {σ τ : Ty ks} {js : JCtx ks} (t : Term Δ Γ σ [])
    (k : Term Δ (σ :: Γ) τ js) (ρ : Env Δ Γ) (κ : JEnv Δ τ js) :
    (Term.join σ k t.retJump).eval ρ κ = k.eval (Tuple.cons (t.eval ρ PUnit.unit) ρ) κ := by
  simp only [Term.eval]
  exact Term.eval_retJump (js' := []) t ρ (fun v => k.eval (Tuple.cons v ρ) κ) PUnit.unit _
    ⟨by simp only [JEnv.get, DeBruijn.atLength, Tuple.get_cons_head], fun j => nomatch j⟩

end RetJump

end LeanScript

end
