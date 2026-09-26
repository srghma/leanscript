module

public import LeanScript.Eval

@[expose] public section

set_option autoImplicit false

/-!
# Renaming and substitution of the variables of a term

* `Term.rename r e` renames the variables of `e` along `r : DeBruijn.Ren Γ Γ'`;
  `Term.weaken e` moves `e` under one more binder.
* `Term.subst σ e` replaces each variable `x : Var Γ τ` of `e` by the term `σ x` in `Γ'`;
  `Term.subst1 b a` fills the innermost variable of `b` with `a`.

Both commute with evaluation (`Term.eval_rename`, `Term.eval_subst`), so a `let` and a
β-redex mean what their substitution instance means (`Term.eval_letE_eq_subst1`,
`Term.eval_app_lam_eq_subst1`).  Everything is structural recursion on the term.
-/

namespace LeanScript

open DeBruijn (Ren)

section Rename
variable {ks : List Nat} {Δ : DSig ks}

mutual
/-- Rename the variables of a term. -/
def Term.rename : {Γ Γ' : Ctx ks} → {τ : Ty ks} → Ren Γ Γ' → Term Δ Γ τ → Term Δ Γ' τ
  | _, _, _, r, .var x => .var (r x)
  | _, _, _, r, .letE e b => .letE (e.rename r) (b.rename (Ren.lift r))
  | _, _, _, r, .lam b => .lam (b.rename (Ren.lift r))
  | _, _, _, r, .app f a => .app (f.rename r) (a.rename r)
  | _, _, _, _, .lit p v h => .lit p v h
  | _, _, _, r, .extern n f as => .extern n f (as.rename r)
  | _, _, _, r, .ite c t e => .ite (c.rename r) (t.rename r) (e.rename r)
  | _, _, _, r, .nat_rec n z s =>
      .nat_rec (n.rename r) (z.rename r) (s.rename (Ren.lift (Ren.lift r)))
  | _, _, _, _, .enum_mk s i => .enum_mk s i
  | _, _, _, r, .enum_casesOn e bs => .enum_casesOn (e.rename r) (fun i => (bs i).rename r)
  | _, _, _, r, .record_mk as => .record_mk (as.rename r)
  | _, _, _, r, .record_casesOn e body => .record_casesOn (e.rename r) (body.rename (Ren.liftN r _))
  | _, _, _, r, .union_mk ix as => .union_mk ix (as.rename r)
  | _, _, _, r, .union_casesOn e bs => .union_casesOn (e.rename r) (bs.rename r)
  | _, _, _, r, .array_mk es => .array_mk (es.rename r)
  | _, _, _, r, .array_foldl a z s =>
      .array_foldl (a.rename r) (z.rename r) (s.rename (Ren.lift (Ren.lift r)))
  | _, _, _, r, .data_in b j e => .data_in b j (e.rename r)
  | _, _, _, r, .data_out b j e => .data_out b j (e.rename r)
  | _, _, _, r, .data_rec b ρ brs j e =>
      .data_rec b ρ (fun i => (brs i).rename (Ren.lift r)) j (e.rename r)
  | _, _, _, r, .data_brec b ρ k brs j e =>
      .data_brec b ρ k (fun i => (brs i).rename (Ren.lift r)) j (e.rename r)
  termination_by structural _ _ _ _ e => e
/-- `Term.rename` on arguments. -/
def Args.rename : {Γ Γ' : Ctx ks} → {σs : List (Ty ks)} → Ren Γ Γ' → Args Δ Γ σs → Args Δ Γ' σs
  | _, _, _, _, .nil => .nil
  | _, _, _, r, .cons a as => .cons (a.rename r) (as.rename r)
  termination_by structural _ _ _ _ a => a
/-- `Term.rename` on the branches of a case analysis. -/
def Branches.rename : {Γ Γ' : Ctx ks} → {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} →
    Ren Γ Γ' → Branches Δ Γ cs τ → Branches Δ Γ' cs τ
  | _, _, _, _, _, r, .two bc bd => .two (bc.rename (Ren.liftN r _)) (bd.rename (Ren.liftN r _))
  | _, _, _, _, _, r, .cons b bs => .cons (b.rename (Ren.liftN r _)) (bs.rename r)
  termination_by structural _ _ _ _ _ _ b => b
/-- `Term.rename` on the elements of an array literal. -/
def Elems.rename : {Γ Γ' : Ctx ks} → {t : Ty ks} → Ren Γ Γ' → Elems Δ Γ t → Elems Δ Γ' t
  | _, _, _, _, .nil => .nil
  | _, _, _, r, .cons e es => .cons (e.rename r) (es.rename r)
  termination_by structural _ _ _ _ e => e
end

/-- A term under one more (innermost) binder. -/
abbrev Term.weaken {Γ : Ctx ks} {σ τ : Ty ks} (e : Term Δ Γ τ) : Term Δ (σ :: Γ) τ :=
  e.rename Ren.weaken

end Rename

/-! ## Substitution -/

/-- A substitution: a term in `Γ'` for every variable of `Γ`. -/
abbrev Subst {ks : List Nat} (Δ : DSig ks) (Γ Γ' : Ctx ks) : Type :=
  ∀ {τ : Ty ks}, Var Γ τ → Term Δ Γ' τ

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
def single {Γ : Ctx ks} {σ : Ty ks} (a : Term Δ Γ σ) : Subst Δ (σ :: Γ) Γ
  | _, .head => a
  | _, .tail x => .var x

end Subst

section SubstDef
variable {ks : List Nat} {Δ : DSig ks}

mutual
/-- Replace every variable `x` of a term by `s x`. -/
def Term.subst : {Γ Γ' : Ctx ks} → {τ : Ty ks} → Subst Δ Γ Γ' → Term Δ Γ τ → Term Δ Γ' τ
  | _, _, _, s, .var x => s x
  | _, _, _, s, .letE e b => .letE (e.subst s) (b.subst (Subst.lift s))
  | _, _, _, s, .lam b => .lam (b.subst (Subst.lift s))
  | _, _, _, s, .app f a => .app (f.subst s) (a.subst s)
  | _, _, _, _, .lit p v h => .lit p v h
  | _, _, _, s, .extern n f as => .extern n f (as.subst s)
  | _, _, _, s, .ite c t e => .ite (c.subst s) (t.subst s) (e.subst s)
  | _, _, _, s, .nat_rec n z st =>
      .nat_rec (n.subst s) (z.subst s) (st.subst (Subst.lift (Subst.lift s)))
  | _, _, _, _, .enum_mk sc i => .enum_mk sc i
  | _, _, _, s, .enum_casesOn e bs => .enum_casesOn (e.subst s) (fun i => (bs i).subst s)
  | _, _, _, s, .record_mk as => .record_mk (as.subst s)
  | _, _, _, s, .record_casesOn e body =>
      .record_casesOn (e.subst s) (body.subst (Subst.liftN s _))
  | _, _, _, s, .union_mk ix as => .union_mk ix (as.subst s)
  | _, _, _, s, .union_casesOn e bs => .union_casesOn (e.subst s) (bs.subst s)
  | _, _, _, s, .array_mk es => .array_mk (es.subst s)
  | _, _, _, s, .array_foldl a z st =>
      .array_foldl (a.subst s) (z.subst s) (st.subst (Subst.lift (Subst.lift s)))
  | _, _, _, s, .data_in b j e => .data_in b j (e.subst s)
  | _, _, _, s, .data_out b j e => .data_out b j (e.subst s)
  | _, _, _, s, .data_rec b ρ brs j e =>
      .data_rec b ρ (fun i => (brs i).subst (Subst.lift s)) j (e.subst s)
  | _, _, _, s, .data_brec b ρ k brs j e =>
      .data_brec b ρ k (fun i => (brs i).subst (Subst.lift s)) j (e.subst s)
  termination_by structural _ _ _ _ e => e
/-- `Term.subst` on arguments. -/
def Args.subst : {Γ Γ' : Ctx ks} → {σs : List (Ty ks)} → Subst Δ Γ Γ' → Args Δ Γ σs →
    Args Δ Γ' σs
  | _, _, _, _, .nil => .nil
  | _, _, _, s, .cons a as => .cons (a.subst s) (as.subst s)
  termination_by structural _ _ _ _ a => a
/-- `Term.subst` on the branches of a case analysis. -/
def Branches.subst : {Γ Γ' : Ctx ks} → {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} →
    Subst Δ Γ Γ' → Branches Δ Γ cs τ → Branches Δ Γ' cs τ
  | _, _, _, _, _, s, .two bc bd => .two (bc.subst (Subst.liftN s _)) (bd.subst (Subst.liftN s _))
  | _, _, _, _, _, s, .cons b bs => .cons (b.subst (Subst.liftN s _)) (bs.subst s)
  termination_by structural _ _ _ _ _ _ b => b
/-- `Term.subst` on the elements of an array literal. -/
def Elems.subst : {Γ Γ' : Ctx ks} → {t : Ty ks} → Subst Δ Γ Γ' → Elems Δ Γ t → Elems Δ Γ' t
  | _, _, _, _, .nil => .nil
  | _, _, _, s, .cons e es => .cons (e.subst s) (es.subst s)
  termination_by structural _ _ _ _ e => e
end

/-- Fill the innermost variable of `b` with `a`. -/
abbrev Term.subst1 {Γ : Ctx ks} {σ τ : Ty ks} (b : Term Δ (σ :: Γ) τ) (a : Term Δ Γ σ) :
    Term Δ Γ τ :=
  b.subst (Subst.single a)

end SubstDef

/-! ## Evaluation commutes with renaming -/

section EvalRename
variable {ks : List Nat} {Δ : DSig ks}

/-- `ρ'` gives each renamed variable `r x` the value `ρ` gives `x`. -/
def EnvRen {Γ Γ' : Ctx ks} (r : Ren Γ Γ') (ρ' : Env Δ Γ') (ρ : Env Δ Γ) : Prop :=
  ∀ {τ : Ty ks} (x : Var Γ τ), ρ'.get (r x) = ρ.get x

theorem EnvRen.lift {Γ Γ' : Ctx ks} {σ : Ty ks} {r : Ren Γ Γ'} {ρ' : Env Δ Γ'} {ρ : Env Δ Γ}
    (h : EnvRen r ρ' ρ) (v : Ty.Den Δ σ) : EnvRen (Ren.lift r) ((v, ρ') : Env Δ (σ :: Γ'))
      ((v, ρ) : Env Δ (σ :: Γ)) := by
  intro τ x
  cases x with
  | head => rfl
  | tail x => exact h x

theorem EnvRen.liftN {Γ Γ' : Ctx ks} {r : Ren Γ Γ'} {ρ' : Env Δ Γ'} {ρ : Env Δ Γ}
    (h : EnvRen r ρ' ρ) : (zs : Ctx ks) → (vs : DenList (DSig.refDen Δ) zs) →
      EnvRen (Ren.liftN r zs) (DenList.append vs ρ') (DenList.append vs ρ)
  | [], _ => h
  | _ :: zs, vs => fun x => by
      cases x with
      | head => rfl
      | tail x => exact EnvRen.liftN h zs vs.2 x

theorem EnvRen.weaken {Γ : Ctx ks} {σ : Ty ks} (v : Ty.Den Δ σ) (ρ : Env Δ Γ) :
    EnvRen (Ren.weaken (y := σ)) ((v, ρ) : Env Δ (σ :: Γ)) ρ := fun _ => rfl

mutual
/-- Evaluating a renamed term in an environment related by the renaming gives the same value. -/
theorem Term.eval_rename : {Γ Γ' : Ctx ks} → {τ : Ty ks} → (e : Term Δ Γ τ) → (r : Ren Γ Γ') →
    (ρ' : Env Δ Γ') → (ρ : Env Δ Γ) → EnvRen r ρ' ρ → (e.rename r).eval ρ' = e.eval ρ
  | _, _, _, .var x, r, ρ', ρ, h => h x
  | _, _, _, .letE e b, r, ρ', ρ, h => by
      simp only [Term.rename, Term.eval]
      rw [Term.eval_rename e r ρ' ρ h]
      exact Term.eval_rename b _ _ _ (h.lift _)
  | _, _, _, .lam b, r, ρ', ρ, h => by
      simp only [Term.rename, Term.eval]
      funext v
      exact Term.eval_rename b _ _ _ (h.lift v)
  | _, _, _, .app f a, r, ρ', ρ, h => by
      simp only [Term.rename, Term.eval]
      rw [Term.eval_rename f r ρ' ρ h, Term.eval_rename a r ρ' ρ h]
  | _, _, _, .lit p v hp, r, ρ', ρ, h => rfl
  | _, _, _, .extern n f as, r, ρ', ρ, h => by
      simp only [Term.rename, Term.eval]
      rw [Args.eval_rename as r ρ' ρ h]
  | _, _, _, .ite c t e, r, ρ', ρ, h => by
      simp only [Term.rename, Term.eval]
      rw [Term.eval_rename c r ρ' ρ h, Term.eval_rename t r ρ' ρ h, Term.eval_rename e r ρ' ρ h]
  | _, _, _, .nat_rec n z st, r, ρ', ρ, h => by
      simp only [Term.rename, Term.eval]
      rw [Term.eval_rename n r ρ' ρ h, Term.eval_rename z r ρ' ρ h]
      congr 1
      funext k acc
      exact Term.eval_rename st _ _ _ (EnvRen.lift (EnvRen.lift (σ := .nat) h k) acc)
  | _, _, _, .enum_mk s i, r, ρ', ρ, h => rfl
  | _, _, _, .enum_casesOn e bs, r, ρ', ρ, h => by
      simp only [Term.rename, Term.eval]
      rw [Term.eval_rename e r ρ' ρ h]
      exact Term.eval_rename (bs _) r ρ' ρ h
  | _, _, _, .record_mk as, r, ρ', ρ, h => by
      simp only [Term.rename, Term.eval]
      rw [Args.eval_rename as r ρ' ρ h]
  | _, _, _, .record_casesOn e body, r, ρ', ρ, h => by
      simp only [Term.rename, Term.eval]
      rw [Term.eval_rename e r ρ' ρ h]
      exact Term.eval_rename body _ _ _ (h.liftN _ _)
  | _, _, _, .union_mk ix as, r, ρ', ρ, h => by
      simp only [Term.rename, Term.eval]
      rw [Args.eval_rename as r ρ' ρ h]
  | _, _, _, .union_casesOn e bs, r, ρ', ρ, h => by
      simp only [Term.rename, Term.eval]
      rw [Term.eval_rename e r ρ' ρ h]
      exact Branches.eval_rename bs r ρ' ρ h _
  | _, _, _, .array_mk es, r, ρ', ρ, h => by
      simp only [Term.rename, Term.eval]
      rw [Elems.eval_rename es r ρ' ρ h]
  | _, _, _, .array_foldl a z st, r, ρ', ρ, h => by
      simp only [Term.rename, Term.eval]
      rw [Term.eval_rename a r ρ' ρ h, Term.eval_rename z r ρ' ρ h]
      congr 1
      funext acc x
      exact Term.eval_rename st _ _ _ (EnvRen.lift (EnvRen.lift h acc) x)
  | _, _, _, .data_in b j e, r, ρ', ρ, h => by
      simp only [Term.rename, Term.eval]
      rw [Term.eval_rename e r ρ' ρ h]
  | _, _, _, .data_out b j e, r, ρ', ρ, h => by
      simp only [Term.rename, Term.eval]
      rw [Term.eval_rename e r ρ' ρ h]
  | _, _, _, .data_rec b ρt brs j e, r, ρ', ρ, h => by
      simp only [Term.rename, Term.eval]
      rw [Term.eval_rename e r ρ' ρ h]
      congr 1
      funext i x
      exact Term.eval_rename (brs i) _ _ _ (h.lift x)
  | _, _, _, .data_brec b ρt k brs j e, r, ρ', ρ, h => by
      simp only [Term.rename, Term.eval]
      rw [Term.eval_rename e r ρ' ρ h]
      congr 1
      funext i x
      exact Term.eval_rename (brs i) _ _ _ (h.lift x)
  termination_by structural _ _ _ e => e
theorem Args.eval_rename : {Γ Γ' : Ctx ks} → {σs : List (Ty ks)} → (as : Args Δ Γ σs) →
    (r : Ren Γ Γ') → (ρ' : Env Δ Γ') → (ρ : Env Δ Γ) → EnvRen r ρ' ρ →
    (as.rename r).eval ρ' = as.eval ρ
  | _, _, _, .nil, _, _, _, _ => rfl
  | _, _, _, .cons a as, r, ρ', ρ, h => by
      simp only [Args.rename, Args.eval]
      rw [Term.eval_rename a r ρ' ρ h, Args.eval_rename as r ρ' ρ h]
  termination_by structural _ _ _ a => a
theorem Branches.eval_rename : {Γ Γ' : Ctx ks} → {bs : List Bool} → {cs : Ctors ks bs} →
    {τ : Ty ks} → (brs : Branches Δ Γ cs τ) → (r : Ren Γ Γ') → (ρ' : Env Δ Γ') →
    (ρ : Env Δ Γ) → EnvRen r ρ' ρ → (x : Ctors.den (DSig.refDen Δ) cs) →
    (brs.rename r).eval ρ' x = brs.eval ρ x
  | _, _, _, _, _, .two bc bd, r, ρ', ρ, h, x => by
      simp only [Branches.rename, Branches.eval]
      congr 1
      · funext v; exact Term.eval_rename bc _ _ _ (h.liftN _ v)
      · funext v; exact Term.eval_rename bd _ _ _ (h.liftN _ v)
  | _, _, _, _, _, .cons b bs, r, ρ', ρ, h, x => by
      simp only [Branches.rename, Branches.eval]
      congr 1
      · funext v; exact Term.eval_rename b _ _ _ (h.liftN _ v)
      · funext y; exact Branches.eval_rename bs r ρ' ρ h y
  termination_by structural _ _ _ _ _ b => b
theorem Elems.eval_rename : {Γ Γ' : Ctx ks} → {t : Ty ks} → (es : Elems Δ Γ t) →
    (r : Ren Γ Γ') → (ρ' : Env Δ Γ') → (ρ : Env Δ Γ) → EnvRen r ρ' ρ →
    (es.rename r).eval ρ' = es.eval ρ
  | _, _, _, .nil, _, _, _, _ => rfl
  | _, _, _, .cons e es, r, ρ', ρ, h => by
      simp only [Elems.rename, Elems.eval]
      rw [Term.eval_rename e r ρ' ρ h, Elems.eval_rename es r ρ' ρ h]
  termination_by structural _ _ _ e => e
end

/-- A weakened term ignores the value of the new variable. -/
theorem Term.eval_weaken {Γ : Ctx ks} {σ τ : Ty ks} (e : Term Δ Γ τ) (v : Ty.Den Δ σ)
    (ρ : Env Δ Γ) : (e.weaken (σ := σ)).eval ((v, ρ) : Env Δ (σ :: Γ)) = e.eval ρ :=
  Term.eval_rename e _ _ _ (EnvRen.weaken v ρ)

end EvalRename

/-! ## Evaluation commutes with substitution -/

section EvalSubst
variable {ks : List Nat} {Δ : DSig ks}

/-- In `ρ'`, each substituted term `s x` has the value `ρ` gives `x`. -/
def EnvSub {Γ Γ' : Ctx ks} (s : Subst Δ Γ Γ') (ρ' : Env Δ Γ') (ρ : Env Δ Γ) : Prop :=
  ∀ {τ : Ty ks} (x : Var Γ τ), (s x).eval ρ' = ρ.get x

theorem EnvSub.lift {Γ Γ' : Ctx ks} {σ : Ty ks} {s : Subst Δ Γ Γ'} {ρ' : Env Δ Γ'}
    {ρ : Env Δ Γ} (h : EnvSub s ρ' ρ) (v : Ty.Den Δ σ) :
    EnvSub (Subst.lift s) ((v, ρ') : Env Δ (σ :: Γ')) ((v, ρ) : Env Δ (σ :: Γ)) := fun x => by
  cases x with
  | head => rfl
  | tail x => exact (Term.eval_weaken _ _ _).trans (h x)

theorem EnvSub.liftN {Γ Γ' : Ctx ks} {s : Subst Δ Γ Γ'} {ρ' : Env Δ Γ'} {ρ : Env Δ Γ}
    (h : EnvSub s ρ' ρ) : (zs : Ctx ks) → (vs : DenList (DSig.refDen Δ) zs) →
      EnvSub (Subst.liftN s zs) (DenList.append vs ρ') (DenList.append vs ρ)
  | [], _ => h
  | _ :: zs, vs => EnvSub.lift (EnvSub.liftN h zs vs.2) vs.1

theorem EnvSub.single {Γ : Ctx ks} {σ : Ty ks} (a : Term Δ Γ σ) (ρ : Env Δ Γ) :
    EnvSub (Subst.single a) ρ ((a.eval ρ, ρ) : Env Δ (σ :: Γ)) := fun x => by
  cases x with
  | head => rfl
  | tail x => rfl

theorem EnvSub.id {Γ : Ctx ks} (ρ : Env Δ Γ) : EnvSub (Subst.id (Δ := Δ)) ρ ρ := fun _ => rfl

mutual
/-- Evaluating a substituted term in an environment related by the substitution gives the same value. -/
theorem Term.eval_subst : {Γ Γ' : Ctx ks} → {τ : Ty ks} → (e : Term Δ Γ τ) → (s : Subst Δ Γ Γ') →
    (ρ' : Env Δ Γ') → (ρ : Env Δ Γ) → EnvSub s ρ' ρ → (e.subst s).eval ρ' = e.eval ρ
  | _, _, _, .var x, s, ρ', ρ, h => h x
  | _, _, _, .letE e b, s, ρ', ρ, h => by
      simp only [Term.subst, Term.eval]
      rw [Term.eval_subst e s ρ' ρ h]
      exact Term.eval_subst b _ _ _ (h.lift _)
  | _, _, _, .lam b, s, ρ', ρ, h => by
      simp only [Term.subst, Term.eval]
      funext v
      exact Term.eval_subst b _ _ _ (h.lift v)
  | _, _, _, .app f a, s, ρ', ρ, h => by
      simp only [Term.subst, Term.eval]
      rw [Term.eval_subst f s ρ' ρ h, Term.eval_subst a s ρ' ρ h]
  | _, _, _, .lit p v hp, s, ρ', ρ, h => rfl
  | _, _, _, .extern n f as, s, ρ', ρ, h => by
      simp only [Term.subst, Term.eval]
      rw [Args.eval_subst as s ρ' ρ h]
  | _, _, _, .ite c t e, s, ρ', ρ, h => by
      simp only [Term.subst, Term.eval]
      rw [Term.eval_subst c s ρ' ρ h, Term.eval_subst t s ρ' ρ h, Term.eval_subst e s ρ' ρ h]
  | _, _, _, .nat_rec n z st, s, ρ', ρ, h => by
      simp only [Term.subst, Term.eval]
      rw [Term.eval_subst n s ρ' ρ h, Term.eval_subst z s ρ' ρ h]
      congr 1
      funext k acc
      exact Term.eval_subst st _ _ _ (EnvSub.lift (EnvSub.lift (σ := .nat) h k) acc)
  | _, _, _, .enum_mk _ _, s, ρ', ρ, h => rfl
  | _, _, _, .enum_casesOn e bs, s, ρ', ρ, h => by
      simp only [Term.subst, Term.eval]
      rw [Term.eval_subst e s ρ' ρ h]
      exact Term.eval_subst (bs _) s ρ' ρ h
  | _, _, _, .record_mk as, s, ρ', ρ, h => by
      simp only [Term.subst, Term.eval]
      rw [Args.eval_subst as s ρ' ρ h]
  | _, _, _, .record_casesOn e body, s, ρ', ρ, h => by
      simp only [Term.subst, Term.eval]
      rw [Term.eval_subst e s ρ' ρ h]
      exact Term.eval_subst body _ _ _ (h.liftN _ _)
  | _, _, _, .union_mk ix as, s, ρ', ρ, h => by
      simp only [Term.subst, Term.eval]
      rw [Args.eval_subst as s ρ' ρ h]
  | _, _, _, .union_casesOn e bs, s, ρ', ρ, h => by
      simp only [Term.subst, Term.eval]
      rw [Term.eval_subst e s ρ' ρ h]
      exact Branches.eval_subst bs s ρ' ρ h _
  | _, _, _, .array_mk es, s, ρ', ρ, h => by
      simp only [Term.subst, Term.eval]
      rw [Elems.eval_subst es s ρ' ρ h]
  | _, _, _, .array_foldl a z st, s, ρ', ρ, h => by
      simp only [Term.subst, Term.eval]
      rw [Term.eval_subst a s ρ' ρ h, Term.eval_subst z s ρ' ρ h]
      congr 1
      funext acc x
      exact Term.eval_subst st _ _ _ (EnvSub.lift (EnvSub.lift h acc) x)
  | _, _, _, .data_in b j e, s, ρ', ρ, h => by
      simp only [Term.subst, Term.eval]
      rw [Term.eval_subst e s ρ' ρ h]
  | _, _, _, .data_out b j e, s, ρ', ρ, h => by
      simp only [Term.subst, Term.eval]
      rw [Term.eval_subst e s ρ' ρ h]
  | _, _, _, .data_rec b ρt brs j e, s, ρ', ρ, h => by
      simp only [Term.subst, Term.eval]
      rw [Term.eval_subst e s ρ' ρ h]
      congr 1
      funext i x
      exact Term.eval_subst (brs i) _ _ _ (h.lift x)
  | _, _, _, .data_brec b ρt k brs j e, s, ρ', ρ, h => by
      simp only [Term.subst, Term.eval]
      rw [Term.eval_subst e s ρ' ρ h]
      congr 1
      funext i x
      exact Term.eval_subst (brs i) _ _ _ (h.lift x)
  termination_by structural _ _ _ e => e
theorem Args.eval_subst : {Γ Γ' : Ctx ks} → {σs : List (Ty ks)} → (as : Args Δ Γ σs) →
    (s : Subst Δ Γ Γ') → (ρ' : Env Δ Γ') → (ρ : Env Δ Γ) → EnvSub s ρ' ρ →
    (as.subst s).eval ρ' = as.eval ρ
  | _, _, _, .nil, _, _, _, _ => rfl
  | _, _, _, .cons a as, s, ρ', ρ, h => by
      simp only [Args.subst, Args.eval]
      rw [Term.eval_subst a s ρ' ρ h, Args.eval_subst as s ρ' ρ h]
  termination_by structural _ _ _ a => a
theorem Branches.eval_subst : {Γ Γ' : Ctx ks} → {bs : List Bool} → {cs : Ctors ks bs} →
    {τ : Ty ks} → (brs : Branches Δ Γ cs τ) → (s : Subst Δ Γ Γ') → (ρ' : Env Δ Γ') →
    (ρ : Env Δ Γ) → EnvSub s ρ' ρ → (x : Ctors.den (DSig.refDen Δ) cs) →
    (brs.subst s).eval ρ' x = brs.eval ρ x
  | _, _, _, _, _, .two bc bd, s, ρ', ρ, h, x => by
      simp only [Branches.subst, Branches.eval]
      congr 1
      · funext v; exact Term.eval_subst bc _ _ _ (h.liftN _ v)
      · funext v; exact Term.eval_subst bd _ _ _ (h.liftN _ v)
  | _, _, _, _, _, .cons b bs, s, ρ', ρ, h, x => by
      simp only [Branches.subst, Branches.eval]
      congr 1
      · funext v; exact Term.eval_subst b _ _ _ (h.liftN _ v)
      · funext y; exact Branches.eval_subst bs s ρ' ρ h y
  termination_by structural _ _ _ _ _ b => b
theorem Elems.eval_subst : {Γ Γ' : Ctx ks} → {t : Ty ks} → (es : Elems Δ Γ t) →
    (s : Subst Δ Γ Γ') → (ρ' : Env Δ Γ') → (ρ : Env Δ Γ) → EnvSub s ρ' ρ →
    (es.subst s).eval ρ' = es.eval ρ
  | _, _, _, .nil, _, _, _, _ => rfl
  | _, _, _, .cons e es, s, ρ', ρ, h => by
      simp only [Elems.subst, Elems.eval]
      rw [Term.eval_subst e s ρ' ρ h, Elems.eval_subst es s ρ' ρ h]
  termination_by structural _ _ _ e => e
end


/-- Filling the innermost variable of `b` with `a` means evaluating `b` with the value of `a`
    bound to it. -/
theorem Term.eval_subst1 {Γ : Ctx ks} {σ τ : Ty ks} (b : Term Δ (σ :: Γ) τ) (a : Term Δ Γ σ)
    (ρ : Env Δ Γ) : (b.subst1 a).eval ρ = b.eval ((a.eval ρ, ρ) : Env Δ (σ :: Γ)) :=
  Term.eval_subst b _ _ _ (EnvSub.single a ρ)

/-- A `let` means its substitution instance. -/
theorem Term.eval_letE_eq_subst1 {Γ : Ctx ks} {σ τ : Ty ks} (e : Term Δ Γ σ)
    (b : Term Δ (σ :: Γ) τ) (ρ : Env Δ Γ) : (Term.letE e b).eval ρ = (b.subst1 e).eval ρ :=
  (Term.eval_subst1 b e ρ).symm

/-- β: a function applied to an argument means the body with the argument substituted. -/
theorem Term.eval_app_lam_eq_subst1 {Γ : Ctx ks} {σ τ : Ty ks} (b : Term Δ (σ :: Γ) τ)
    (a : Term Δ Γ σ) (ρ : Env Δ Γ) : (Term.app (.lam b) a).eval ρ = (b.subst1 a).eval ρ :=
  (Term.eval_subst1 b a ρ).symm

/-- The identity substitution does not change the value. -/
theorem Term.eval_subst_id {Γ : Ctx ks} {τ : Ty ks} (e : Term Δ Γ τ) (ρ : Env Δ Γ) :
    (e.subst Subst.id).eval ρ = e.eval ρ :=
  Term.eval_subst e _ _ _ (EnvSub.id ρ)

end EvalSubst

end LeanScript

end
