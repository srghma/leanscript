module

public import LeanScript.Eval
public import LeanScript.Expr.Build

@[expose] public section

set_option autoImplicit false

/-!
# Renaming does not change a value

`Term.eval_rename`: a renamed term, run in an environment that agrees with the original
one along the renaming, has the value the original term has there.  This is what makes
the A-normalising builders of `LeanScript.Expr.Build` correct, which
`LeanScript.EvalBuild` states.
-/

namespace LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-- `env'` agrees with `env` along `ρ`: the variable `ρ v` has in `env'` the value `v` has
    in `env`. -/
def EnvRel {Γ Δ : Ctx} (ρ : Ren Γ Δ) (env : Env Γ) (env' : Env Δ) : Prop :=
  ∀ {τ : TyWf} (v : Γ ∋ τ), Env.get (ρ v) env' = Env.get v env

theorem EnvRel.lift {Γ Δ : Ctx} {σ : TyWf} {ρ : Ren Γ Δ} {env : Env Γ} {env' : Env Δ}
    (h : EnvRel ρ env env') (x : TyWf.Den σ) :
    EnvRel (Ren.lift (σ := σ) ρ) (x, env) (x, env') := by
  intro τ v
  match v with
  | .head => rfl
  | .tail v => exact h v

theorem EnvRel.liftN {Γ Δ : Ctx} {ρ : Ren Γ Δ} {env : Env Γ} {env' : Env Δ}
    (h : EnvRel ρ env env') :
    (xs : List TyWf) → (vs : TyWf.DenList xs) →
      EnvRel (Ren.liftN xs ρ) (Env.append vs env) (Env.append vs env')
  | [], _ => h
  | _ :: xs, vs => EnvRel.lift (EnvRel.liftN h xs vs.2) vs.1

theorem EnvRel.liftNat {Γ Δ : Ctx} {ρ : Ren Γ Δ} {env : Env Γ} {env' : Env Δ}
    (h : EnvRel ρ env env') (τ : TyWf) :
    (k : Nat) → (w : NatWin τ k) →
      EnvRel (Ren.liftNat τ k ρ) (Env.ofWin w env) (Env.ofWin w env')
  | 0, _ => h
  | k + 1, w => EnvRel.lift (EnvRel.liftNat h τ k w.2) w.1

theorem EnvRel.wk {Γ : Ctx} {σ : TyWf} (env : Env Γ) (x : TyWf.Den σ) :
    EnvRel (Ren.wk (σ := σ)) env (x, env) := fun _ => rfl

theorem EnvRel.id {Γ : Ctx} (env : Env Γ) : EnvRel Ren.id env env := fun _ => rfl

theorem EnvRel.comp {Γ Δ Θ : Ctx} {ρ : Ren Γ Δ} {ρ' : Ren Δ Θ} {env : Env Γ}
    {env' : Env Δ} {env'' : Env Θ} (h : EnvRel ρ env env') (h' : EnvRel ρ' env' env'') :
    EnvRel (Ren.comp ρ' ρ) env env'' := fun v => (h' (ρ v)).trans (h v)

variable {Sg : Sig} (G : GlobalEnv Sg.decls)

theorem Atom.eval_rename {Γ Δ : Ctx} {τ : TyWf} {ρ : Ren Γ Δ} {env : Env Γ}
    {env' : Env Δ} (h : EnvRel ρ env env') (a : Atom Sg Γ τ) :
    Atom.eval G (a.rename ρ) env' = Atom.eval G a env := by
  cases a <;> first | rfl | exact h _

theorem Args.eval_rename {Γ Δ : Ctx} {ρ : Ren Γ Δ} {env : Env Γ} {env' : Env Δ}
    (h : EnvRel ρ env env') :
    {σs : List TyWf} → (as : Args Sg Γ σs) → Args.eval G (as.rename ρ) env' = Args.eval G as env
  | _, .nil => rfl
  | _, .cons a as => by
      simp only [Args.rename, Args.eval, Atom.eval_rename G h, Args.eval_rename h as]

theorem FamilyMemberArgs.eval_rename {Γ Δ : Ctx} {ρ : Ren Γ Δ} {env : Env Γ}
    {env' : Env Δ} (h : EnvRel ρ env env') :
    {m : LeanFamMemberSchema TyWf} → (as : FamilyMemberArgs Sg Γ m) →
      FamilyMemberArgs.eval G (as.rename ρ) env' = FamilyMemberArgs.eval G as env
  | _, .ctors l t ht fields => by
      simp only [FamilyMemberArgs.rename, FamilyMemberArgs.eval, Args.eval_rename G h]
  | _, .record fs fields => by
      simp only [FamilyMemberArgs.rename, FamilyMemberArgs.eval, Args.eval_rename G h]
  | _, .alias b value => by
      simp only [FamilyMemberArgs.rename, FamilyMemberArgs.eval, Atom.eval_rename G h]

mutual

theorem Term.eval_rename {Γ Δ : Ctx} {τ : TyWf} (ρ : Ren Γ Δ) :
    (t : Term Sg Γ τ) → (env : Env Γ) → (env' : Env Δ) → EnvRel ρ env env' →
      Term.eval G (t.rename ρ) env' = Term.eval G t env
  | .ret c, env, env', h => Comp.eval_rename ρ c env env' h
  | .letE c body, env, env', h => by
      simp only [Term.rename, Term.eval, Comp.eval_rename ρ c env env' h]
      exact Term.eval_rename (Ren.lift ρ) body _ _ (h.lift _)

theorem Comp.eval_rename {Γ Δ : Ctx} {τ : TyWf} (ρ : Ren Γ Δ) :
    (c : Comp Sg Γ τ) → (env : Env Γ) → (env' : Env Δ) → EnvRel ρ env env' →
      Comp.eval G (c.rename ρ) env' = Comp.eval G c env
  | .atom a, env, env', h => Atom.eval_rename G h a
  | .lam body, env, env', h =>
      funext fun x => Term.eval_rename (Ren.lift ρ) body _ _ (h.lift x)
  | .ap f a, env, env', h => by
      simp only [Comp.rename, Comp.eval, Atom.eval_rename G h]
  | .extern e, env, env', h => rfl
  | .externCall args call, env, env', h => by
      simp only [Comp.rename, Comp.eval, Args.eval_rename G h]
  | .externCallChecked args call fallback, env, env', h => by
      simp only [Comp.rename, Comp.eval, Args.eval_rename G h,
        Term.eval_rename ρ fallback env env' h]
  | .bool_casesOn c t e, env, env', h => by
      simp only [Comp.rename, Comp.eval, Atom.eval_rename G h,
        Term.eval_rename ρ t env env' h, Term.eval_rename ρ e env env' h]
  | .nat_casesOn n z s, env, env', h => by
      simp only [Comp.rename, Comp.eval, Atom.eval_rename G h,
        Term.eval_rename ρ z env env' h,
        fun x => Term.eval_rename (Ren.lift ρ) s (x, env) (x, env') (h.lift x)]
  | _, _, _, _ => sorry

end

end LeanScript

end
