module

public import LeanScript.Eval
public import LeanScript.EvalFacts

@[expose] public section

set_option autoImplicit false

/-!
# Environments that agree along a renaming

`EnvRel ρ env env'`, and the value of an atom (list of atoms) under a renaming — the leaf
cases of `LeanScript.RenameEvalFacts`.
-/

namespace LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

variable {Sg : Sig}

/-! ## Environments that agree along a renaming -/

/-- `env'` agrees with `env` along `ρ`: the variable `ρ v` has in `env'` the value `v` has
    in `env`. -/
def EnvRel {Γ Δ : Ctx} (ρ : Ren Γ Δ) (env : Env Γ) (env' : Env Δ) : Prop :=
  ∀ {τ : TyWf} (v : Γ ∋ τ), Env.get (ρ v) env' = Env.get v env

namespace EnvRel

theorem id' {Γ : Ctx} (env : Env Γ) : EnvRel Ren.id env env := fun _ => rfl

theorem wk {Γ : Ctx} {σ : TyWf} (x : TyWf.Den σ) (env : Env Γ) :
    EnvRel (Ren.wk (σ := σ)) env (x, env) := fun _ => rfl

theorem nil {Δ : Ctx} (env : Env []) (env' : Env Δ) : EnvRel Ren.nil env env' :=
  fun v => nomatch v

theorem comp {Γ Δ Θ : Ctx} {ρ : Ren Γ Δ} {ρ' : Ren Δ Θ} {env : Env Γ} {env' : Env Δ}
    {env'' : Env Θ} (h' : EnvRel ρ' env' env'') (h : EnvRel ρ env env') :
    EnvRel (Ren.comp ρ' ρ) env env'' := fun v => (h' (ρ v)).trans (h v)

theorem lift {Γ Δ : Ctx} {σ : TyWf} {ρ : Ren Γ Δ} {env : Env Γ} {env' : Env Δ}
    (h : EnvRel ρ env env') (x : TyWf.Den σ) :
    EnvRel (Ren.lift (σ := σ) ρ) (x, env) (x, env') := by
  intro _ v
  cases v with
  | head => rfl
  | tail v => exact h v

theorem cons {Γ Δ : Ctx} {σ : TyWf} {ρ : Ren Γ Δ} {env : Env Γ} {env' : Env Δ}
    (h : EnvRel ρ env env') (v : Δ ∋ σ) :
    EnvRel (Ren.cons v ρ) (Env.get v env', env) env' := by
  intro _ w
  cases w with
  | head => rfl
  | tail w => exact h w

theorem liftN {Γ Δ : Ctx} {ρ : Ren Γ Δ} {env : Env Γ} {env' : Env Δ}
    (h : EnvRel ρ env env') :
    (xs : List TyWf) → (vs : TyWf.DenList xs) →
      EnvRel (Ren.liftN xs ρ) (Env.append vs env) (Env.append vs env')
  | [], _ => h
  | _ :: xs, vs => lift (liftN h xs vs.2) vs.1

theorem liftNat {Γ Δ : Ctx} {ρ : Ren Γ Δ} {env : Env Γ} {env' : Env Δ}
    (h : EnvRel ρ env env') (τ : TyWf) :
    (k : Nat) → (w : NatWin τ k) →
      EnvRel (Ren.liftNat τ k ρ) (Env.ofWin w env) (Env.ofWin w env')
  | 0, _ => h
  | k + 1, w => lift (liftNat h τ k w.2) w.1

end EnvRel

/-! ## Atoms and lists of atoms -/

theorem Atom.eval_rename {Γ Δ : Ctx} {τ : TyWf} {ρ : Ren Γ Δ} {env : Env Γ} {env' : Env Δ}
    (h : EnvRel ρ env env') (a : Atom Γ τ) : Atom.eval (a.rename ρ) env' = Atom.eval a env := by
  cases a with
  | var v => exact h v

theorem Args.eval_rename (G : GlobalEnv Sg.decls) {Γ Δ : Ctx} {ρ : Ren Γ Δ} {env : Env Γ}
    {env' : Env Δ} (h : EnvRel ρ env env') :
    {σs : List TyWf} → (as : Args Sg Γ σs) → Args.eval G (as.rename ρ) env' = Args.eval G as env
  | _, .nil => rfl
  | _, .cons a as => by
      show (Atom.eval (a.rename ρ) env', Args.eval G (as.rename ρ) env') = _
      rw [Atom.eval_rename h, Args.eval_rename G h as]; rfl

theorem FamilyMemberArgs.eval_rename (G : GlobalEnv Sg.decls) {Γ Δ : Ctx} {ρ : Ren Γ Δ}
    {env : Env Γ} {env' : Env Δ} (h : EnvRel ρ env env') :
    {m : LeanFamMemberSchema TyWf} → (as : FamilyMemberArgs Sg Γ m) →
      FamilyMemberArgs.eval G (as.rename ρ) env' = FamilyMemberArgs.eval G as env
  | _, .ctors _ t ht fields =>
      congrArg (fun x => TyWf.DenTU.mk t ht (TyWf.DenFields.ofList x)) (Args.eval_rename G h fields)
  | _, .record fs fields =>
      congrArg (fun x => cast (Ty.denRecord_eq (fs.map TyWf.toTy)).symm
          (TyWf.DenFields.ofList (ts := fs.toList) x))
        (Args.eval_rename G h fields)
  | _, .alias _ value => Atom.eval_rename h value

end LeanScript

end
