module

public import LeanScript.Eval.Env
public import LeanScript.Eval.Extern
public import LeanScript.Den.Rec
public import LeanScript.Den.RecObjectAlias
public import LeanScript.Den.Family

@[expose] public section

set_option autoImplicit false

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

namespace LeanScript

/-!
# Evaluating atoms, and the values of join points

The leaves of the evaluator `LeanScript.Term.eval`: the value of an atom and of a list
of atoms, and `JEnv`, the values of the join points in scope.
-/

/-! ## Atoms -/

/-- The value of an atom: the variable is read off the environment. -/
def Atom.eval {Γ : Ctx} {τ : TyWf} : Atom Γ τ → Env Γ → TyWf.Den τ
  | .var v, env => Env.get v env

/-- The values of a list of atoms, typed by the list of their types. -/
def Args.eval {Sg : Sig} (G : GlobalEnv Sg.decls) {Γ : Ctx} :
    {σs : List TyWf} → Args Sg Γ σs → Env Γ → TyWf.DenList σs
  | _, .nil, _ => PUnit.unit
  | _, .cons a as, env => (Atom.eval a env, Args.eval G as env)

/-- The value of a member of a mutual family, built from the shape that member has. -/
def FamilyMemberArgs.eval {Sg : Sig} (G : GlobalEnv Sg.decls) {Γ : Ctx} :
    {m : LeanFamMemberSchema TyWf} → FamilyMemberArgs Sg Γ m → Env Γ → TyWf.DenMember m
  | _, .ctors _ t ht fields, env => TyWf.DenTU.mk t ht (TyWf.DenFields.ofList (Args.eval G fields env))
  | _, .record _ fields, env =>
      cast (Ty.denRecord_eq _).symm (TyWf.DenFields.ofList (Args.eval G fields env))
  | _, .alias _ value, env => Atom.eval value env

/-! ## Join points -/

/-- The values of the join points in scope, for a term of type `τ`: each join point of
    parameter type `σ` is the function `TyWf.Den σ → TyWf.Den τ` its body computes. -/
def JEnv (τ : TyWf) : JCtx → Type
  | [] => PUnit
  | σ :: J => (TyWf.Den σ → TyWf.Den τ) × JEnv τ J

/-- The function a join point stands for. -/
def JEnv.get {τ : TyWf} : {J : JCtx} → {σ : TyWf} → (J ∋ σ) → JEnv τ J →
    TyWf.Den σ → TyWf.Den τ
  | _ :: _, _, .head, jenv => jenv.1
  | _ :: _, _, .tail j, jenv => JEnv.get j jenv.2

/-- Deliver the answer of a fold to its destination: it is the value of the term, or it is
    passed to a join point. -/
def Dest.apply {J : JCtx} {ρ τ : TyWf} : Dest J ρ τ → JEnv τ J → TyWf.Den ρ → TyWf.Den τ
  | .ret, _, v => v
  | .jump j, jenv, v => JEnv.get j jenv v

end LeanScript

end
