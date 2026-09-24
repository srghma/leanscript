module

public import LeanScript.Eval

@[expose] public section

set_option autoImplicit false

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

namespace LeanScript

/-!
# What the evaluator does with a recursive record and a recursive newtype

The analogue of the ι-rules of `LeanScript.RecUnionEvalFacts` for the two other recursive
shapes that have values.

* **Reading back.**  The unfolded fields of a record built by `Term.recObject_mk` are the
  values of the fields it was built with (`Term.eval_recObject_mk_unfold`), and the
  unfolded body of a newtype built by `Term.recAlias_mk` is the value it was built with
  (`Term.eval_recAlias_mk_unfold`).
* **ι-rules for the eliminator.**  Taking apart a value built by the introduction form
  binds exactly those values (`Term.eval_recObject_casesOn_mk`,
  `Term.eval_recAlias_casesOn_mk`).

All of them rest on the round trips `TyWf.DenObj.unfold_mk` and `TyWf.DenAlias.unfold_mk`
of `LeanScript.Den.RecObjectAlias` (and `Ty.unroll_roll` below them).
-/

variable {Sg : Sig} (G : GlobalEnv Sg.decls)

/-! ## Recursive records -/

/-- The unfolded fields of a record built by the introduction form are the values of the
    fields it was built with. -/
theorem Term.eval_recObject_mk_unfold {Γ : Ctx} (fs : LeanRecordSchema (TyWfIn 1))
    (hwf : Ty.Wf (TyWf.recObjectTy fs))
    (fields : Spine Sg Γ (TyWf.recObjectUnfold fs hwf).toList) (env : Env Γ) :
    TyWf.DenObj.unfold fs hwf (Term.eval G (.recObject_mk fs hwf fields) env) =
      Spine.eval G fields env :=
  TyWf.DenObj.unfold_mk fs hwf _

/-- Taking apart a record built by the introduction form binds the values of the fields
    it was built with. -/
theorem Term.eval_recObject_casesOn_mk {Γ : Ctx} {τ : TyWf}
    (fs : LeanRecordSchema (TyWfIn 1)) (hwf : Ty.Wf (TyWf.recObjectTy fs))
    (fields : Spine Sg Γ (TyWf.recObjectUnfold fs hwf).toList)
    (body : Term Sg ((TyWf.recObjectUnfold fs hwf).toList ++ Γ) τ) (env : Env Γ) :
    Term.eval G (.recObject_casesOn (.recObject_mk fs hwf fields) body) env =
      Term.eval G body (Env.append (Spine.eval G fields env) env) := by
  show Term.eval G body
      (Env.append (TyWf.DenObj.unfold fs hwf (TyWf.DenObj.mk fs hwf _)) env) = _
  rw [TyWf.DenObj.unfold_mk]

/-! ## Recursive newtypes -/

/-- The unfolded body of a newtype built by the introduction form is the value it was
    built with. -/
theorem Term.eval_recAlias_mk_unfold {Γ : Ctx} (b : TyWfIn 1)
    (hwf : Ty.Wf (TyWf.recAliasTy b)) (value : Term Sg Γ (TyWf.recAliasUnfold b hwf))
    (env : Env Γ) :
    TyWf.DenAlias.unfold b hwf (Term.eval G (.recAlias_mk b hwf value) env) =
      Term.eval G value env :=
  TyWf.DenAlias.unfold_mk b hwf _

/-- Taking apart a newtype built by the introduction form binds the value it was built
    with. -/
theorem Term.eval_recAlias_casesOn_mk {Γ : Ctx} {τ : TyWf} (b : TyWfIn 1)
    (hwf : Ty.Wf (TyWf.recAliasTy b)) (value : Term Sg Γ (TyWf.recAliasUnfold b hwf))
    (body : Term Sg (TyWf.recAliasUnfold b hwf :: Γ) τ) (env : Env Γ) :
    Term.eval G (.recAlias_casesOn (.recAlias_mk b hwf value) body) env =
      Term.eval G body (Term.eval G value env, env) := by
  show Term.eval G body
      (TyWf.DenAlias.unfold b hwf (TyWf.DenAlias.mk b hwf _), env) = _
  rw [TyWf.DenAlias.unfold_mk]

end LeanScript

end
