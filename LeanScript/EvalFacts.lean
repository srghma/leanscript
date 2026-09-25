module

public import LeanScript.Eval

@[expose] public section

set_option autoImplicit false

namespace LeanScript

/-! # What the evaluator does, stated

The clauses below are the ones worth naming: they hold by `rfl`, and they say that the
language's application is Lean's, that a `let` is a substitution, that a delay carries
nothing, and that reading the fields of the constructor a value was built with gives them
back. -/

variable {Sg : Sig} {Γ : Ctx} {σ τ : TyWf} (G : GlobalEnv Sg.decls)

/-- Applying an abstraction is substituting the argument's value for the bound
    variable. -/
theorem Term.eval_beta (body : Term Sg (σ :: Γ) τ) (a : Term Sg Γ σ) (env : Env Γ) :
    Term.eval G (.ap (.lam body) a) env =
      Term.eval G body (Term.eval G a env, env) :=
  rfl

/-- `let x = e; body` binds the value of `e`. -/
theorem Term.eval_letE (e : Term Sg Γ σ) (body : Term Sg (σ :: Γ) τ) (env : Env Γ) :
    Term.eval G (.letE e body) env =
      Term.eval G body (Term.eval G e env, env) :=
  rfl

/-- Forcing a delay gives back what was delayed. -/
theorem Term.eval_lazy_force_mk (e : Term Sg Γ τ) (env : Env Γ) :
    Term.eval G (.lazy_force (.lazy_mk e)) env = Term.eval G e env :=
  rfl

/-- Forcing a thunk gives back what was delayed. -/
theorem Term.eval_thunk_force_mk (e : Term Sg Γ τ) (env : Env Γ) :
    Term.eval G (.thunk_force (.thunk_mk e)) env = Term.eval G e env :=
  rfl

/-- An extern is the Lean function it implements. -/
theorem Term.eval_extern (e : Extern τ) (env : Env Γ) :
    Term.eval (Sg := Sg) G (.extern e) env = Extern.eval e :=
  rfl

/-- An extern applied to terms is the Lean function called on their values. -/
theorem Term.eval_externCall {σs : List TyWf} (args : Spine Sg Γ σs)
    (call : TyWf.DenList σs → Extern τ) (env : Env Γ) :
    Term.eval G (.externCall args call) env = Extern.eval (call (Spine.eval G args env)) :=
  rfl

/-- An extern that takes a proof, applied to terms whose values satisfy the proposition,
    is the Lean function called on those values, with the proof. -/
theorem Term.eval_externCallChecked_of_some {σs : List TyWf} (args : Spine Sg Γ σs)
    (call : TyWf.DenList σs → Option (Extern τ)) (fallback : Term Sg Γ τ) (env : Env Γ)
    (e : Extern τ)
    (he : call (Spine.eval G args env) = some e) :
    Term.eval G (.externCallChecked args call fallback) env = Extern.eval e := by
  show (match call (Spine.eval G args env) with
    | some e => Extern.eval e
    | none => Term.eval G fallback env) = _
  rw [he]

/-- The tag of a tagged value is the constructor it was built with. -/
theorem Term.eval_taggedUnion_mk_fst {l : LeanTaggedUnionSchema TyWf} (t : Nat)
    (ht : t < l.length) (fields : Spine Sg Γ (l.get t ht)) (env : Env Γ) :
    (Term.eval G (.taggedUnion_mk l t ht fields) env).1.val = t :=
  rfl

/-- The fields of a tagged value are the ones it was built with. -/
theorem Term.eval_taggedUnion_field? {l : LeanTaggedUnionSchema TyWf} (t : Nat)
    (ht : t < l.length) (fields : Spine Sg Γ (l.get t ht)) (env : Env Γ) :
    TyWf.DenTU.field? t ht (Term.eval G (.taggedUnion_mk l t ht fields) env) =
      some (Spine.eval G fields env) :=
  TyWf.DenTU.field?_mk t ht _

end LeanScript

end
