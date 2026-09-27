module

public import LeanScript.Term.TermSubst
public import TermTests.TermTest
public meta import LeanScript.TacticElab.KernelRfl

@[expose] public section

set_option autoImplicit false

/-!
# Renaming and substitution of terms (`LeanScript.TermSubst`)

Weakening and substitution on the programs of `TermTests.TermTest`, run by `rfl`, and the
general facts used on them.
-/

namespace TermSubstTest

open LeanScript TermTest

/-- `sumT` applied to a pure argument: `let f := sumT; f a`. -/
def appT' {Γ : Ctx [0, 0]} (a : PExpr Δ Γ listNat) : Term Δ Γ .nat [] :=
  .letE sumT (.ofComp (.app (.bvar 0) a.weaken))

/-- `fun x => x + y`, with `y` free (index `0` of the outer context). -/
def addY : Comp Δ [.nat] (.fn .nat .nat) := .lam (.ret (addT (.bvar 0) (.bvar 1)))

/-- Weakening moves `addY` under a binder it does not use. -/
example : (Term.letE (.share (natT 100)) (.letE addY.weaken (.ofComp (.app (.bvar 0) (natT 1)))) :
    Term Δ [.nat] .nat []).eval (5 : Nat) PUnit.unit = (6 : Nat) := rfl

/-- Filling `y` with `41` closes `addY`. -/
def add41 : Comp Δ [] (.fn .nat .nat) := addY.subst1 (natT 41)

example : (appT add41 (natT 1)).run = (42 : Nat) := rfl

/-- The fold `sumT` survives substitution under its binders. -/
example : (Term.subst1 (appT' (.bvar 0)) list123 : Term Δ [] .nat []).run = (6 : Nat) := by
  kernel_rfl

/-- `let` of a shared value and β, by the general theorems, for any argument. -/
example (a : PExpr Δ [] .nat) :
    (Comp.lam (Γ := []) (σ := .nat) (Term.ret (addT (.bvar 0) (.bvar 0)))).run a.run =
      (Term.subst1 (Term.ret (addT (.bvar 0) (.bvar 0))) a).run :=
  Comp.eval_app_lam_eq_subst1 _ _ _

example (a : PExpr Δ [] listNat) (b : Term Δ [listNat] .nat []) :
    (Term.letE (.share a) b).run = (b.subst1 a).run :=
  Term.eval_letE_share_eq_subst1 _ _ _ _

/-- Substituting into a weakened term gives the term back, for any argument. -/
example (a : PExpr Δ [] listNat) (t : Term Δ [] .nat []) :
    (Term.subst1 t.weaken a).run = t.run :=
  (Term.eval_subst1 _ a _ _).trans (Term.eval_weaken t _ _ _)

/-- `PExpr.bvar` is the variable at that position. -/
example : (PExpr.bvar 2 : PExpr Δ [.nat, listNat, .bool] .bool) = .var (.tail (.tail .head)) :=
  rfl

end TermSubstTest

end
