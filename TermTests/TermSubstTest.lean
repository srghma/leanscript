module

public import LeanScript.TermSubst
public import TermTests.TermTest

@[expose] public section

set_option autoImplicit false

/-!
# Renaming and substitution of terms (`LeanScript.TermSubst`)

Weakening and substitution on the programs of `TermTests.TermTest`, run by `rfl`, and the
general facts used on them.
-/

namespace TermSubstTest

open LeanScript TermTest

/-- `fun x => x + y`, with `y` free (index `0` of the outer context). -/
def addY : Term Δ [.nat] (.fn .nat .nat) := .lam (addT (.bvar 0) (.bvar 1))

/-- Weakening moves `addY` under a binder it does not use. -/
example : (Term.letE (natT 100) (addY.weaken.app (natT 1))).eval ((5 : Nat), PUnit.unit) =
    (6 : Nat) := rfl

/-- Filling `y` with `41` closes `addY`. -/
def add41 : Term Δ [] (.fn .nat .nat) := addY.subst1 (natT 41)

example : (Term.app add41 (natT 1)).run = (42 : Nat) := rfl

/-- The fold `sumT` survives substitution under its binders. -/
example : (Term.subst1 (Term.app sumT (.bvar 0)) list123).run = (6 : Nat) := rfl

/-- β and `let` by the general theorems, for any argument. -/
example (a : Term Δ [] .nat) :
    (Term.app (.lam (addT (.bvar 0) (.bvar 0))) a).run =
      (Term.subst1 (addT (.bvar 0) (.bvar 0)) a).run :=
  Term.eval_app_lam_eq_subst1 _ _ _

example (a : Term Δ [] listNat) (b : Term Δ [listNat] .nat) :
    (Term.letE a b).run = (b.subst1 a).run :=
  Term.eval_letE_eq_subst1 _ _ _

/-- Substituting into a weakened term gives the term back, for any argument. -/
example (a : Term Δ [] listNat) :
    (Term.subst1 (Term.app sumT.weaken (.bvar 0)) a).run = (Term.app sumT a).run :=
  (Term.eval_subst1 _ a _).trans (congrFun (Term.eval_weaken sumT _ _) _)

/-- `Term.bvar` is the variable at that position. -/
example : (Term.bvar 2 : Term Δ [.nat, listNat, .bool] .bool) = .var (.tail (.tail .head)) := rfl

end TermSubstTest

end
