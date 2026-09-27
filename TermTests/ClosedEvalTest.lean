module

public import LeanScript.Term.Build
public import LeanScript.Term.ExternShorthands

@[expose] public section

set_option autoImplicit false

/-!
# `Term.eval` on a closed `Term` is not the identity

`Term.eval t ρ κ : Ty.Den Δ τ` returns a Lean value, not a `Term`.  So "`Term.eval` is the
identity on closed terms" can only mean that a closed term *is* its value: that some map
`quote : Ty.Den Δ τ → Term Δ [] τ []` recovers every closed term from its value.  That is false.
The grammar rules out β-redexes and ι-redexes (constructors taken apart). It does not rule out
computation, because a closed term can still contain

* a call of an extern on literals (`Neu.extern`, a *closed neutral*: `3 + 4`),
* a branch on such a call (`ite`), a `let` of a computation, a fold (`nat_rec`), …

and these compute.  So two different closed terms can have the same value, and `Term.run`
(`Term.eval` on the empty environment and no join points) has no left inverse.
-/

namespace ClosedEvalTest

open LeanScript

/-- Closed statements of type `τ` over no datatypes, with no join point in scope. -/
abbrev T (τ : Ty []) : Type := Term (ks := []) .nil [] τ []

/-- `3 + 4`: a closed statement whose answer is a call of an extern. -/
def addT : T .nat := .ret (PExpr.lean_nat_add 3 4)

/-- `7`: a closed statement whose answer is a literal. -/
def sevenT : T .nat := .ret (.lit .nat 7)

/-- `if 1 < 2 then 10 else 20`: a closed branch on a call of an extern. -/
def iteT : T .nat := .ite (Neu.lean_nat_dec_lt 1 2) (.ret (.lit .nat 10)) (.ret (.lit .nat 20))

/-- The two statements are different terms. -/
theorem addT_ne_sevenT : addT ≠ sevenT := by
  intro h
  cases h

/-- …with the same value. -/
theorem addT_run_eq_sevenT_run : addT.run = sevenT.run := rfl

/-- The branch is taken when the term is evaluated. -/
theorem iteT_run : iteT.run = (10 : Nat) := rfl

/-- `Term.run` on closed statements is not injective: two different closed statements
    can have the same value. -/
theorem closed_term_run_not_injective :
    ∃ t₁ t₂ : T .nat, t₁ ≠ t₂ ∧ t₁.run = t₂.run :=
  ⟨addT, sevenT, addT_ne_sevenT, addT_run_eq_sevenT_run⟩

/-- **`Term.eval` on closed statements is not the identity.** No map from values back to
    closed statements recovers every closed statement from its value (`Term.run`, which is
    `Term.eval` on the empty environment and no join points). -/
theorem closed_term_eval_not_identity :
    ¬ ∃ quote : Ty.Den (ks := []) .nil .nat → T .nat, ∀ t : T .nat, quote t.run = t := by
  rintro ⟨quote, h⟩
  apply addT_ne_sevenT
  rw [← h addT, ← h sevenT, addT_run_eq_sevenT_run]

end ClosedEvalTest

end
