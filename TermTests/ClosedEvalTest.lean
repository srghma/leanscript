module

public import LeanScript.Term.Build
public import LeanScript.Term.Closed
public import LeanScript.Term.ExternShorthands

@[expose] public section

set_option autoImplicit false

/-!
# A closed `Term` is a value

`Term.eval t ρ κ : Ty.Den Δ τ` returns a Lean value, not a `Term`.  In the grammar of normal
forms every elimination needs an *open* operand (one that mentions an unknown), so a closed
statement cannot compute anything:

* a call of an extern on literals (`3 + 4`) cannot be written: `Neu.extern` needs an open
  argument.  Its value is written as a literal instead (`PExpr.externLit`);
* a branch on such a call, a `let` of a computation, a fold over a literal cannot be written
  either;
* so a closed statement is a chain of `letV`s of closed values ending in a closed answer
  (`Term.run_isValue`).

Different closed statements can still have the same value: a value can be shared by name
(`letV`) or written in place.
-/

namespace ClosedEvalTest

open LeanScript

/-- Closed statements of type `τ` over no datatypes, with no join point in scope. -/
abbrev T (τ : Ty []) : Type := Term (ks := []) .nil 0 [] [] τ [] none

/-- `3 + 4` on literals cannot be written: a call of an extern needs an open argument. -/
example : True := by
  fail_if_success
    have : Term (ks := []) .nil 0 [] [] .nat [] (some 0) := .ret (PExpr.lean_nat_add (.lit .nat 3) (.lit .nat 4))
  trivial

/-- Nor can a branch on a literal condition. -/
example : True := by
  fail_if_success
    have : Term (ks := []) .nil 0 [] [] .nat [] (some 0) :=
      .branch (.ite (Neu.lean_nat_dec_lt (.lit .nat 1) (.lit .nat 2)) (.ret (.lit .nat 10)) (.ret (.lit .nat 20)))
  trivial

/-- The value of `3 + 4`, written as a literal (computed when the term is built). -/
def addT : T .nat := .ret (PExpr.externLit .lean_nat_add (.cons (.lit .nat 3) (.cons (.lit .nat 4) .nil)))

/-- `7`. -/
def sevenT : T .nat := .ret (.lit .nat 7)

/-- They are the same term: the call was computed. -/
example : addT = sevenT := rfl

/-- A pair shared by name. -/
def pairShared : T (.record .nat (.one .nat)) :=
  .letV .one (Φ := []) (o := none) (.record_mk (.cons (.lit .nat 1) (.cons (.lit .nat 2) .nil)))
    (.ret (.kvar .head))

/-- The same pair written in place. -/
def pairInPlace : T (.record .nat (.one .nat)) :=
  .ret (.record_mk (.cons (.lit .nat 1) (.cons (.lit .nat 2) .nil)))

theorem pairShared_ne_pairInPlace : pairShared ≠ pairInPlace := by
  intro h
  cases h

theorem pairShared_run : pairShared.run = pairInPlace.run := rfl

/-- **Every closed statement is a value** (a chain of `letV`s ending in a closed answer). -/
theorem closed_isValue {τ : Ty []} (t : T τ) : t.IsValue := Term.run_isValue t

/-- `Term.run` on closed statements is not injective: sharing by name and writing in place
    have the same value. -/
theorem closed_term_run_not_injective :
    ∃ t₁ t₂ : T (.record .nat (.one .nat)), t₁ ≠ t₂ ∧ t₁.run = t₂.run :=
  ⟨pairShared, pairInPlace, pairShared_ne_pairInPlace, pairShared_run⟩

end ClosedEvalTest

end
