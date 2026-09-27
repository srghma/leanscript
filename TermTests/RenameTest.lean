module

public import LeanScript.Term.RenameEval
public import TermTests.TermTest
public meta import LeanScript.TacticElab.KernelRfl

@[expose] public section

set_option autoImplicit false

/-!
# Renaming terms (`LeanScript.Term.Rename`)

A renaming maps the variables of one context to those of another, or fails (`none`) on a
variable it drops; `Term.rename` fails exactly when a dropped variable is used.  Renaming
preserves the meaning of a term (`Term.rename_eval`).  Checked on small terms by `rfl`, and by
the general theorem for any term.

(The grammar of normal forms has no substitution: substituting a value for a variable could
create a redex, which the normaliser computes instead.)
-/

namespace RenameTest

open LeanScript TermTest

/-- Three unknowns: `n` (innermost), `b`, and `y`. -/
abbrev G3 : UCtx [0, 0] := [⟨.nat, .many, 0⟩, ⟨.bool, .many, 0⟩, ⟨.nat, .many, 0⟩]
/-- The same without `b`. -/
abbrev G2 : UCtx [0, 0] := [⟨.nat, .many, 0⟩, ⟨.nat, .many, 0⟩]

/-- `n + y`, over `n`, `b`, `y`. -/
def addNY : Term Δ 0 [] G3 .nat [] (some 0) :=
  .ret (addT (.neu (.var (.head (by decide))))
    (.neu (.var (.tail (.tail (.head (by decide)))))))

/-- `n + y`, over `n`, `y`. -/
def addNY' : Term Δ 0 [] G2 .nat [] (some 0) :=
  .ret (addT (.neu (.var (.head (by decide)))) (.neu (.var (.tail (.head (by decide))))))

/-- Drop the unused `b`. -/
def dropB : URen G3 G2 := URen.lift URen.drop _

example : addNY.rename KRen.id dropB JRen.id = some addNY' := rfl

/-- Dropping the used `n` fails. -/
example : addNY.rename KRen.id URen.drop JRen.id = none := rfl

/-- The meanings agree. -/
example : addNY'.eval PUnit.unit ((3 : Nat), (4 : Nat)) PUnit.unit =
    addNY.eval PUnit.unit ((3 : Nat), true, (4 : Nat)) PUnit.unit := rfl

/-- **Dropping an unused unknown preserves the meaning**, for every term that does not use it. -/
theorem dropB_eval {τ : Ty [0, 0]} {o : Lvl} (t : Term Δ 0 [] G3 τ [] o)
    {t' : Term Δ 0 [] G2 τ [] o} (h : t.rename KRen.id dropB JRen.id = some t')
    (n : Nat) (b : Bool) (y : Nat) :
    t'.eval PUnit.unit (n, y) PUnit.unit = t.eval PUnit.unit (n, b, y) PUnit.unit :=
  Term.rename_eval (KRen.Agree.id _)
    (URen.Agree.lift (URen.Agree.drop (Δ := Δ) (σ := .bool) (u := .many) (ℓ := 0) b
      (Tuple.cons (F := fun b : UBinder [0, 0] => Ty.Den Δ b.ty) (a := ⟨.nat, .many, 0⟩) (as := [])
        y PUnit.unit)) ⟨.nat, .many, 0⟩ n)
    (JRen.Agree.id _) t h

/-- A whole program mentions no unknown, so it renames along the empty renaming. -/
example : (sumT.rename (Γ' := []) KRen.id (URen.nil) JRen.id).isSome = true := rfl

end RenameTest

end
