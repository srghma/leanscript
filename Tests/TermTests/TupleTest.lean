module

public import LeanScript.Term.Build
public import LeanScript.Term.ExternShorthands

@[expose] public section

set_option autoImplicit false

/-!
# Tuples have no trailing `PUnit`

Environments, the arguments of an extern and the closures of the join points in scope are
`LeanScript.Tuple`s: `[a, b]` gives `A × B`, not `A × B × PUnit`; `[a]` gives `A`; `[]` gives
`PUnit`.
-/

namespace TupleTest

open LeanScript

example : UEnv DSig.nil [] = PUnit := rfl
example : UEnv DSig.nil [⟨.nat, .many, 0⟩] = Nat := rfl
example : UEnv DSig.nil [⟨.nat, .many, 0⟩, ⟨.bool, .one, 0⟩] = (Nat × Bool) := rfl
example : UEnv DSig.nil [⟨.nat, .many, 0⟩, ⟨.bool, .one, 0⟩, ⟨.nat, .zero, 1⟩] =
    (Nat × Bool × Nat) := rfl

example : KEnv DSig.nil [⟨.nat, .many, none, true⟩, ⟨.bool, .one, some 0, false⟩] =
    (Nat × Bool) := rfl

example : DenList (DSig.refDen DSig.nil) [.nat, .nat] = (Nat × Nat) := rfl

example : JEnv DSig.nil .nat [] = PUnit := rfl
example : JEnv DSig.nil .nat [⟨.bool, .one⟩] = (Bool → Nat) := rfl
example : JEnv DSig.nil .nat [⟨.bool, .one⟩, ⟨.nat, .many⟩] = ((Bool → Nat) × (Nat → Nat)) := rfl

/-- An extern of two arguments takes a pair. -/
def addT : Neu DSig.nil [] [⟨.nat, .many, 0⟩, ⟨.nat, .many, 0⟩] .nat 0 :=
  Neu.lean_nat_add (.neu (.var (.head (by decide)))) (.neu (.var (.tail (.head (by decide)))))

example : addT.eval PUnit.unit ((3 : Nat), (4 : Nat)) = (7 : Nat) := rfl

/-- `Tuple.cons` puts a value in front: on a non-empty tuple it is `Prod.mk`. -/
example : (Tuple.cons (F := Ty.den (DSig.refDen DSig.nil)) (a := .nat) (as := [.bool])
    (1 : Nat) true) = ((1 : Nat), true) := rfl
example : (Tuple.cons (F := Ty.den (DSig.refDen DSig.nil)) (a := .nat) (as := [])
    (1 : Nat) PUnit.unit) = (1 : Nat) := rfl

end TupleTest

end
