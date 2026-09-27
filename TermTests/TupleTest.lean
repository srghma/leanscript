module

public import LeanScript.Term.Eval

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

example : Env DSig.nil [] = PUnit := rfl
example : Env DSig.nil [.nat] = Nat := rfl
example : Env DSig.nil [.nat, .bool] = (Nat × Bool) := rfl
example : Env DSig.nil [.nat, .bool, .nat] = (Nat × Bool × Nat) := rfl

example : DenList (DSig.refDen DSig.nil) [.nat, .nat] = (Nat × Nat) := rfl

example : JEnv DSig.nil .nat [] = PUnit := rfl
example : JEnv DSig.nil .nat [.bool] = (Bool → Nat) := rfl
example : JEnv DSig.nil .nat [.bool, .nat] = ((Bool → Nat) × (Nat → Nat)) := rfl

/-- An extern of two arguments takes a pair. -/
def addT : Comp DSig.nil [.nat, .nat] .nat :=
  .extern (σs := [.nat, .nat]) "Nat.add" (fun v => Nat.add v.1 v.2)
    (.cons (.var .head) (.cons (.var (.tail .head)) .nil))

example : addT.eval ((3 : Nat), (4 : Nat)) = (7 : Nat) := rfl

/-- `Tuple.cons` puts a value in front: on a non-empty tuple it is `Prod.mk`. -/
example : (Tuple.cons (F := Ty.den (DSig.refDen DSig.nil)) (a := .nat) (as := [.bool])
    (1 : Nat) true) = ((1 : Nat), true) := rfl
example : (Tuple.cons (F := Ty.den (DSig.refDen DSig.nil)) (a := .nat) (as := [])
    (1 : Nat) PUnit.unit) = (1 : Nat) := rfl

end TupleTest

end
