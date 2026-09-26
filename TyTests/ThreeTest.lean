module

import LeanScript.Three

/-!
# Tests: two points are only ever `bool`

`Ty.eq_bool_of_two_points` and `Ty.den_exists_three` use no axiom beyond the standard ones
(the float leaves are settled by `decide`: `Float`/`Float32` have a decidable equality).
The three values that `Ty.threeDen` picks are computed and checked by `rfl`.
-/

open LeanScript

/--
info: 'LeanScript.Ty.eq_bool_of_two_points' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ty.eq_bool_of_two_points

/--
info: 'LeanScript.Ty.den_exists_three' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ty.den_exists_three

/--
info: 'LeanScript.Ty.den_exists_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ty.den_exists_ne

/-- `Option Bool` (three values): `none`, `some true`, `some false`. -/
example : let T := Ty.threeDen .nil (Ty.option .bool) (by decide)
    (T.x, T.y, T.z) = (none, some true, some false) := rfl

/-- `Bool × Bool`: three of its four values. -/
example : let T := Ty.threeDen .nil (Ty.pair .bool .bool) (by decide)
    (T.x, T.y, T.z) = ((true, true), (false, true), (true, false)) := rfl

/-- `Bool ⊕ Bool`. -/
example : let T := Ty.threeDen .nil (Ty.sum .bool .bool) (by decide)
    (T.x, T.y, T.z) = (.inl true, .inl false, .inr true) := rfl

/-- `Nat`. -/
example : let T := Ty.threeDen .nil (Ty.nat) (by decide)
    (T.x, T.y, T.z) = ((0 : Nat), (1 : Nat), (2 : Nat)) := rfl

/-- A declared list of naturals: the three values are told apart by the test. -/
def natList : DSig [0] :=
  .cons .nil 0 (.cons (.union (.two₁ .nullary (.fields (.cons (.old .nat) (.one (.hole 0 (by decide))))))) .nil)

example : ∃ x y z : Ty.Den natList (.data (.here 0)), x ≠ y ∧ y ≠ z ∧ x ≠ z :=
  Ty.den_exists_three natList _ (by decide)
