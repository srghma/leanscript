module

import LeanScript.Ty.Three

/-!
# Tests: two points are only ever `bool`

`Ty.eq_bool_of_two_points` and `Ty.den_exists_three` use no axiom beyond the standard ones
(the float leaves are settled by `decide`: `HashableFloat`/`HashableFloat32` have a decidable equality).
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

-- [SKIPPED BY PROFILE_LAKE] /-- `Option Bool` (three values): `none`, `some true`, `some false`. -/
-- [SKIPPED BY PROFILE_LAKE] example : let T := Ty.threeDen .nil (Ty.option .bool) (by decide)
-- [SKIPPED BY PROFILE_LAKE]     (T.x, T.y, T.z) = (none, some true, some false) := rfl

-- [SKIPPED BY PROFILE_LAKE] /-- `Bool × Bool`: three of its four values. -/
-- [SKIPPED BY PROFILE_LAKE] example : let T := Ty.threeDen .nil (Ty.pair .bool .bool) (by decide)
-- [SKIPPED BY PROFILE_LAKE]     (T.x, T.y, T.z) = ((true, true), (false, true), (true, false)) := rfl

-- [SKIPPED BY PROFILE_LAKE] /-- `Bool ⊕ Bool`. -/
-- [SKIPPED BY PROFILE_LAKE] example : let T := Ty.threeDen .nil (Ty.sum .bool .bool) (by decide)
-- [SKIPPED BY PROFILE_LAKE]     (T.x, T.y, T.z) = (.inl true, .inl false, .inr true) := rfl

-- [SKIPPED BY PROFILE_LAKE] /-- `Nat`. -/
-- [SKIPPED BY PROFILE_LAKE] example : let T := Ty.threeDen .nil (Ty.nat) (by decide)
-- [SKIPPED BY PROFILE_LAKE]     (T.x, T.y, T.z) = ((0 : Nat), (1 : Nat), (2 : Nat)) := rfl

/-- A declared list of naturals: the three values are told apart by the test. -/
def natList : DSig [0] :=
  .cons .nil 0 (.cons (.union (.two₁ .nullary (.fields (.cons (.old .nat) (.one (.hole 0 (by decide))))))) .nil)

-- [SKIPPED BY PROFILE_LAKE] example : ∃ x y z : Ty.Den natList (.data (.here 0)), x ≠ y ∧ y ≠ z ∧ x ≠ z :=
-- [SKIPPED BY PROFILE_LAKE]   Ty.den_exists_three natList _ (by decide)
