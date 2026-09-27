module

import LeanScript.Ty.LeanPrimTy
meta import HashableFloat.HashableFloat
meta import Std.Data.HashMap.Basic

/-!
# Tests: `HashableFloat`, `HashableFloat32` and the hashable `LeanPrimTy`
-/

open LeanScript

/-! ## Literals and `normalize` (settled in the kernel by `decide`) -/

example : (0.0 : HashableFloat) ≠ 1.0 := by decide
example : (1.5 : HashableFloat) = 1.5 := by decide
example : (-0.0 : HashableFloat) = 0.0 := by decide
example : (0.0 : HashableFloat) / 0.0 = 0.0 := by decide
example : (2 : HashableFloat) = 2.0 := by decide
example : HashableFloat.ofFloat? (0.0 / 0.0) = none := by decide
example : HashableFloat.ofFloat? (-0.0) = none := by decide
example : (HashableFloat.ofFloat? 2.5).isSome := by decide

example : (0.0 : HashableFloat32) ≠ 1.0 := by decide
example : (-0.0 : HashableFloat32) = 0.0 := by decide
example : HashableFloat32.ofFloat32? (0.0 / 0.0) = none := by decide

/-! ## Order -/

example : (1.0 : HashableFloat) < 2.0 := by decide
example : compare (3.0 : HashableFloat) 2.0 = .gt := by decide
example : max (3.0 : HashableFloat) 2.0 = 3.0 := by decide
example : compare (1.0 : HashableFloat32) 2.0 = .lt := by decide

/-! ## Instances -/

example : LawfulBEq HashableFloat := inferInstance
example : LawfulHashable HashableFloat := inferInstance
example : Std.TransOrd HashableFloat := inferInstance
example : Std.LawfulEqOrd HashableFloat := inferInstance
example : Std.LawfulOrderOrd HashableFloat := inferInstance
example : Std.IsLinearOrder HashableFloat := inferInstance
example : LawfulBEq HashableFloat32 := inferInstance
example : LawfulHashable HashableFloat32 := inferInstance
example : Std.TransOrd HashableFloat32 := inferInstance
example : Std.IsLinearOrder HashableFloat32 := inferInstance

example : Hashable LeanPrimTy := inferInstance
example : LawfulHashable LeanPrimTy := inferInstance

/-- The values of the float leaves are the hashable floats. -/
example : LeanPrimTy.float.denote = HashableFloat := rfl
example : LeanPrimTy.float32.denote = HashableFloat32 := rfl
example : Hashable LeanPrimTy.float.denote := inferInstance
example : LawfulHashable LeanPrimTy.float32.denote := inferInstance

/-! ## A hash map keyed by floats -/

/-- info: some "three halves" -/
#guard_msgs in
#eval ((∅ : Std.HashMap HashableFloat String).insert 1.5 "three halves").get? 1.5

/-- info: some 1 -/
#guard_msgs in
#eval ((∅ : Std.HashMap HashableFloat Nat).insert (-0.0) 1).get? 0.0
