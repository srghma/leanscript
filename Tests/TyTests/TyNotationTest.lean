module

public import LeanScript.TyElab.Notation

@[expose] public section

set_option autoImplicit false

/-!
# The `[Ty| …]` notation (`LeanScript.TyElab.Notation`)

What each surface form elaborates to (checked by `rfl`), how types are printed back
(`#guard_msgs`), and the forms that are refused.
-/

namespace TyNotationTest

open LeanScript

/-! ## Elaboration -/

-- [SKIPPED BY PROFILE_LAKE] example : ([Ty| Nat] : Ty []) = .nat := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Ty| UInt8] : Ty []) = .prim .uint8 := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Ty| Float.Model] : Ty []) = .prim .floatModel := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Ty| BitVec 32] : Ty []) = .prim (.bitvec 32) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Ty| String.Pos "ab"] : Ty []) = .prim (.stringPos "ab") := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Ty| Nat → Bool → String] : Ty []) = .fn .nat (.fn .bool .string) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Ty| (Nat → Bool) → String] : Ty []) = .fn (.fn .nat .bool) .string := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Ty| Array (Array Int)] : Ty []) = .array (.array .int) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Ty| Option Nat] : Ty []) = .union (.two .nullary (.fields (.one .nat))) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Ty| Nat ⊕ Bool] : Ty []) = .union (.two (.fields (.one .nat)) (.fields (.one .bool))) :=
-- [SKIPPED BY PROFILE_LAKE]   rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Ty| Enum 3] : Ty []) = .enum {} := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Ty| Enum 3 -1] : Ty []) = .enum { shift := -1 } := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Ty| Enum 5 2] : Ty []) = .enum { extraConstructors := 2, shift := 2 } := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Ty| Enum ‹{ extraConstructors := 1 }›] : Ty []) = .enum { extraConstructors := 1 } := rfl

-- [SKIPPED BY PROFILE_LAKE] /-- A chain of `×` is one record; parentheses make a field that is a record. -/
-- [SKIPPED BY PROFILE_LAKE] example : ([Ty| Nat × Int × String] : Ty []) = .record .nat (.cons .int (.one .string)) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Ty| Nat × (Int × String)] : Ty []) =
-- [SKIPPED BY PROFILE_LAKE]     .record .nat (.one (.record .int (.one .string))) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Ty| (Nat × Int) × String] : Ty []) =
-- [SKIPPED BY PROFILE_LAKE]     .record (.record .nat (.one .int)) (.one .string) := rfl

-- [SKIPPED BY PROFILE_LAKE] /-- A union: `·` is a constructor without fields, commas separate the fields of one. -/
-- [SKIPPED BY PROFILE_LAKE] example : ([Ty| ⟪· | Nat, Data 0 0⟫] : Ty [0]) =
-- [SKIPPED BY PROFILE_LAKE]     .union (.two .nullary (.fields (.cons .nat (.one (.data (.here 0)))))) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Ty| ⟪Nat | · | Bool × Int, String⟫] : Ty []) =
-- [SKIPPED BY PROFILE_LAKE]     .union (.cons (.fields (.one .nat)) (.two .nullary
-- [SKIPPED BY PROFILE_LAKE]       (.fields (.cons (.record .bool (.one .int)) (.one .string))))) := rfl

-- [SKIPPED BY PROFILE_LAKE] /-- Declared datatypes: member `j` of block `b` (`0` is the newest block). -/
-- [SKIPPED BY PROFILE_LAKE] example : ([Ty| Data 0 1] : Ty [2, 0]) = .data (.here 1) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Ty| Data 1 0] : Ty [2, 0]) = .data (.there (.here 0)) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Ty| Data ‹.there (.here 0)›] : Ty [2, 0]) = .data (.there (.here 0)) := rfl

/-- A Lean term is always written `‹t›`, even a single name. -/
abbrev listNat : Ty [0] := [Ty| Data 0 0]
-- [SKIPPED BY PROFILE_LAKE] example : ([Ty| Array ‹listNat›] : Ty [0]) = .array (.data (.here 0)) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Ty| ‹Ty.option .nat› → Nat] : Ty []) = .fn (Ty.option .nat) .nat := rfl
-- [SKIPPED BY PROFILE_LAKE] example (t : Ty []) : [Ty| ‹t› × ‹t›] = .record t (.one t) := rfl

/-! ## Printing -/

/-- info: [Ty| Nat → Option Bool] : Ty [] -/
#guard_msgs in #check (Ty.fn .nat (Ty.option .bool) : Ty [])

/-- info: [Ty| (Nat → Nat) → Array (Nat × Int) → Nat] : Ty [] -/
#guard_msgs in #check ([Ty| (Nat → Nat) → Array (Nat × Int) → Nat] : Ty [])

/-- info: [Ty| Nat × (Int × String)] : Ty [] -/
#guard_msgs in #check (Ty.record .nat (.one (.record .int (.one .string))) : Ty [])

/-- info: [Ty| (Nat × Int) × String] : Ty [] -/
#guard_msgs in #check ([Ty| (Nat × Int) × String] : Ty [])

/-- info: [Ty| ⟪· | Nat | · | Bool, ‹listNat›⟫] : Ty [0] -/
#guard_msgs in #check ([Ty| ⟪· | Nat | · | Bool, ‹listNat›⟫] : Ty [0])

/-- info: [Ty| Array (BitVec 8) ⊕ String.Pos "ab" ⊕ Enum 4 -1] : Ty [] -/
#guard_msgs in #check ([Ty| Array (BitVec 8) ⊕ String.Pos "ab" ⊕ Enum 4 -1] : Ty [])

/-- info: [Ty| (Nat ⊕ Int) ⊕ Enum 3] : Ty [] -/
#guard_msgs in #check (Ty.sum (Ty.sum .nat .int) (.enum {}) : Ty [])

/-- info: [Ty| Data 1 2] : Ty [0, 3] -/
#guard_msgs in #check (Ty.data (.there (.here 2)) : Ty [0, 3])

-- A subterm outside the notation is printed as `‹t›`, even a single name.
/-- info: [Ty| Option ‹Ty.map id listNat›] : Ty [0] -/
#guard_msgs in #check Ty.option (Ty.map id listNat)

/-- info: fun t => [Ty| ‹t› → Option ‹t›] : Ty [] → Ty [] -/
#guard_msgs in #check fun (t : Ty []) => [Ty| ‹t› → Option ‹t›]

-- The notation can be turned off.
/-- info: Ty.nat.fn Ty.bool.option : Ty [] -/
#guard_msgs in set_option pp.leanscript false in #check ([Ty| Nat → Option Bool] : Ty [])

/-! ## Refused forms -/

/-- error: an enum has at least three constructors (two field-less constructors are `Bool`) -/
#guard_msgs in example : Ty [] := [Ty| Enum 2]

/--
error: unknown type former `Set` with 1 argument(s): expected `Array τ`, `List τ`, `Thunk τ`, `Option τ`, `BitVec n`, `String.Pos s`, `Enum n`, `Enum n k` or `Data b j`
-/
#guard_msgs in example : Ty [] := [Ty| Set Nat]

/-- error: unknown leaf `listNat`: a Lean term is written `‹listNat›` -/
#guard_msgs in example : Ty [0] := [Ty| Array listNat]

-- A union needs a constructor with fields (`UnionShape`).
/--
error: failed to synthesize instance of type class
  UnionShape [false, false]

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in example : Ty [] := [Ty| ⟪· | ·⟫]

end TyNotationTest

end
