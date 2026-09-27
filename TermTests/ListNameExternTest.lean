module

public import LeanScript.Term.Eval
public import LeanScript.Term.ExternShorthands
public import LeanScript.TyElab.Notation
public meta import LeanScript.Term.Eval
public meta import LeanScript.Term.ExternShorthands
public meta import LeanScript.TermElab.ToTerm

@[expose] public section

set_option autoImplicit false

/-!
# Externs over lists and names

A Lean `List` is the type former `Ty.list` (like `Ty.array`, it denotes Lean's own `List`),
and a `Lean.Name` is the leaf `Ty.leanName` (`LeanPrimTy.leanName`).  So the entries of the
catalogue that take or answer a list or a name (`Array.toList`, `Array.mk`, `String.toList`,
`String.ofList`, `String.Internal.intercalate`, `Lean.Name.beq`, …) are ordinary calls.
-/

namespace ListNameExternTest

open LeanScript

/-- The closed programs over no datatypes. -/
abbrev P (τ : Ty []) : Type := PExpr (ks := []) .nil [] τ

/-- The types denote Lean's own `List` and `Lean.Name`. -/
example : Ty.Den DSig.nil (.list .nat) = List Nat := rfl
example : Ty.Den DSig.nil .leanName = Lean.Name := rfl

/-- The notation. -/
example : ([Ty| List Nat] : Ty []) = .list .nat := rfl
example : ([Ty| Lean.Name] : Ty []) = .leanName := rfl
example : ([Ty| Array (List Lean.Name)] : Ty []) = .array (.list .leanName) := rfl

/-- `#[1, 2].toList`. -/
def toListT : P (.list .nat) :=
  PExpr.lean_array_to_list .nat
    (PExpr.lean_array_push .nat
      (PExpr.lean_array_push .nat
        (PExpr.lean_mk_empty_array_with_capacity__Array_emptyWithCapacity .nat 2) 1) 2)

#guard id (α := List Nat) (toListT.eval ()) == [1, 2]

/-- `Array.mk #[1, 2].toList`: back to the array. -/
def mkT : P (.array .nat) := PExpr.lean_array_mk .nat toListT

#guard id (α := Array Nat) (mkT.eval ()) == #[1, 2]

/-- `String.ofList "abc".toList`. -/
def roundTripT : P .string :=
  PExpr.lean_string_mk__String_ofList (PExpr.lean_string_data__String_toList "abc")

#guard id (α := String) (roundTripT.eval ()) == "abc"

-- `"abc".toList` (and the deprecated `String.data`, the same function).
#guard id (α := List Char) ((PExpr.lean_string_data__String_toList (Δ := .nil) (Γ := []) "abc").eval ()) ==
  ['a', 'b', 'c']
#guard id (α := List Char) ((PExpr.lean_string_data__String_data (Δ := .nil) (Γ := []) "abc").eval ()) ==
  ['a', 'b', 'c']

/-- `String.Internal.intercalate ", " xs`, the list a variable. -/
def intercalateT : PExpr (ks := []) .nil [.list .string] .string :=
  PExpr.lean_string_intercalate ", " (.bvar 0)

#guard id (α := String) (intercalateT.eval ["a", "b", "c"]) == "a, b, c"

/-- `Lean.Name.beq x y`, the names variables. -/
def nameEqT : PExpr (ks := []) .nil [.leanName, .leanName] .bool :=
  PExpr.lean_name_eq (.bvar 0) (.bvar 1)

#guard id (α := Bool) (nameEqT.eval (`a.b, `a.b)) == true
#guard id (α := Bool) (nameEqT.eval (`a.b, `a.c)) == false

-- A name literal.
#guard id (α := Bool)
  ((PExpr.lean_name_eq (Δ := .nil) (Γ := []) (.lit .leanName `x) (.lit .leanName `x)).eval ()) == true

/-- info: [Ty| List Lean.Name] : Ty [] -/
#guard_msgs in #check ([Ty| List Lean.Name] : Ty [])

/-- info: [Ty| Array (List Nat)] : Ty [] -/
#guard_msgs in #check (.array (.list .nat) : Ty [])

/-! ## Translated from Lean: `#leanscript_to_term` calls the externs -/

/-- `Lean.Name.beq`: a name is a leaf. -/
def nameEq (a b : Lean.Name) : Bool := Lean.Name.beq a b
def nameEqT' := #leanscript_to_term nameEq

example : (nameEqT' (Δ := DSig.nil)).run `a.b `a.b = nameEq `a.b `a.b := rfl
example : (nameEqT' (Δ := DSig.nil)).run `a.b `a = nameEq `a.b `a := rfl

/-- `String.ofList s.toList`: the intermediate list is a `Ty.list`. -/
def roundTrip (s : String) : String := String.ofList s.toList
def roundTripT' := #leanscript_to_term roundTrip

#guard id (α := String) ((roundTripT' (Δ := DSig.nil)).run "héllo") == roundTrip "héllo"

end ListNameExternTest

end
