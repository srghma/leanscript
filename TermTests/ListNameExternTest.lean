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
and a `Lean.Name` is `Ty.leanName`, the list of its components (`.list Ty.nameComponent`,
denoting `List (String ⊕ Nat)`; converted by `nameToComponents` / `nameOfComponents`, as an
`Ordering` is the enum `Ty.ordering`, converted by `orderingToFin`).  So the entries of the
catalogue that take or answer a list or a name (`Array.toList`, `Array.mk`, `String.toList`,
`String.ofList`, `String.Internal.intercalate`, `Lean.Name.beq`, …) are ordinary calls.
-/

namespace ListNameExternTest

open LeanScript

/-- The closed programs over no datatypes. -/
abbrev P (τ : Ty []) : Type := PExpr (ks := []) .nil [] τ

/-- The types denote Lean's own `List`, and a name is the list of its components. -/
example : Ty.Den DSig.nil (.list .nat) = List Nat := rfl
example : Ty.Den DSig.nil .leanName = List (String ⊕ Nat) := rfl

/-- `Lean.Name` is not a leaf: it is built from `list` and `union`, like `Ty.ordering` from
    `enum`. -/
example : (Ty.leanName : Ty []) =
    .list (.union (.two (.fields (.one .string)) (.fields (.one .nat)))) := rfl

/-- A name's components, root first, and back. -/
example : nameToComponents `a.b = [.inl "a", .inl "b"] := rfl
example : nameToComponents (.num `a 3) = [.inl "a", .inr 3] := rfl
example (n : Lean.Name) : nameOfComponents (nameToComponents n) = n := by simp

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

#guard id (α := Bool) (nameEqT.eval (nameToComponents `a.b, nameToComponents `a.b)) == true
#guard id (α := Bool) (nameEqT.eval (nameToComponents `a.b, nameToComponents `a.c)) == false

/-- A component of a name, as a constructor of the union `Ty.nameComponent`. -/
def componentLit {Γ : Ctx []} : NameComponent → PExpr (ks := []) .nil Γ Ty.nameComponent
  | .inl s => .union_mk .two₁ (.cons (.lit .string s) .nil)
  | .inr n => .union_mk .two₂ (.cons (.lit .nat n) .nil)

/-- A name literal: the list of its components, from an array literal (`Array.toList`). -/
def nameLit {Γ : Ctx []} (n : Lean.Name) : PExpr (ks := []) .nil Γ .leanName :=
  PExpr.lean_array_to_list Ty.nameComponent
    (.array_mk ((nameToComponents n).foldr (fun c es => .cons (componentLit c) es) .nil))

#guard id (α := List (String ⊕ Nat)) ((nameLit (Γ := []) (.num `a.b 3)).eval ()) ==
  [.inl "a", .inl "b", .inr 3]
#guard id (α := Bool)
  ((PExpr.lean_name_eq (Δ := .nil) (Γ := []) (nameLit `x.y) (nameLit `x.y)).eval ()) == true
#guard id (α := Bool)
  ((PExpr.lean_name_eq (Δ := .nil) (Γ := []) (nameLit `x.y) (nameLit `x)).eval ()) == false

/-- info: [Ty| List Lean.Name] : Ty [] -/
#guard_msgs in #check ([Ty| List Lean.Name] : Ty [])

/-- info: [Ty| Array (List Nat)] : Ty [] -/
#guard_msgs in #check (.array (.list .nat) : Ty [])

/-! ## Translated from Lean: `#leanscript_to_term` calls the externs -/

/-- `Lean.Name.beq`: a `Lean.Name` argument is read as `Ty.leanName`, and the call is the
    extern `lean_name_eq`.  The translated term takes the components of the names. -/
def nameEq (a b : Lean.Name) : Bool := Lean.Name.beq a b
def nameEqT' := #leanscript_to_term nameEq

/-- info: ListNameExternTest.nameEqT' {ks : List Nat} {Δ : DSig ks} : Term Δ [] [Ty| Lean.Name → Lean.Name → Bool] [] -/
#guard_msgs in #check nameEqT'

example : (nameEqT' (Δ := DSig.nil)).run (nameToComponents `a.b) (nameToComponents `a.b) =
    nameEq `a.b `a.b := rfl
example : (nameEqT' (Δ := DSig.nil)).run (nameToComponents `a.b) (nameToComponents `a) =
    nameEq `a.b `a := rfl

/-- `String.ofList s.toList`: the intermediate list is a `Ty.list`. -/
def roundTrip (s : String) : String := String.ofList s.toList
def roundTripT' := #leanscript_to_term roundTrip

#guard id (α := String) ((roundTripT' (Δ := DSig.nil)).run "héllo") == roundTrip "héllo"

end ListNameExternTest

end
