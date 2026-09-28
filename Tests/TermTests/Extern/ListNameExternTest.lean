module

public import LeanScript.Term.Build
public import LeanScript.Term.Extern.Shorthands
public import LeanScript.TyElab.Notation
public meta import LeanScript.Term.Semantics.Eval
public meta import LeanScript.Term.Extern.Shorthands
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

/-- Pure expressions over no datatypes, with the unknowns `Γ` (a call of an extern has an
    open argument). -/
abbrev P (Γ : UCtx []) (τ : Ty []) : Type := PExpr (ks := []) .nil [] Γ τ (some 0)

/-- The innermost unknown. -/
abbrev x0 {τ : Ty []} {Γ : UCtx []} : PExpr (ks := []) .nil [] (⟨τ, .many, 0⟩ :: Γ) τ (some 0) :=
  .neu (.var (.head (by decide)))

/-- The unknown one binder further out. -/
abbrev x1 {τ : Ty []} {Γ : UCtx []} {b : UBinder []} :
    PExpr (ks := []) .nil [] (b :: ⟨τ, .many, 0⟩ :: Γ) τ (some 0) :=
  .neu (.var (.tail (.head (by decide))))

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

/-- `#[n, 2].toList`, `n` an unknown. -/
def toListT : P [⟨.nat, .many, 0⟩] (.list .nat) :=
  PExpr.lean_array_to_list .nat
    (PExpr.lean_array_push .nat (PExpr.lean_array_push .nat (.array_mk .nil) x0) (.lit .nat 2))

#guard id (α := List Nat) (toListT.eval PUnit.unit (1 : Nat)) == [1, 2]

/-- `Array.mk #[n, 2].toList`: back to the array. -/
def mkT : P [⟨.nat, .many, 0⟩] (.array .nat) := PExpr.lean_array_mk .nat toListT

#guard id (α := Array Nat) (mkT.eval PUnit.unit (1 : Nat)) == #[1, 2]

/-- `String.ofList s.toList`. -/
def roundTripT : P [⟨.string, .many, 0⟩] .string :=
  PExpr.lean_string_mk__String_ofList (PExpr.lean_string_data__String_toList x0)

#guard id (α := String) (roundTripT.eval PUnit.unit ("abc" : String)) == "abc"

-- `s.toList` (and the deprecated `String.data`, the same function).
#guard id (α := List Char) ((PExpr.lean_string_data__String_toList (Δ := .nil) (Φ := [])
  (Γ := [⟨.string, .many, 0⟩]) x0).eval PUnit.unit ("abc" : String)) == ['a', 'b', 'c']
#guard id (α := List Char) ((PExpr.lean_string_data__String_data (Δ := .nil) (Φ := [])
  (Γ := [⟨.string, .many, 0⟩]) x0).eval PUnit.unit ("abc" : String)) == ['a', 'b', 'c']

/-- `String.Internal.intercalate ", " xs`, the list an unknown. -/
def intercalateT : P [⟨.list .string, .many, 0⟩] .string :=
  PExpr.lean_string_intercalate (.lit .string ", ") x0

#guard id (α := String) (intercalateT.eval PUnit.unit ["a", "b", "c"]) == "a, b, c"

/-- `Lean.Name.beq x y`, the names unknowns. -/
def nameEqT : P [⟨.leanName, .many, 0⟩, ⟨.leanName, .many, 0⟩] .bool :=
  PExpr.lean_name_eq x0 x1

#guard id (α := Bool) (nameEqT.eval PUnit.unit (nameToComponents `a.b, nameToComponents `a.b)) == true
#guard id (α := Bool) (nameEqT.eval PUnit.unit (nameToComponents `a.b, nameToComponents `a.c)) == false

/-- A component of a name, as a constructor of the union `Ty.nameComponent`. -/
def componentLit {Φ : KCtx []} {Γ : UCtx []} :
    NameComponent → PExpr (ks := []) .nil Φ Γ Ty.nameComponent none
  | .inl s => .union_mk .two₁ (.cons (.lit .string s) .nil)
  | .inr n => .union_mk .two₂ (.cons (.lit .nat n) .nil)

/-- The components of a name, as elements of a literal. -/
def componentElems {Φ : KCtx []} {Γ : UCtx []} :
    List NameComponent → Elems (ks := []) .nil Φ Γ Ty.nameComponent none
  | [] => .nil
  | c :: cs => .cons (componentLit c) (componentElems cs)

/-- A name literal: the list literal of its components. -/
def nameLit {Φ : KCtx []} {Γ : UCtx []} (n : Lean.Name) : PExpr (ks := []) .nil Φ Γ .leanName none :=
  .list_mk (componentElems (nameToComponents n))

#guard id (α := List (String ⊕ Nat)) ((nameLit (Φ := []) (Γ := []) (.num `a.b 3)).run) ==
  [.inl "a", .inl "b", .inr 3]
#guard id (α := Bool) ((PExpr.lean_name_eq (Δ := .nil) (Φ := []) (Γ := [⟨.leanName, .many, 0⟩])
  x0 (nameLit `x.y)).eval PUnit.unit (nameToComponents `x.y)) == true
#guard id (α := Bool) ((PExpr.lean_name_eq (Δ := .nil) (Φ := []) (Γ := [⟨.leanName, .many, 0⟩])
  x0 (nameLit `x.y)).eval PUnit.unit (nameToComponents `x)) == false

/-- info: [Ty| List Lean.Name] : Ty [] -/
#guard_msgs in #check ([Ty| List Lean.Name] : Ty [])

/-- info: [Ty| Array (List Nat)] : Ty [] -/
#guard_msgs in #check (.array (.list .nat) : Ty [])

/-! ## Translated from Lean: `#leanscript_to_term` calls the externs -/

/-- `Lean.Name.beq`: a `Lean.Name` argument is read as `Ty.leanName`, and the call is the
    extern `lean_name_eq`.  The translated term takes the components of the names. -/
def nameEq (a b : Lean.Name) : Bool := Lean.Name.beq a b
def nameEqT' := #leanscript_to_term nameEq

/--
info: ListNameExternTest.nameEqT' {ks : List Nat} {Δ : DSig ks} : Term Δ 0 [] [] [Ty| Lean.Name → Lean.Name → Bool] [] none
-/
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
