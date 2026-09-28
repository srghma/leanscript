module

import LeanScript.Ty.Syntax.Decl
import LeanScript.Term.Syntax.Common
import LeanScript.Ty.Syntax.LeanPrimTyCovariant
import NonEmpty.String.Basic
import NonEmpty.ListCorrectByConstruction.Basic
import NonEmpty.ArrayCorrectByConstruction.Basic

/-!
# Tests: the standard instances of the data types

`Inhabited`, `Repr`, `DecidableEq`, `BEq`, `ReflBEq`, `LawfulBEq`, `Hashable` (and the
`LawfulHashable` that follows) for the types of the language.
-/

open LeanScript

section
variable {ks : List Nat} {n g : Nat} {d b : Bool} {bs : List Bool}

/-- Asks for every class of the list, for a type. -/
def allStd (α : Type) [Repr α] [DecidableEq α] [BEq α] [ReflBEq α] [LawfulBEq α] [Hashable α]
    [LawfulHashable α] : Unit := ()

example : Unit := allStd LeanPrimTy
example : Unit := allStd HashableFloat
example : Unit := allStd HashableFloat32
example : Unit := allStd LeanEnumSchema
example : Unit := allStd (LeanPrimTyCovariant LeanPrimTy)
example : Unit := allStd (Ref ks)
example : Unit := allStd (BRef ks)
example : Unit := allStd (Ty ks d)
example : Unit := allStd (Fields ks)
example : Unit := allStd (Ctor ks b)
example : Unit := allStd (Ctors ks bs)
example : Unit := allStd (Fld ks n g)
example : Unit := allStd (Flds ks n g)
example : Unit := allStd (BCtor ks n g b)
example : Unit := allStd (BCtors ks n bs)
example : Unit := allStd (Alts ks n g bs)
example : Unit := allStd (Decl ks n g)
example : Unit := allStd (Mems ks n g)
example : Unit := allStd (DSig ks)
example {Γ : Ctx ks} {τ : Ty ks} : Unit := allStd (Var Γ τ)
example {cs : Ctors ks bs} {c : Ctor ks b} : Unit := allStd (CtorIx cs c)
example : Unit := allStd NonEmpty.String.NonEmptyString
example : Unit := allStd (NonEmpty.ListCorrectByConstruction.NonEmptyList Nat)
example : Unit := allStd (NonEmpty.ArrayCorrectByConstruction.NonEmptyArray Nat)

example : Inhabited (Ty ks d) := inferInstance
example : Inhabited (Ctors ks [true, false, true]) := inferInstance
example : Inhabited (Ref [3, 1]) := inferInstance
example : Inhabited (Decl ks n g) := inferInstance
example : Inhabited (Alts ks n g [true, false]) := inferInstance
example : Inhabited (BCtors ks n [false, true, true]) := inferInstance
example : Inhabited (DSig []) := inferInstance
example {Γ : Ctx ks} {τ : Ty ks} : Inhabited (Var (τ :: Γ) τ) := inferInstance
example : Inhabited NonEmpty.String.NonEmptyString := inferInstance

end

example : (default : Ty []) = .prim .bool := rfl
example : ((.head : Var (ks := []) [.nat, .bool] .nat) == .head) = true := by decide
example : ((.tail .head : Var (ks := []) [.bool, .nat, .nat] .nat) == .tail (.tail .head)) = false := by
  decide
