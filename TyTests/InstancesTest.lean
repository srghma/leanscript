/-
# Printing, mapping and the remaining coercions

Pins the `Repr` instances of the trees and the schemas, the `Functor`/`LawfulFunctor`
instances of the schemas and shapes (whose `<$>` is their `map`), and the coercions
between the schemas.
-/
import LeanScript.Ty.Ty
import LeanScript.Ty.TyBEq
import LeanScript.Ty.Wf
import LeanScript.Ty.TyWf
import LeanScript.Ty.TyWfIn
import LeanScript.Ty.WfTactic
import LeanScript.ExprCtx
import LeanScript.DeBruijn
import LeanScript.Expr.SelfField

open LeanScript

namespace InstancesTest

/-! ## `Repr` -/

/--
info: LeanScript.Ty.shape
  (LeanScript.TyShape.record
    { fst := LeanScript.Ty.shape (LeanScript.TyShape.prim (LeanScript.LeanPrimTy.nat)),
      snd := LeanScript.Ty.self,
      rest := [] })
-/
#guard_msgs in
#eval (Ty.record ⟨.prim .nat, .self, []⟩ : Ty)

/-- info: { toTy := LeanScript.Ty.shape (LeanScript.TyShape.prim (LeanScript.LeanPrimTy.bool)), isWf := _ } -/
#guard_msgs in
#eval (⟨.prim .bool, by ty_wf⟩ : TyWf)

/-- info: LeanScript.LeanFamMemberSchema.alias 3 -/
#guard_msgs in
#eval (LeanFamMemberSchema.alias 3 : LeanFamMemberSchema Nat)

/-- info: { name := "x", ty := { toTy := LeanScript.Ty.shape (LeanScript.TyShape.prim (LeanScript.LeanPrimTy.nat)), isWf := _ } } -/
#guard_msgs in
#eval (⟨"x", ⟨.prim .nat, by ty_wf⟩⟩ : GlobalDecl)

example : Repr (LeanTaggedUnionSchema Nat) := inferInstance
example : Repr (CtorsWithPayload Nat) := inferInstance
example : Repr (LeanMutualRecFamily Nat) := inferInstance
example : Repr (TyShape Nat) := inferInstance
example : Repr (TyWfIn 1) := inferInstance
example : Repr Sig := inferInstance
example : Repr (DeBruijnProj id [Ty.self] Ty.self) := inferInstance
example : Repr (SelfField []) := inferInstance

/-! ## Equality of the indexed pointers comes from their decidable equality -/

example : LawfulBEq (SelfField []) := inferInstance
example : LawfulBEq (FamilyMemberField (n := 0) 0 []) := inferInstance

/-! ## `Functor` and `LawfulFunctor` -/

example : LawfulFunctor LeanRecordSchema := inferInstance
example : LawfulFunctor CtorsWithPayload := inferInstance
example : LawfulFunctor LeanTaggedUnionSchema := inferInstance
example : LawfulFunctor LeanFamMemberSchema := inferInstance
example : LawfulFunctor LeanMutualRecFamily := inferInstance
example : LawfulFunctor LeanPrimTyCovariant := inferInstance
example : LawfulFunctor TyShape := inferInstance

example : ((· + 1) <$> (⟨1, 2, [3]⟩ : LeanRecordSchema Nat)) = ⟨2, 3, [4]⟩ := rfl
example : ((· * 2) <$> (TyShape.fn 1 2 : TyShape Nat)) = .fn 2 4 := rfl
example (s : LeanTaggedUnionSchema Nat) : id <$> s = s := id_map s

/-! ## Coercions -/

example (s : LeanRecordSchema Ty) : Ty := s
example (s : LeanTaggedUnionSchema Ty) : Ty := s
example (e : LeanEnumSchema) : Ty := e
example (c : CtorsWithPayload Nat) : LeanTaggedUnionSchema Nat := c
example (s : LeanRecordSchema Nat) : LeanFamMemberSchema Nat := s
example (s : LeanTaggedUnionSchema Nat) : LeanFamMemberSchema Nat := s
example (t : TyWf) : TyWfIn 1 := t
example (t : TyWf) : ((t : TyWfIn 1) : Ty) = t.toTy := rfl

end InstancesTest
