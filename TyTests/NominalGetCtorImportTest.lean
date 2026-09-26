module

public import TyTests.NominalGetCtorTest
public meta import LeanScript.Nominal.GetCtor

@[expose] public section

set_option autoImplicit false

/-!
# The cache across modules

The program `NominalGetCtorTest.Prog` and the definitions generated in
`TyTests.NominalGetCtorTest` are imported: the program is still the current one, and asking
for the same constructor again reuses the imported definition instead of generating a new
one.
-/

namespace NominalGetCtorImportTest

open LeanScript LeanScript.Nominal NominalGetCtorTest

/--
info: NominalGetCtorTest.Prog.Tree.node {Γ : Ctx Prog.ks} (x0 : Term Prog.Δ Γ (Ty.data (Ref.here 0).there))
  (x1 : Term Prog.Δ Γ (Ty.prim LeanPrimTy.nat ⋯)) (x2 : Term Prog.Δ Γ (Ty.data (Ref.here 0).there)) :
  Term Prog.Δ Γ (Ty.data (Ref.here 0).there)
-/
#guard_msgs in
#leanscript_get_ctor Tree.node

/--
info: TyTests.NominalGetCtorTest.Option.some.leanScriptCtor {ks : List ℕ} {Δ : DSig ks} {Γ : Ctx ks} (α : Ty ks)
  (x0 : Term Δ Γ α) : Term Δ Γ (Ty.union (Ctors.two Ctor.nullary (Ctor.fields (Fields.one α))))
-/
#guard_msgs in
#leanscript_get_ctor Option.some

-- A constructor not generated before is generated here, under this module's name.
/--
info: TyTests.NominalGetCtorImportTest.Sum.inl.leanScriptCtor {ks : List ℕ} {Δ : DSig ks} {Γ : Ctx ks} (α β : Ty ks)
  (x0 : Term Δ Γ α) : Term Δ Γ (Ty.union (Ctors.two (Ctor.fields (Fields.one α)) (Ctor.fields (Fields.one β))))
-/
#guard_msgs in
#leanscript_get_ctor Sum.inl

/-- The imported definitions compute. -/
example : treeSum ((#leanscript_get_ctor Tree.node) leaf (.lit .nat rfl 5) leaf :
    Term Prog.Δ [] _).run = 5 := rfl

end NominalGetCtorImportTest

end
