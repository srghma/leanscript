module

public import TyTests.GetCtorTest
public meta import LeanScript.GenElab.GetCtor

@[expose] public section

set_option autoImplicit false

/-!
# The cache across modules

The program `GetCtorTest.Prog` and the definitions generated in
`TyTests.GetCtorTest` are imported: the program is still the current one, and asking
for the same constructor again reuses the imported definition instead of generating a new
one.
-/

namespace GetCtorImportTest

open LeanScript GetCtorTest

/--
info: GetCtorTest.Prog.Tree.node {Φ : KCtx Prog.ks} {Γ : UCtx Prog.ks} {o0 o1 o2 : Lvl}
  (x0 : PExpr Prog.Δ Φ Γ (Ty.data (Ref.here 0).there) o0) (x1 : PExpr Prog.Δ Φ Γ (Ty.prim LeanPrimTy.nat) o1)
  (x2 : PExpr Prog.Δ Φ Γ (Ty.data (Ref.here 0).there) o2) :
  PExpr Prog.Δ Φ Γ (Ty.data (Ref.here 0).there) (o0.meet (o1.meet (o2.meet none)))
-/
#guard_msgs in
#leanscript_get_ctor Tree.node

/--
info: TyTests.GetCtorTest.Option.some.leanScriptCtor {ks : List Nat} {Δ : DSig ks} {Φ : KCtx ks} {Γ : UCtx ks} (α : Ty ks)
  {o0 : Lvl} (x0 : PExpr Δ Φ Γ α o0) :
  PExpr Δ Φ Γ (Ty.union (Ctors.two Ctor.nullary (Ctor.fields (Fields.one α)))) (o0.meet none)
-/
#guard_msgs in
#leanscript_get_ctor Option.some

-- A constructor not generated before is generated here, under this module's name.
/--
info: TyTests.GetCtorImportTest.Sum.inl.leanScriptCtor {ks : List Nat} {Δ : DSig ks} {Φ : KCtx ks} {Γ : UCtx ks} (α β : Ty ks)
  {o0 : Lvl} (x0 : PExpr Δ Φ Γ α o0) :
  PExpr Δ Φ Γ (Ty.union (Ctors.two (Ctor.fields (Fields.one α)) (Ctor.fields (Fields.one β)))) (o0.meet none)
-/
#guard_msgs in
#leanscript_get_ctor Sum.inl

/-- The imported definitions compute. -/
example : treeSum ((#leanscript_get_ctor Tree.node) leaf (.lit .nat 5) leaf :
    PExpr Prog.Δ [] [] _ none).run = 5 := rfl

end GetCtorImportTest

end
