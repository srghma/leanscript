import TyTests.CtorFnTest.Module
open LeanScript CtorFnModuleTest
example : Term.run (Sg := ⟨[], rfl⟩) PUnit.unit pt = (1, 2, ()) := rfl
def some4 : Term ⟨[], rfl⟩ [] (#leanscript_layout `Option `some natT) :=
  #leanscript_ctor `Option `some natT (.nat_mk 4)
#print some4
