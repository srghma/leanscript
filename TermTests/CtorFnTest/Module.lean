module

public import LeanScript.CtorFn
public import LeanScript.Eval

@[expose] public section

open LeanScript

namespace CtorFnModuleTest

inductive Color | red | green | blue

structure Pt where
  x : Nat
  y : Nat

def natT : TyWf := .prim .nat

def green : SomeTerm ⟨[], rfl⟩ [] (#leanscript_layout `Color `green) := ⟨#leanscript_ctor `Color `green⟩
def pt : SomeTerm ⟨[], rfl⟩ [] (#leanscript_layout `Pt) := ⟨#leanscript_ctor `Pt (.nat_mk 1) (.nat_mk 2)⟩
def some3 : SomeTerm ⟨[], rfl⟩ [] (#leanscript_layout `Option `some natT) :=
  ⟨#leanscript_ctor `Option `some natT (.nat_mk 3)⟩

end CtorFnModuleTest
