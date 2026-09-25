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

def green :=
  (#leanscript_ctor `Color `green :
    Term ⟨[], rfl⟩ [] _ (#leanscript_layout `Color `green) (.enumLit 1))
def pt :=
  (#leanscript_ctor `Pt (.nat_mk 1) (.nat_mk 2) :
    Term ⟨[], rfl⟩ [] _ (#leanscript_layout `Pt) .val)
def some3 :=
  (#leanscript_ctor `Option `some natT (.nat_mk 3) :
    Term ⟨[], rfl⟩ [] _ (#leanscript_layout `Option `some natT) .val)

end CtorFnModuleTest
