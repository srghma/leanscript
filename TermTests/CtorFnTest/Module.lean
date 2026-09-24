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

def green : Term ⟨[], rfl⟩ [] 0 (#leanscript_layout `Color `green) .lit := #leanscript_ctor `Color `green
def pt : Term ⟨[], rfl⟩ [] 0 (#leanscript_layout `Pt) .ctor := #leanscript_ctor `Pt (.nat_mk 1) (.nat_mk 2)
def some3 : Term ⟨[], rfl⟩ [] 0 (#leanscript_layout `Option `some natT) .ctor :=
  #leanscript_ctor `Option `some natT (.nat_mk 3)

end CtorFnModuleTest
