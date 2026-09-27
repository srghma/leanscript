module

public import TermTests.NestTest
public meta import LeanScript.TermElab.ToTerm
public meta import LeanScript.TacticElab.KernelRfl

@[expose] public section

set_option autoImplicit false

/-!
# The element type of a type-indexed family across modules

`NestTest.Nest.Elem` was generated in `TermTests.NestTest`; here it is imported, reused (not
generated again) by a new program, and usable as an ordinary Lean type.
-/

namespace NestImportTest

open LeanScript NestTest

-- an ordinary Lean inductive type
example : Nest.Elem Nat := .node (.leaf 1) (.leaf 2)

-- the imported program is still the current one
example : lengthT.run n3T.run = (3 : Nat) := by kernel_rfl

-- a new program reuses the imported element type, at another base
leanscript_signature Prog2 where
  nestBool := Nest Bool
  nestNat := Nest Nat

example : Prog2.ks = [0, 0, 0, 0] := rfl

def nb : Nest Bool := .cons true (.cons (false, true) .nil)
def nbT := #leanscript_to_term nb
def lengthBoolT := #leanscript_to_term Nest.length (α := Bool)
example : lengthBoolT.run nbT.run = (2 : Nat) := rfl

-- two instances of the family in the program: the index must be given
/--
error: LeanScript: `NestTest.Nest.length` is generic in the type index `α` of `NestTest.Nest`: give the index as `#leanscript_to_term NestTest.Nest.length (α := …)`
-/
#guard_msgs in
#leanscript_to_term Nest.length

end NestImportTest
