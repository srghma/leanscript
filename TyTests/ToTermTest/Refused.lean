module

public import TyTests.ToTermTest.Recursion
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-!
# `#leanscript_to_term`, run: what the translation refuses
-/

namespace TyTests.ToTerm

open LeanScript

/-! ## What is refused -/

/-- A definition that is neither declared in the signature nor inlinable cannot be
    called. -/
def notDeclared (n : Nat) : Nat := n

def callsNotDeclared (n : Nat) : Nat := notDeclared n

/-- error: `#leanscript_to_term`: `TyTests.ToTerm.notDeclared` is not declared in the signature and is not inlinable, so a term cannot call it.  Either add a `GlobalDecl` named "notDeclared" (or "TyTests.ToTerm.notDeclared") to the signature, or mark `TyTests.ToTerm.notDeclared` `@[inline]`. -/
#guard_msgs (error) in
example : Term sig0 [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term callsNotDeclared

/-- A `partial` definition has no value to translate. -/
partial def loop (n : Nat) : Nat := loop n

/-- error: `#leanscript_to_term`: `TyTests.ToTerm.loop` is `partial`, and a `partial` definition has no value the grammar can express -/
#guard_msgs (error) in
example : Term sig0 [] (TyWf.prim .nat ⇒ TyWf.prim .nat) := #leanscript_to_term loop

/-- An `unsafe` definition is refused as well. -/
unsafe def unsafeId (n : Nat) : Nat := n

/-- error: `#leanscript_to_term`: `TyTests.ToTerm.unsafeId` is `unsafe` -/
#guard_msgs (error) in
example : Term sig0 [] (TyWf.prim .nat ⇒ TyWf.prim .nat) := #leanscript_to_term unsafeId

/-- An array and a list are different types, so there is no term for `Array.toList`. -/
def asList (a : Array Nat) : List Nat := a.toList

/-- error: `#leanscript_to_term`: a list and an array are different types here — `List α` is the recursive tagged union it is and `Array α` is `Ty.array` — and the grammar builds an array from all of its elements at once, so there is no term for `Array.toList` -/
#guard_msgs (error) in
example : Term sig0 [] (TyWf.array (TyWf.prim .nat) ⇒ tyWfOf (List Nat)) :=
  #leanscript_to_term asList

/-- A well-founded recursion is refused. -/
def halve (n : Nat) : Nat :=
  if n < 2 then 0 else 1 + halve (n - 2)
decreasing_by omega

/-- error: `#leanscript_to_term`: well-founded recursion (WellFounded.Nat.fix) is not supported — the only folds the translation produces are `nat_rec` and `recTaggedUnion_rec`, so write the recursion as `Nat.rec` or `List.rec` with a non-dependent motive -/
#guard_msgs (error) in
example : Term sig0 [] (TyWf.prim .nat ⇒ TyWf.prim .nat) := #leanscript_to_term halve

/-- A `partial_fixpoint` is refused: the grammar has no fixpoint that does not
    descend. -/
def spin (n : Nat) : Option Nat := spin n
partial_fixpoint

/-- error: `#leanscript_to_term`: a partial fixpoint (Lean.Order.fix) is not supported: the grammar has no fixpoint that does not descend -/
#guard_msgs (error) in
example : Term sig0 [] (TyWf.prim .nat ⇒ tyWfOf (Option Nat)) := #leanscript_to_term spin

/-! ## An existentially typed structure

The type a `Process` carries is hidden in the value, which the language has no shape
for, so `Process` has no tree — `deriving LeanScriptTyWf` refuses it — and a definition
of that type has no translation either. -/

structure Process (Out : Type) where
  State : Type
  seed : State
  step : State → Option (State × Out)

def stuck : Process Nat := ⟨Nat, 0, fun _ => none⟩

#guard_msgs (drop error) in
example : Term sig0 [] (TyWf.prim .nat) := #leanscript_to_term stuck


end TyTests.ToTerm

end
