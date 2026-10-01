module

public import LeanScript.Term.Build
public meta import LeanScript.TermElab.ToTerm

@[expose] public section

set_option autoImplicit false

/-!
# Polymorphic definitions

A definition generic in types is translated at one instance: every type parameter is fixed to
the stand-in `Nat` (the language has no leaf type for a type parameter), a rank-2 parameter
(`f : ∀ {α β γ : Type}, α → β → γ`) is read at the one instance at which the body uses it.  A
definition whose result has one value (`Unit`) is refused: the language is pure, so such a
function does nothing.

The definitions of `Tests/SnapshotsPBOPure/DefaultRulesFunction01.lean` are copied here (that
file is not a module of a library), and each translation is proved to compute the Lean
definition at the stand-in instance, for every argument.
-/

namespace PolymorphismTest

open LeanScript

/-! ## `DefaultRulesFunction01` -/

def F := ∀ {α β γ : Type}, α → β → γ

def test1 (f : F) (g : F) (a : Nat) : Nat :=
  f 1 <| (g "foo" a : Nat)

def test2 (f : F) (g : F) (a : Nat) : Nat :=
  (a |> g "foo" : Nat) |> f 1

def test3 (f : F) (g : F) : Nat → Nat :=
  fun _ => flip f 3 $ (flip g 2 1 : Int)

def test4 (f : F) : F :=
  fun b a => flip f a b

def test5 (α β : Type) (a : α) : β → α :=
  Function.const β a

def test6 {α : Type} : α → α :=
  flip (Function.const Nat) 42

def test1T := #leanscript_to_term test1
def test2T := #leanscript_to_term test2
def test3T := #leanscript_to_term test3
def test4T := #leanscript_to_term test4
def test5T := #leanscript_to_term test5
def test6T := #leanscript_to_term test6

/-- The rank-2 parameters of `test1` are read at their instances `@f Nat Nat Nat` and
    `@g String Nat Nat`; the translation computes `test1` on every argument. -/
theorem test1T_run (f : F) (g : F) (a : Nat) :
    (test1T (Δ := DSig.nil)).run (@f Nat Nat Nat) (@g String Nat Nat) a = test1 f g a := rfl

theorem test2T_run (f : F) (g : F) (a : Nat) :
    (test2T (Δ := DSig.nil)).run (@f Nat Nat Nat) (@g String Nat Nat) a = test2 f g a := rfl

/-- `test3` calls `g` at `Nat Nat Int` and `f` at `Int Nat Nat`; its argument is unused. -/
theorem test3T_run (f : F) (g : F) (u : Nat) :
    (test3T (Δ := DSig.nil)).run (@f Int Nat Nat) (@g Nat Nat Int) u = test3 f g u := rfl

/-- The result of `test4` is itself polymorphic (`F`): it is read at `Nat Nat Nat`, and `f` at
    the instance the body uses, `@f Nat Nat Nat`. -/
theorem test4T_run (f : F) (b : Nat) (a : Nat) :
    (test4T (Δ := DSig.nil)).run (@f Nat Nat Nat) b a =
      test4 f (α := Nat) (β := Nat) (γ := Nat) b a := rfl

theorem test5T_run (a : Nat) (b : Nat) :
    (test5T (Δ := DSig.nil)).run a b = test5 Nat Nat a b := rfl

theorem test6T_run (a : Nat) : (test6T (Δ := DSig.nil)).run a = test6 a := rfl

/-! ## More shapes -/

/-- A type parameter in a structure. -/
def swap {α β : Type} (p : α × β) : β × α := (p.2, p.1)
def swapT := #leanscript_to_term swap

theorem swapT_run (a : Nat) (b : Nat) : (swapT (Δ := DSig.nil)).run (a, b) = swap (a, b) := rfl

/-- `Option Unit` is read as `Bool` (its `Unit` field erased, `isOnePointField`): `some ()` is
    `true`. -/
def isSomeU (o : Option Unit) : Bool := o.isSome
def isSomeUT := #leanscript_to_term isSomeU

theorem isSomeUT_run (o : Option Unit) :
    (isSomeUT (Δ := DSig.nil)).run o.isSome = isSomeU o := by
  cases o <;> rfl

/-! ## `DefaultRulesMonoid01` -/

/-- `Monoid.guard` of `Tests/SnapshotsPBOPure/DefaultRulesMonoid01.lean`. -/
def guardM {M : Type} [EmptyCollection M] (b : Bool) (a : M) : M :=
  if b then a else ∅

def G := ∀ {α : Type}, α → α

/-- `∅ : Array Int` is the extern `Array.emptyWithCapacity 0` on a closed argument; its result
    is no leaf, so it is the array literal `#[]`. -/
def monoidTest1 : Bool → Array Int := flip guardM #[1, 2, 3]
/-- A rank-2 parameter: the type of the translation is the one of `f` read at its instance, `Array Int → Array Int`. -/
def monoidTest2 (f : G) : Bool → Array Int := flip guardM (f #[1, 2, 3])

def monoidTest1T := #leanscript_to_term monoidTest1
def monoidTest2T := #leanscript_to_term monoidTest2

theorem monoidTest1T_run (b : Bool) : (monoidTest1T (Δ := DSig.nil)).run b = monoidTest1 b := by
  cases b <;> rfl

theorem monoidTest2T_run (f : G) (b : Bool) :
    (monoidTest2T (Δ := DSig.nil)).run (@f (Array Int)) b = monoidTest2 f b := by
  cases b <;> rfl

/-- Other empty arrays of a closed capacity. -/
def emptyCap (b : Bool) : Array Nat := if b then #[1] else Array.emptyWithCapacity 5
def emptyCapT := #leanscript_to_term emptyCap

theorem emptyCapT_run (b : Bool) : (emptyCapT (Δ := DSig.nil)).run b = emptyCap b := by
  cases b <;> rfl

/-- A rank-2 parameter used at two different instances is refused (the language reads a
    parameter at one type). -/
def twice (f : ∀ {α : Type}, α → α) : Nat × String := (f 1, f "a")
/--
error: LeanScript: the parameter `f` of `PolymorphismTest.twice` has the polymorphic type
  {α : Type} → α → α
and is used at 2 different instances: the language reads it at one
-/
#guard_msgs in
#leanscript_to_term twice

/-- A `let` of type `Unit` is refused (the language has no type of one value). -/
def letUnit (n : Nat) : Nat := let _u : Unit := (); n
/--
error: LeanScript: the type
  PUnit
has one constructor and no field (it has one value)
-/
#guard_msgs in
#leanscript_to_term letUnit

/-! ## Results of one value

The language is pure, so a function whose result has one value always answers it and does
nothing else: it has no translation, even when it is total and terminating. -/

def unitResult (f : F) (g : F) (a : Unit) : Unit :=
  f 1 <| (g "foo" a : Unit)
/--
error: LeanScript: the result of `PolymorphismTest.unitResult` has one value: in a pure language the function always answers it and does nothing else, so it has no translation
-/
#guard_msgs in
#leanscript_to_term unitResult

def unitPairResult : Nat → Unit × PUnit := fun _ => ((), ())
/--
error: LeanScript: the result of `PolymorphismTest.unitPairResult` has one value: in a pure language the function always answers it and does nothing else, so it has no translation
-/
#guard_msgs in
#leanscript_to_term unitPairResult

end PolymorphismTest

end
