module

public import LeanScript.Term.Build
public meta import LeanScript.TermElab.ToTerm

@[expose] public section

set_option autoImplicit false

/-!
# Polymorphic definitions

A definition generic in types is translated at one instance: every type parameter is fixed to
the stand-in `Nat` (the language has no leaf type for a type parameter), a rank-2 parameter
(`f : ∀ {α β γ : Type}, α → β → γ`) is read at the one instance at which the body uses it, and a
definition that passes a `Unit` around is translated through its generalisation over `Unit`
(`f._leanscript_unit_gen`, `Unit` replaced by a type parameter).

The definitions of `Tests/SnapshotsPBOPure/DefaultRulesFunction01.lean` are copied here (that
file is not a module of a library), and each translation is proved to compute the Lean
definition at the stand-in instance, for every argument.
-/

namespace PolymorphismTest

open LeanScript

/-! ## `DefaultRulesFunction01` -/

def F := ∀ {α β γ : Type}, α → β → γ

def test1 (f : F) (g : F) (a : Unit) : Unit :=
  f 1 <| (g "foo" a : Unit)

def test2 (f : F) (g : F) (a : Unit) : Unit :=
  (a |> g "foo" : Unit) |> f 1

def test3 (f : F) (g : F) : Unit → Unit :=
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

/-- `test1` passes `a : Unit` to `g` and answers a `Unit`: it is translated through its
    generalisation over `Unit`, at `P := Nat`; the rank-2 parameters are read at their
    instances `@f Nat P P` and `@g String P P`.  The translation computes the generalisation
    on every argument, and `test1` is the generalisation at `P := Unit`. -/
theorem test1T_run (f : F) (g : F) (a : Nat) :
    (test1T (Δ := DSig.nil)).run (@f Nat Nat Nat) (@g String Nat Nat) a =
      test1._leanscript_unit_gen Nat f g a := rfl

theorem test1_eq_gen : test1 = test1._leanscript_unit_gen Unit := rfl

theorem test2T_run (f : F) (g : F) (a : Nat) :
    (test2T (Δ := DSig.nil)).run (@f Nat Nat Nat) (@g String Nat Nat) a =
      test2._leanscript_unit_gen Nat f g a := rfl

/-- `test3` calls `g` at `Nat Nat Int` and `f` at `Int Nat P`. -/
theorem test3T_run (f : F) (g : F) (u : Nat) :
    (test3T (Δ := DSig.nil)).run (@f Int Nat Nat) (@g Nat Nat Int) u =
      test3._leanscript_unit_gen Nat f g u := rfl

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

/-- `Option Unit` is read as `Bool` (its `Unit` field erased, `isUnitField`): `some ()` is
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
/-- A rank-2 parameter whose result is no `Unit` (no generalisation over `Unit`): the type of
    the translation is the one of `f` read at its instance, `Array Int → Array Int`. -/
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

/-- A body that builds `()` itself cannot be generalised over `Unit`: still refused. -/
def letUnit (n : Nat) : Nat := let _u : Unit := (); n
/--
error: LeanScript: the type
  PUnit
has one constructor and no field (it has one value)
-/
#guard_msgs in
#leanscript_to_term letUnit

end PolymorphismTest

end
