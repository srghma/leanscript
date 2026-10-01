module

public import LeanScript.Term.Build
public meta import LeanScript.TermElab.ToTerm

@[expose] public section

set_option autoImplicit false

/-!
# Polymorphic definitions

A definition generic in types is translated at one instance: every type parameter is fixed to
its stand-in `LeanScript.TyParam i` (the leaf `LeanPrimTy.tyParam i`), a rank-2 parameter
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

/-- `TyParam 0`, the stand-in for the first type parameter. -/
abbrev P0 := TyParam 0
/-- `TyParam 1`. -/
abbrev P1 := TyParam 1
/-- `TyParam 2`. -/
abbrev P2 := TyParam 2

/-- `test1` passes `a : Unit` to `g` and answers a `Unit`: it is translated through its
    generalisation over `Unit`, at `P := TyParam 0`; the rank-2 parameters are read at their
    instances `@f Nat P P` and `@g String P P`.  The translation computes the generalisation
    on every argument, and `test1` is the generalisation at `P := Unit`. -/
theorem test1T_run (f : F) (g : F) (a : P0) :
    (test1T (Δ := DSig.nil)).run (@f Nat P0 P0) (@g String P0 P0) a =
      test1._leanscript_unit_gen P0 f g a := rfl

theorem test1_eq_gen : test1 = test1._leanscript_unit_gen Unit := rfl

theorem test2T_run (f : F) (g : F) (a : P0) :
    (test2T (Δ := DSig.nil)).run (@f Nat P0 P0) (@g String P0 P0) a =
      test2._leanscript_unit_gen P0 f g a := rfl

/-- `test3` calls `g` at `Nat Nat Int` and `f` at `Int Nat P`. -/
theorem test3T_run (f : F) (g : F) (u : P0) :
    (test3T (Δ := DSig.nil)).run (@f Int Nat P0) (@g Nat Nat Int) u =
      test3._leanscript_unit_gen P0 f g u := rfl

/-- The result of `test4` is itself polymorphic (`F`): it is read at `P0 P1 P2`, and `f` at the
    instance the body uses, `@f P0 P1 P2`. -/
theorem test4T_run (f : F) (b : P0) (a : P1) :
    (test4T (Δ := DSig.nil)).run (@f P0 P1 P2) b a = test4 f (α := P0) (β := P1) (γ := P2) b a :=
  rfl

theorem test5T_run (a : P0) (b : P1) : (test5T (Δ := DSig.nil)).run a b = test5 P0 P1 a b := rfl

theorem test6T_run (a : P0) : (test6T (Δ := DSig.nil)).run a = test6 a := rfl

/-! ## More shapes -/

/-- A type parameter in a structure. -/
def swap {α β : Type} (p : α × β) : β × α := (p.2, p.1)
def swapT := #leanscript_to_term swap

theorem swapT_run (a : P0) (b : P1) : (swapT (Δ := DSig.nil)).run (a, b) = swap (a, b) := rfl

/-- `Option Unit` is read as `Bool` (its `Unit` field erased, `isUnitField`): `some ()` is
    `true`. -/
def isSomeU (o : Option Unit) : Bool := o.isSome
def isSomeUT := #leanscript_to_term isSomeU

theorem isSomeUT_run (o : Option Unit) :
    (isSomeUT (Δ := DSig.nil)).run o.isSome = isSomeU o := by
  cases o <;> rfl

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
