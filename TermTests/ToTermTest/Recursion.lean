module

public import TermTests.ToTermTest.Data
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-!
# `#leanscript_to_term`, run: partial dispatches and recursions
-/

namespace TermTests.ToTerm

open LeanScript

/-- Running a closed term of `sig0`; see `TermTests.ToTermTest.Basic`. -/
local macro:max "run" t:term:max : term => `(Term.run (Sg := sig0) GlobalEnv.nil $t)

/-- Running a closed term of `sigAdd`. -/
local macro:max "runAdd" t:term:max : term => `(Term.run (Sg := sigAdd) envAdd $t)

/-! ## A `match` that does not name every constructor

Lean compiles a `match` whose patterns leave constructors out into a dispatch with a
default branch, and the grammar has exactly that form: `enum_casesOnWithDefault`,
`taggedUnion_casesOnWithDefault` and `recTaggedUnion_casesOnWithDefault`, which name some
of the constructors and send the rest to one default.  So the translation of such a
`match` is the partial dispatch, not the exhaustive one with the default branch copied
into every constructor it covers. -/

/-- A `match` on an enum with a wildcard: one branch, and a default. -/
def isRed (c : Colour) : Bool :=
  match c with
  | .red => true
  | _ => false

def isRed_term : Term sig0 [] 0 (tyWfOf Colour ⇒ TyWf.prim .bool) .lam :=
  #leanscript_to_term isRed

def red : Colour := .red

def red_term : Term sig0 [] 0 (tyWfOf Colour) .lit := #leanscript_to_term red

def green : Colour := .green

def green_term : Term sig0 [] 0 (tyWfOf Colour) .lit := #leanscript_to_term green

example : run isRed_term (run red_term) = true := rfl
example : run isRed_term (run green_term) = false := rfl

/-- The dispatch is the partial one: it names the constructor `red` and nothing else. -/
example : isRed_term =
    ⟨.lam (.enum_casesOnWithDefault (.var (v♯0))
      (.last ⟨0, by decide⟩ (.bool_mk true)) (.bool_mk false))⟩ := rfl

/-- A tagged union with three constructors, two of which share the wildcard's branch. -/
inductive Sized where
  | box (width height : Nat)
  | line (length : Nat)
  | point
  deriving LeanScriptTyWf

def widthOrZero (s : Sized) : Nat :=
  match s with
  | .box w _ => w
  | _ => 0

def widthOrZero_term : Term sig0 [] 0 (tyWfOf Sized ⇒ TyWf.prim .nat) .lam :=
  #leanscript_to_term widthOrZero

def aBox : Sized := .box 3 4

def aBox_term : Term sig0 [] 0 (tyWfOf Sized) .ctor := #leanscript_to_term aBox

def aPoint : Sized := .point

def aPoint_term : Term sig0 [] 0 (tyWfOf Sized) .ctor := #leanscript_to_term aPoint

example : run widthOrZero_term (run aBox_term) = 3 := rfl
example : run widthOrZero_term (run aPoint_term) = 0 := rfl

/-- A `match` that *does* name every constructor is still the exhaustive dispatch: there
    is no default branch to reach.  `colourCode` above is one, and this pins that its
    translation is `enum_casesOn`. -/
example : colourCode_term =
    ⟨.lam (.enum_casesOn (.var (v♯0)) (.three (.nat_mk 0) (.nat_mk 1) (.nat_mk 2)))⟩ := rfl

/-! ## A recursion Lean compiled through `brecOn`

A structurally recursive definition does not have to be written as `Nat.rec` or
`List.rec`: Lean compiles it into `X.brecOn`, which hands the branch the value of the
function at *every* smaller argument, and the translation reduces that history away.  It
succeeds exactly when the branch reads the value at the immediate predecessor and nothing
deeper, which is what the grammar's folds give it. -/

/-- A recursion on a `Nat`, written as a `match`. -/
def sumDown : Nat → Nat
  | 0 => 0
  | n + 1 => n + sumDown n

def sumDown_term : Term sigAdd [] 0 (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam :=
  #leanscript_to_term sumDown

example : runAdd sumDown_term 4 = 6 := rfl

/-- The fold is `nat_rec`, the same term `sumUpTo`'s `Nat.rec` translates to. -/
example : sumDown_term = sumUpTo_term := rfl

/-- A recursion whose branch does not use the recursive value is the case analysis. -/
def constDown : Nat → Nat
  | 0 => 7
  | n + 1 => constDown n

def constDown_term : Term sig0 [] 0 (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam :=
  #leanscript_to_term constDown

example : run constDown_term 5 = 7 := rfl

/-- A recursion on a list, written as a `match`: the fold `recTaggedUnion_rec`, which is
    what `sumList`'s `List.rec` translates to.  A recursive tree has no values, so the
    term is checked by its type. -/
def sumL : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumL xs

def sumL_term : Term sigAdd [] 0 (tyWfOf (List Nat) ⇒ TyWf.prim .nat) .lam :=
  #leanscript_to_term sumL

example : sumL_term = sumList_term := rfl

/-! ## A recursion that descends more than one step

`Term.nat_rec k` descends `k + 1` steps: its base values are the answers below the depth,
nearest first, and its branch is given the answers at the `k + 1` nearest predecessors.
The translation reads the depth off the compiled recursion — it is the smallest number of
steps at which the history of the `brecOn` is fully read — so a definition of this shape
is translated as it is written. -/

/-- Two steps: the branch reads the answers at `n` and at `n + 1`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

def fib_term : Term sigAdd [] 0 (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam :=
  #leanscript_to_term fib

example : runAdd fib_term 0 = 0 := rfl
example : runAdd fib_term 1 = 1 := rfl
example : runAdd fib_term 10 = 55 := rfl
example : runAdd fib_term 20 = fib 20 := rfl

/-- Three steps: the tribonacci numbers. -/
def trib : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => trib n + trib (n + 1) + trib (n + 2)

def trib_term : Term sigAdd [] 0 (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam :=
  #leanscript_to_term trib

example : runAdd trib_term 10 = trib 10 := rfl


end TermTests.ToTerm

end
