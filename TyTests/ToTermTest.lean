module

public import LeanScript.Eval
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-!
# `#leanscript_to_term`, run

Every example below translates a Lean definition into a `LeanScript.Term` and, where the
term is closed, checks by `rfl` — that is, by the kernel — that the evaluator gives it
the value the Lean definition has.  The last section pins what the translation
**refuses**.
-/

namespace TyTests.ToTerm

open LeanScript

/-- The empty signature. -/
def sig0 : Sig := ⟨[], by decide⟩

/-- Running a closed term of `sig0`.  It is a macro rather than a function so that the
    term is the *whole* of its argument: `Term.run` takes the proof that the term builds
    no recursive value as a trailing argument written by `no_rec_mk`, and a function
    applied to one more argument would pass that argument as the proof. -/
local macro:max "run" t:term:max : term => `(Term.run (Sg := sig0) GlobalEnv.nil $t)

/-! ## Functions, applications, `let` and literals -/

def idNat (n : Nat) : Nat := n

def idNat_term : Term sig0 [] (TyWf.prim .nat ⇒ TyWf.prim .nat) := #leanscript_to_term idNat

example : run idNat_term 7 = 7 := rfl

def constNat (a : Nat) (_b : Nat) : Nat := a

def constNat_term : Term sig0 [] (TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term constNat

example : run constNat_term 3 9 = 3 := rfl

def letExample : Nat := let x := 4; x

def letExample_term : Term sig0 [] (TyWf.prim .nat) := #leanscript_to_term letExample

example : run letExample_term = 4 := rfl

def applied : Nat := (fun (f : Nat → Nat) => f 5) (fun n => n)

def applied_term : Term sig0 [] (TyWf.prim .nat) := #leanscript_to_term applied

example : run applied_term = 5 := rfl

def hello : String := "hello"

def hello_term : Term sig0 [] (TyWf.prim .string) := #leanscript_to_term hello

example : run hello_term = "hello" := rfl

def yes : Bool := true

def yes_term : Term sig0 [] (TyWf.prim .bool) := #leanscript_to_term yes

example : run yes_term = true := rfl

def negOne : Int := -1

def negOne_term : Term sig0 [] (TyWf.prim .int) := #leanscript_to_term negOne

example : run negOne_term = -1 := rfl

/-! ## A test on a `Bool` -/

def pick (b : Bool) : Nat := if b then 1 else 0

def pick_term : Term sig0 [] (TyWf.prim .bool ⇒ TyWf.prim .nat) := #leanscript_to_term pick

example : run pick_term true = 1 := rfl
example : run pick_term false = 0 := rfl

/-! ## Calling a declaration of the signature

A top-level function that is not inlinable is called through the signature, by the name
it is declared under: the declaration `"double"` below is what `double` translates to.
A name is matched in full (`TyTests.ToTerm.double`) or by its last component
(`double`). -/

/-- A signature with one declaration, `double : nat ⇒ nat`. -/
def sigDouble : Sig := ⟨[⟨"double", TyWf.prim .nat ⇒ TyWf.prim .nat⟩], by decide⟩

/-- The values of the declarations of `sigDouble`. -/
def envDouble : GlobalEnv sigDouble.decls := (fun n => 2 * n, PUnit.unit)

def double (n : Nat) : Nat := 2 * n

def quadruple (n : Nat) : Nat := double (double n)

def quadruple_term : Term sigDouble [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term quadruple

example : (Term.run envDouble quadruple_term) 3 = 12 := rfl

/-! ## Records -/

structure Point where
  x : Nat
  y : Nat
  deriving LeanScriptTyWf

def mkPoint (a : Nat) (b : Nat) : Point := ⟨a, b⟩

def mkPoint_term : Term sig0 [] (TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ tyWfOf Point) :=
  #leanscript_to_term mkPoint

def fstOf (p : Point) : Nat := p.x

def fstOf_term : Term sig0 [] (tyWfOf Point ⇒ TyWf.prim .nat) := #leanscript_to_term fstOf

example : run fstOf_term (run mkPoint_term 2 5) = 2 := rfl

/-! ## Tagged unions -/

def orZero (o : Option Nat) : Nat :=
  match o with
  | none => 0
  | some n => n

def orZero_term : Term sig0 [] (tyWfOf (Option Nat) ⇒ TyWf.prim .nat) :=
  #leanscript_to_term orZero

def someThree : Option Nat := some 3

def someThree_term : Term sig0 [] (tyWfOf (Option Nat)) := #leanscript_to_term someThree

example : run orZero_term (run someThree_term) = 3 := rfl

/-! ## Enums -/

inductive Colour where
  | red
  | green
  | blue
  deriving LeanScriptTyWf

def colourCode (c : Colour) : Nat :=
  match c with
  | .red => 0
  | .green => 1
  | .blue => 2

def colourCode_term : Term sig0 [] (tyWfOf Colour ⇒ TyWf.prim .nat) :=
  #leanscript_to_term colourCode

def blue : Colour := .blue

def blue_term : Term sig0 [] (tyWfOf Colour) := #leanscript_to_term blue

example : run colourCode_term (run blue_term) = 2 := rfl

/-! ## Arrays

`Array α` is the grammar's `TyWf.array`, whose introduction form takes every element at
once, so an array literal translates and the term runs. -/

def digits : Array Nat := #[1, 2, 3]

def digits_term : Term sig0 [] (TyWf.array (TyWf.prim .nat)) := #leanscript_to_term digits

example : run digits_term = [1, 2, 3] := rfl

/-! ## Lists

`List α` is not `TyWf.array`: it is the recursive tagged union it is, `nil | cons α self`,
which is the tree of its `LeanScriptTyWf` instance.  So `[]` and `hd :: tl` translate to
`Term.recTaggedUnion_mk`, a `match` on a list to `Term.recTaggedUnion_casesOn` and
`List.rec` to `Term.recTaggedUnion_rec`.  Unlike an array literal, a list does not have
to be written out: `prepend` below builds one from a variable tail.

`Ty.Den` gives a recursive tree no values, so these terms are outside the fragment the
evaluator interprets (`Term.NoRecMk`) and cannot be run; each one is checked by its type
instead, which is what says the translation is well typed. -/

def digitList : List Nat := [1, 2, 3]

def digitList_term : Term sig0 [] (tyWfOf (List Nat)) := #leanscript_to_term digitList

def prepend (n : Nat) (l : List Nat) : List Nat := n :: l

def prepend_term :
    Term sig0 [] (TyWf.prim .nat ⇒ tyWfOf (List Nat) ⇒ tyWfOf (List Nat)) :=
  #leanscript_to_term prepend

def firstOrZero (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | hd :: _ => hd

def firstOrZero_term : Term sig0 [] (tyWfOf (List Nat) ⇒ TyWf.prim .nat) :=
  #leanscript_to_term firstOrZero

/-- A `match` that does not recur is a case analysis: this is `nat_casesOn`. -/
def pred (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => k

def pred_term : Term sig0 [] (TyWf.prim .nat ⇒ TyWf.prim .nat) := #leanscript_to_term pred

example : run pred_term 5 = 4 := rfl
example : run pred_term 0 = 0 := rfl

/-! ## The two folds

A recursion is written as `Nat.rec` or `List.rec` with a non-dependent motive: those are
the grammar's `nat_rec` and `recTaggedUnion_rec`.  Addition is not an operation of the
grammar, so `Nat.add` is called through the signature, under the name `"add"`. -/

/-- A signature with one declaration, `add : nat ⇒ nat ⇒ nat`. -/
def sigAdd : Sig := ⟨[⟨"add", TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat⟩], by decide⟩

/-- The values of the declarations of `sigAdd`. -/
def envAdd : GlobalEnv sigAdd.decls := (Nat.add, PUnit.unit)

/-- Running a closed term of `sigAdd`. -/
local macro:max "runAdd" t:term:max : term => `(Term.run (Sg := sigAdd) envAdd $t)

noncomputable def sumUpTo (n : Nat) : Nat := Nat.rec 0 (fun k ih => k + ih) n

def sumUpTo_term : Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term sumUpTo

example : runAdd sumUpTo_term 4 = 6 := rfl

noncomputable def sumList (l : List Nat) : Nat :=
  List.rec 0 (fun hd _tl ih => hd + ih) l

/-- The fold over a list, which is `Term.recTaggedUnion_rec`: its `cons` branch binds the
    head, the tail and the value of the fold at the tail.  A recursive tree has no
    values, so this term is not one the evaluator runs. -/
def sumList_term : Term sigAdd [] (tyWfOf (List Nat) ⇒ TyWf.prim .nat) :=
  #leanscript_to_term sumList

/-! ## The cache

`twiceA` and `twiceB` are different definitions of the same shape, so the second one is
not stored twice: it is merged into the tree of the first. -/

#leanscript_to_term_cache_clear

@[inline] def twiceA (n : Nat) : Nat := n + n

@[inline] def twiceB (m : Nat) : Nat := m + m

def usesA : Nat := twiceA 2

def usesB : Nat := twiceB 2

def usesAagain : Nat := twiceA 5

def usesA_term : Term sigAdd [] (TyWf.prim .nat) := #leanscript_to_term usesA

/-- `twiceB` has the shape of `twiceA`, which is translated already. -/
def usesB_term : Term sigAdd [] (TyWf.prim .nat) := #leanscript_to_term usesB

/-- `twiceA` is translated already: this is a plain cache hit. -/
def usesAagain_term : Term sigAdd [] (TyWf.prim .nat) := #leanscript_to_term usesAagain

example : runAdd usesA_term = 4 := rfl
example : runAdd usesB_term = 4 := rfl
example : runAdd usesAagain_term = 10 := rfl

-- Five definitions were translated (`usesA`, `twiceA`, `usesB`, `twiceB`, `usesAagain`;
-- `Nat.add` is a signature global, not a translation), `twiceB` turned out to have the
-- shape of `twiceA` and was merged into its tree, and the two later uses were found in
-- the cache.
/-- info: entries: 5, hits: 2, shape merges: 1 -/
#guard_msgs (info) in
#leanscript_to_term_cache_stats

/-! ## A user-defined tagged union, a pair and a thunk -/

inductive Shape where
  | circle (radius : Nat)
  | rect (width height : Nat)
  deriving LeanScriptTyWf

def widthOf (s : Shape) : Nat :=
  match s with
  | .circle r => r
  | .rect w _ => w

def widthOf_term : Term sig0 [] (tyWfOf Shape ⇒ TyWf.prim .nat) :=
  #leanscript_to_term widthOf

def aRect : Shape := .rect 3 4

def aRect_term : Term sig0 [] (tyWfOf Shape) := #leanscript_to_term aRect

example : run widthOf_term (run aRect_term) = 3 := rfl

def swap (p : Nat × Bool) : Bool × Nat := (p.2, p.1)

def swap_term : Term sig0 [] (tyWfOf (Nat × Bool) ⇒ tyWfOf (Bool × Nat)) :=
  #leanscript_to_term swap

def aPair : Nat × Bool := (7, true)

def aPair_term : Term sig0 [] (tyWfOf (Nat × Bool)) := #leanscript_to_term aPair

example : (run swap_term (run aPair_term)).1 = true := rfl
example : (run swap_term (run aPair_term)).2.1 = (7 : Nat) := rfl

@[inline] def delayed : Thunk Nat := Thunk.mk (fun _ => 6)

def delayed_term : Term sig0 [] (TyWf.thunk (TyWf.prim .nat)) := #leanscript_to_term delayed

def forced : Nat := delayed.get

def forced_term : Term sig0 [] (TyWf.prim .nat) := #leanscript_to_term forced

example : run forced_term = 6 := rfl

/-! ## The type of the translation, inferred

With `(sig := …)` the signature does not have to be read off the expected type, so the
translation can be written with no type ascription at all. -/

def inferred_term := #leanscript_to_term (sig := sigAdd) sumUpTo

example : runAdd inferred_term 4 = 6 := rfl

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

def isRed_term : Term sig0 [] (tyWfOf Colour ⇒ TyWf.prim .bool) :=
  #leanscript_to_term isRed

def red : Colour := .red

def red_term : Term sig0 [] (tyWfOf Colour) := #leanscript_to_term red

def green : Colour := .green

def green_term : Term sig0 [] (tyWfOf Colour) := #leanscript_to_term green

example : run isRed_term (run red_term) = true := rfl
example : run isRed_term (run green_term) = false := rfl

/-- The dispatch is the partial one: it names the constructor `red` and nothing else. -/
example : isRed_term =
    .lam (.enum_casesOnWithDefault (.var (v♯0))
      (.last ⟨0, by decide⟩ (.bool_mk true)) (.bool_mk false)) := rfl

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

def widthOrZero_term : Term sig0 [] (tyWfOf Sized ⇒ TyWf.prim .nat) :=
  #leanscript_to_term widthOrZero

def aBox : Sized := .box 3 4

def aBox_term : Term sig0 [] (tyWfOf Sized) := #leanscript_to_term aBox

def aPoint : Sized := .point

def aPoint_term : Term sig0 [] (tyWfOf Sized) := #leanscript_to_term aPoint

example : run widthOrZero_term (run aBox_term) = 3 := rfl
example : run widthOrZero_term (run aPoint_term) = 0 := rfl

/-- A `match` that *does* name every constructor is still the exhaustive dispatch: there
    is no default branch to reach.  `colourCode` above is one, and this pins that its
    translation is `enum_casesOn`. -/
example : colourCode_term =
    .lam (.enum_casesOn (.var (v♯0)) (.three (.nat_mk 0) (.nat_mk 1) (.nat_mk 2))) := rfl

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

def sumDown_term : Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term sumDown

example : runAdd sumDown_term 4 = 6 := rfl

/-- The fold is `nat_rec`, the same term `sumUpTo`'s `Nat.rec` translates to. -/
example : sumDown_term = sumUpTo_term := rfl

/-- A recursion whose branch does not use the recursive value is the case analysis. -/
def constDown : Nat → Nat
  | 0 => 7
  | n + 1 => constDown n

def constDown_term : Term sig0 [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term constDown

example : run constDown_term 5 = 7 := rfl

/-- A recursion on a list, written as a `match`: the fold `recTaggedUnion_rec`, which is
    what `sumList`'s `List.rec` translates to.  A recursive tree has no values, so the
    term is checked by its type. -/
def sumL : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumL xs

def sumL_term : Term sigAdd [] (tyWfOf (List Nat) ⇒ TyWf.prim .nat) :=
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

def fib_term : Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
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

def trib_term : Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term trib

example : runAdd trib_term 10 = trib 10 := rfl

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
