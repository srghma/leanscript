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
the value the Lean definition has.  The examples continue in
`TermTests.ToTermTest.Data` and `TermTests.ToTermTest.Recursion`, and
`TermTests.ToTermTest.Refused` pins what the translation **refuses**.
-/

namespace TermTests.ToTerm

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

def idNat_term :=
  (#leanscript_to_term idNat :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run idNat_term 7 = 7 := rfl

def constNat (a : Nat) (_b : Nat) : Nat := a

def constNat_term :=
  (#leanscript_to_term constNat :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run constNat_term 3 9 = 3 := rfl

def letExample : Nat := let x := 4; x

def letExample_term := (#leanscript_to_term letExample : Term sig0 [] _ (TyWf.prim .nat) .lit)

example : run letExample_term = 4 := rfl

def applied : Nat := (fun (f : Nat → Nat) => f 5) (fun n => n)

def applied_term := (#leanscript_to_term applied : Term sig0 [] _ (TyWf.prim .nat) .lit)

example : run applied_term = 5 := rfl

-- The translation emits already-optimized terms: the `let` of a literal is inlined, and the
-- two β-redexes of `applied` are reduced, so both translations are the bare literal — their
-- declared head is `.lit`, and a declaration stating any other head would not elaborate.
-- Their types say so, together with their grade vectors:
/-- info: TermTests.ToTerm.letExample_term : Term sig0 [] 0 (TyWf.prim LeanPrimTy.nat) Head.lit -/
#guard_msgs in #check letExample_term
/-- info: TermTests.ToTerm.applied_term : Term sig0 [] 0 (TyWf.prim LeanPrimTy.nat) Head.lit -/
#guard_msgs in #check applied_term
/--
info: TermTests.ToTerm.idNat_term :
  Term sig0 [] (Usage.single DeBruijnProj.head).tail
    ({ toTy := Ty.shape (TyShape.prim LeanPrimTy.nat), isWf := ⋯ } ⇒
      { toTy := Ty.shape (TyShape.prim LeanPrimTy.nat), isWf := ⋯ })
    Head.lam
-/
#guard_msgs in #check idNat_term

def hello : String := "hello"

def hello_term := (#leanscript_to_term hello : Term sig0 [] _ (TyWf.prim .string) .lit)

example : run hello_term = "hello" := rfl

def yes : Bool := true

def yes_term := (#leanscript_to_term yes : Term sig0 [] _ (TyWf.prim .bool) .lit)

example : run yes_term = true := rfl

def negOne : Int := -1

def negOne_term := (#leanscript_to_term negOne : Term sig0 [] _ (TyWf.prim .int) .lit)

example : run negOne_term = -1 := rfl

/-! ## A test on a `Bool` -/

def pick (b : Bool) : Nat := if b then 1 else 0

def pick_term := (#leanscript_to_term pick : Term sig0 [] _ (TyWf.prim .bool ⇒ TyWf.prim .nat) .lam)

example : run pick_term true = 1 := rfl
example : run pick_term false = 0 := rfl

/-! ## Calling a declaration of the signature

A top-level function that is not inlinable is called through the signature, by the name
it is declared under: the declaration `"double"` below is what `double` translates to.
A name is matched in full (`TermTests.ToTerm.double`) or by its last component
(`double`). -/

/-- A signature with one declaration, `double : nat ⇒ nat`. -/
def sigDouble : Sig := ⟨[⟨"double", TyWf.prim .nat ⇒ TyWf.prim .nat⟩], by decide⟩

/-- The values of the declarations of `sigDouble`. -/
def envDouble : GlobalEnv sigDouble.decls := (fun n => 2 * n, PUnit.unit)

def double (n : Nat) : Nat := 2 * n

def quadruple (n : Nat) : Nat := double (double n)

def quadruple_term :=
  (#leanscript_to_term quadruple :
    Term sigDouble [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : (Term.run envDouble quadruple_term) 3 = 12 := rfl

/-! ## Records -/

structure Point where
  x : Nat
  y : Nat
  deriving LeanScriptTyWf

def mkPoint (a : Nat) (b : Nat) : Point := ⟨a, b⟩

def mkPoint_term :=
  (#leanscript_to_term mkPoint :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ tyWfOf Point) .lam)

def fstOf (p : Point) : Nat := p.x

def fstOf_term := (#leanscript_to_term fstOf : Term sig0 [] _ (tyWfOf Point ⇒ TyWf.prim .nat) .lam)

example : run fstOf_term (run mkPoint_term 2 5) = 2 := rfl

/-! ## Tagged unions -/

def orZero (o : Option Nat) : Nat :=
  match o with
  | none => 0
  | some n => n

def orZero_term :=
  (#leanscript_to_term orZero :
    Term sig0 [] _ (tyWfOf (Option Nat) ⇒ TyWf.prim .nat) .lam)

def someThree : Option Nat := some 3

def someThree_term := (#leanscript_to_term someThree : Term sig0 [] _ (tyWfOf (Option Nat)) .ctor)

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

def colourCode_term :=
  (#leanscript_to_term colourCode :
    Term sig0 [] _ (tyWfOf Colour ⇒ TyWf.prim .nat) .lam)

def blue : Colour := .blue

def blue_term := (#leanscript_to_term blue : Term sig0 [] _ (tyWfOf Colour) .lit)

example : run colourCode_term (run blue_term) = 2 := rfl

/-! ## Arrays

`Array α` is the grammar's `TyWf.array`, whose introduction form takes every element at
once, so an array literal translates and the term runs. -/

def digits : Array Nat := #[1, 2, 3]

def digits_term := (#leanscript_to_term digits : Term sig0 [] _ (TyWf.array (TyWf.prim .nat)) .ctor)

example : run digits_term = #[1, 2, 3] := rfl

/-! ## Lists

`List α` is not `TyWf.array`: it is the recursive tagged union it is, `nil | cons α self`,
which is the tree of its `LeanScriptTyWf` instance.  So `[]` and `hd :: tl` translate to
`Term.recTaggedUnion_mk`, a `match` on a list to `Term.recTaggedUnion_casesOn` and
`List.rec` to `Term.recTaggedUnion_rec`.  Unlike an array literal, a list does not have
to be written out: `prepend` below builds one from a variable tail.

A value of a list is a W-tree of its constructors (`LeanScript.Ty.Den`), so these terms
run like any other; `Ty.DenRec.toList` reads a list back as a Lean list to compare it. -/

def digitList : List Nat := [1, 2, 3]

def digitList_term := (#leanscript_to_term digitList : Term sig0 [] _ (tyWfOf (List Nat)) .ctor)

def prepend (n : Nat) (l : List Nat) : List Nat := n :: l

def prepend_term :=
  (#leanscript_to_term prepend :
    Term sig0 [] _ (TyWf.prim .nat ⇒ tyWfOf (List Nat) ⇒ tyWfOf (List Nat)) .lam)

def firstOrZero (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | hd :: _ => hd

def firstOrZero_term :=
  (#leanscript_to_term firstOrZero :
    Term sig0 [] _ (tyWfOf (List Nat) ⇒ TyWf.prim .nat) .lam)

example : Ty.DenRec.toList (.prim .nat) (run digitList_term) = [1, 2, 3] := by decide
example : Ty.DenRec.toList (.prim .nat) (run prepend_term 7 (run digitList_term)) =
    [7, 1, 2, 3] := by decide
example : run firstOrZero_term (run digitList_term) = 1 := by decide
example : run firstOrZero_term (run prepend_term 7 (run digitList_term)) = 7 := by decide

/-- A `match` that does not recur is a case analysis: this is `nat_casesOn`. -/
def pred (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => k

def pred_term := (#leanscript_to_term pred : Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

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

def sumUpTo_term :=
  (#leanscript_to_term sumUpTo :
    Term sigAdd [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : runAdd sumUpTo_term 4 = 6 := rfl

noncomputable def sumList (l : List Nat) : Nat :=
  List.rec 0 (fun hd _tl ih => hd + ih) l

/-- The fold over a list, which is `Term.recTaggedUnion_rec`: its `cons` branch binds the
    head, the tail and the value of the fold at the tail. -/
def sumList_term :=
  (#leanscript_to_term sumList :
    Term sigAdd [] _ (tyWfOf (List Nat) ⇒ TyWf.prim .nat) .lam)

example : runAdd sumList_term (run digitList_term) = 6 := by decide

end TermTests.ToTerm

end
