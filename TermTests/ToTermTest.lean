module

public import LeanScript.Eval
public meta import LeanScript.ToTerm

@[expose] public section

set_option autoImplicit false

/-!
# `#leanscript_to_term`

Lean definitions translated to `LeanScript.Term`, and the translations run by `Term.eval`
against the Lean definitions (by `rfl`).  Non-recursive definitions, `if`, `match` on
`Option`, an enum, `Bool` and a structure, projections, `let`, structural recursion on `Nat`
(`nat_rec`), on `List Nat` and on a binary tree (`data_rec`), a map that builds a list
(`data_in` through `#leanscript_get_ctor`), and course-of-values recursion (`data_brec`).
Then the refusals: every unit-like type (`Unit` as a parameter, `Option Unit`, a `let` of
`()`), `Thunk Bool` (a second type of two values), an extern on a non-leaf value, a non-structural recursive call, a type parameter.
-/

namespace ToTermTest

open LeanScript

def add3 (a b c : Nat) : Nat := a + b + c

def add3T := #leanscript_to_term add3

example : (add3T (Δ := DSig.nil)).run (1 : Nat) (2 : Nat) (3 : Nat) = add3 1 2 3 := rfl

def mx (a b : Nat) : Nat := if a < b then b else a
def mxT := #leanscript_to_term mx
example : (mxT (Δ := DSig.nil)).run (3 : Nat) (7 : Nat) = (7 : Nat) := rfl

def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

def sumToT := #leanscript_to_term sumTo
example : (sumToT (Δ := DSig.nil)).run (5 : Nat) = sumTo 5 := rfl

/-- The translation of `sumTo` computes `sumTo` at every argument. -/
theorem sumToT_run (n : Nat) : (sumToT (Δ := DSig.nil)).run n = sumTo n := by
  have key : ∀ m, natIter (0 : Nat) (fun k acc => k + 1 + acc) m = sumTo m := by
    intro m; induction m <;> simp_all [natIter, sumTo]
  exact key n

def optGet (o : Option Nat) : Nat := match o with | none => 0 | some x => x
def optGetT := #leanscript_to_term optGet
example : (optGetT (Δ := DSig.nil)).run (some (4 : Nat)) = (4 : Nat) := rfl

inductive Color where
  | red | green | blue

def colorNum : Color → Nat
  | .red => 10
  | .green => 20
  | .blue => 30

def colorNumT := #leanscript_to_term colorNum
example : (colorNumT (Δ := DSig.nil)).run (1 : Fin 3) = (20 : Nat) := rfl

def notB (b : Bool) : Bool := match b with | true => false | false => true
def notBT := #leanscript_to_term notB
example : (notBT (Δ := DSig.nil)).run true = false := rfl

structure Point where
  x : Nat
  y : Nat

def Point.sum (p : Point) : Nat := p.x + p.y
def pointSumT := #leanscript_to_term Point.sum
example : (pointSumT (Δ := DSig.nil)).run ((3 : Nat), (4 : Nat)) = (7 : Nat) := rfl

def swapP (p : Point) : Point := { x := p.y, y := p.x }
def swapPT := #leanscript_to_term swapP
example : (swapPT (Δ := DSig.nil)).run ((3 : Nat), (4 : Nat)) = ((4 : Nat), (3 : Nat)) := rfl

def letTwice (n : Nat) : Nat := let m := n * 2; m + m
def letTwiceT := #leanscript_to_term letTwice
example : (letTwiceT (Δ := DSig.nil)).run (5 : Nat) = (20 : Nat) := rfl

def safeDiv (a b : Nat) : Nat := if _h : b = 0 then 0 else a / b
def safeDivT := #leanscript_to_term safeDiv
example : (safeDivT (Δ := DSig.nil)).run (10 : Nat) (2 : Nat) = (5 : Nat) := rfl

/-! ## Recursive datatypes: over the current program -/

inductive Tree where
  | leaf : Tree
  | node : Tree → Nat → Tree → Tree

leanscript_signature Prog where
  listNat := List Nat
  tree := Tree

def lsum : List Nat → Nat
  | [] => 0
  | x :: xs => x + lsum xs

def lsumT := #leanscript_to_term lsum

def addK (k : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => (x + k) :: addK k xs

def addKT := #leanscript_to_term addK

def tsum : Tree → Nat
  | .leaf => 0
  | .node l n r => tsum l + n + tsum r

def tsumT := #leanscript_to_term tsum

def mkList : Term Prog.Δ [] Prog.listNat :=
  (#leanscript_get_ctor List.cons (α := Nat)) (.lit .nat rfl 1)
    ((#leanscript_get_ctor List.cons (α := Nat)) (.lit .nat rfl 2)
      (#leanscript_get_ctor List.nil (α := Nat)))

example : lsumT.run mkList.run = (3 : Nat) := rfl
example : lsumT.run ((addKT.run (10 : Nat)) mkList.run) = (23 : Nat) := rfl

def leafT : Term Prog.Δ [] Prog.tree := #leanscript_get_ctor Tree.leaf
def treeT : Term Prog.Δ [] Prog.tree :=
  (#leanscript_get_ctor Tree.node) ((#leanscript_get_ctor Tree.node) leafT (.lit .nat rfl 1) leafT)
    (.lit .nat rfl 2) leafT

example : tsumT.run treeT.run = (3 : Nat) := rfl

/-- Course-of-values recursion: `fibL (y :: t)` and `fibL t` are one and two levels down, so
    the translation is `data_brec` of depth `1`. -/
def fibL : List Nat → Nat
  | [] => 0
  | [_] => 1
  | _ :: y :: t => fibL (y :: t) + fibL t

def fibLT := #leanscript_to_term fibL

def mkList5 : Term Prog.Δ [] Prog.listNat :=
  (#leanscript_get_ctor List.cons (α := Nat)) (.lit .nat rfl 1)
    ((#leanscript_get_ctor List.cons (α := Nat)) (.lit .nat rfl 2)
      ((#leanscript_get_ctor List.cons (α := Nat)) (.lit .nat rfl 3)
        ((#leanscript_get_ctor List.cons (α := Nat)) (.lit .nat rfl 4)
          ((#leanscript_get_ctor List.cons (α := Nat)) (.lit .nat rfl 5)
            (#leanscript_get_ctor List.nil (α := Nat))))))

example : fibLT.run mkList5.run = fibL [1, 2, 3, 4, 5] := rfl

/-! ## The command shows the type of the translation -/

/--
info: lsum : Term Prog.Δ [] ((Ty.data (Ref.here 0).there).fn (Ty.prim LeanPrimTy.nat ⋯))
-/
#guard_msgs in
#leanscript_to_term lsum
/--
info: sumTo : {ks : List Nat} → {Δ : DSig ks} → Term Δ [] ((Ty.prim LeanPrimTy.nat ⋯).fn (Ty.prim LeanPrimTy.nat ⋯))
-/
#guard_msgs in
#leanscript_to_term sumTo

/-! ## Refusals -/

def withUnit (_u : Unit) (n : Nat) : Nat := n
/--
error: LeanScript: the type
  PUnit
has one constructor and no field (it has one value)
-/
#guard_msgs in
#leanscript_to_term withUnit

def isSomeU (o : Option Unit) : Bool := o.isSome
/--
error: LeanScript: the type
  PUnit
has one constructor and no field (it has one value)
-/
#guard_msgs in
#leanscript_to_term isSomeU

def letUnit (n : Nat) : Nat := let _u : Unit := (); n
/--
error: LeanScript: the type
  PUnit
has one constructor and no field (it has one value)
-/
#guard_msgs in
#leanscript_to_term letUnit

def lenL (l : List Nat) : Nat := l.length
/--
error: LeanScript: the argument
  l
of `List.length` is not a value of a leaf type (an extern takes and returns values of leaf types only)
-/
#guard_msgs in
#leanscript_to_term lenL

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)
/--
error: LeanScript: the recursive call
  fib (n✝ + 1)
is not structural: it must pass the parameters unchanged except the one recursed on, which must be a direct subvalue of it
-/
#guard_msgs in
#leanscript_to_term fib

def idT (α : Type) (a : α) : α := a
/--
error: LeanScript: the parameter `α` of `ToTermTest.idT` is a type
-/
#guard_msgs in
#leanscript_to_term idT

def forceB (t : Thunk Bool) : Bool := t.get
/--
error: LeanScript: `Thunk` is not a type of the language: a delay denotes the value it stands for, so `Thunk Bool` would be a second type of two values
  Thunk Bool
-/
#guard_msgs in
#leanscript_to_term forceB

end ToTermTest

end
