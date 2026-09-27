module

public import LeanScript.Term.Eval
public meta import LeanScript.TermElab.ToTerm
public meta import LeanScript.TacticElab.KernelRfl

@[expose] public section

set_option autoImplicit false

/-!
# `#leanscript_to_term`

Lean definitions translated to `LeanScript.Term` (in A-normal form), and the translations run
by `Term.eval` against the Lean definitions (by `rfl`).  Values of the datatypes are built as
pure expressions (`PExpr`) by the constructor functions of `#leanscript_get_ctor`.  Non-recursive definitions, `if`, `match` on
`Option`, an enum, `Bool` and a structure, projections, `let`, structural recursion on `Nat`
(`nat_rec`), on `List Nat` and on a binary tree (`data_rec`), a map that builds a list
(`data_in` through `#leanscript_get_ctor`), and course-of-values recursion (`data_brec`).
Then the refusals: every unit-like type (`Option Unit`, a `let` of `()`), a library function
that is not the Lean function of an extern (`List.length`), a non-structural recursive call, a
type parameter.  Last the delays `Thunk τ` and `Unit → τ`.
-/

namespace ToTermTest

open LeanScript

def add3 (a b c : Nat) : Nat := a + b + c

def add3T := #leanscript_to_term add3

example : (add3T (Δ := DSig.nil)).run (1 : Nat) (2 : Nat) (3 : Nat) = add3 1 2 3 := rfl

def mx (a b : Nat) : Nat := if a < b then b else a
def mxT := #leanscript_to_term mx
example : (mxT (Δ := DSig.nil)).run (3 : Nat) (7 : Nat) = (7 : Nat) := rfl

/-- An `if` that is not in tail position, whose branches are pure: `n * 2` and `+ 1` are
    calls of externs (`PExpr.extern`, neutral pure expressions), so the `if` is the pure
    conditional `PExpr.cond` and the whole body is one pure expression, with no join point. -/
def nonTailIf (b : Bool) (n : Nat) : Nat := (if b then n * 2 else 0) + 1
def nonTailIfT := #leanscript_to_term nonTailIf
example : (nonTailIfT (Δ := DSig.nil)).run true (4 : Nat) = (9 : Nat) := rfl
example : (nonTailIfT (Δ := DSig.nil)).run false (4 : Nat) = (1 : Nat) := rfl

example {ks : List Nat} {Δ : DSig ks} : nonTailIfT (Δ := Δ) =
    .ofComp (.lam (.ofComp (.lam
      (.ret (.lean_nat_add
        (.cond (.bvar 1) (.lean_nat_mul (.bvar 0) (.lit .nat 2)) (.lit .nat 0))
        (.lit .nat 1)))))) := rfl

/-- Every call of an extern is a pure expression, whatever the extern (`String.length`, on a
    string, as well as `Nat.add`): there is no distinction between cheap and costly externs, so
    this `if` is a `PExpr.cond` too.  (An extern call whose value should be computed once is
    named by a `let`, `Comp.share`.) -/
def nonTailIfCall (b : Bool) (s : String) : Nat := (if b then s.length else 0) + 1
def nonTailIfCallT := #leanscript_to_term nonTailIfCall
example : (nonTailIfCallT (Δ := DSig.nil)).run true "abc" = (4 : Nat) := rfl
example : (nonTailIfCallT (Δ := DSig.nil)).run false "abc" = (1 : Nat) := rfl

example {ks : List Nat} {Δ : DSig ks} : nonTailIfCallT (Δ := Δ) =
    .ofComp (.lam (.ofComp (.lam
      (.ret (.lean_nat_add
        (.cond (.bvar 1) (.lean_string_length__String_length (.bvar 0)) (.lit .nat 0))
        (.lit .nat 1)))))) := rfl

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

def mkList : PExpr Prog.Δ [] Prog.listNat :=
  (#leanscript_get_ctor List.cons (α := Nat)) (.lit .nat 1)
    ((#leanscript_get_ctor List.cons (α := Nat)) (.lit .nat 2)
      (#leanscript_get_ctor List.nil (α := Nat)))

example : lsumT.run mkList.run = (3 : Nat) := rfl
example : lsumT.run ((addKT.run (10 : Nat)) mkList.run) = (23 : Nat) := by kernel_rfl

def leafT : PExpr Prog.Δ [] Prog.tree := #leanscript_get_ctor Tree.leaf
def treeT : PExpr Prog.Δ [] Prog.tree :=
  (#leanscript_get_ctor Tree.node) ((#leanscript_get_ctor Tree.node) leafT (.lit .nat 1) leafT)
    (.lit .nat 2) leafT

example : tsumT.run treeT.run = (3 : Nat) := by kernel_rfl

/-- Course-of-values recursion: `fibL (y :: t)` and `fibL t` are one and two levels down, so
    the translation is `data_brec` of depth `1`. -/
def fibL : List Nat → Nat
  | [] => 0
  | [_] => 1
  | _ :: y :: t => fibL (y :: t) + fibL t

def fibLT := #leanscript_to_term fibL

def mkList5 : PExpr Prog.Δ [] Prog.listNat :=
  (#leanscript_get_ctor List.cons (α := Nat)) (.lit .nat 1)
    ((#leanscript_get_ctor List.cons (α := Nat)) (.lit .nat 2)
      ((#leanscript_get_ctor List.cons (α := Nat)) (.lit .nat 3)
        ((#leanscript_get_ctor List.cons (α := Nat)) (.lit .nat 4)
          ((#leanscript_get_ctor List.cons (α := Nat)) (.lit .nat 5)
            (#leanscript_get_ctor List.nil (α := Nat))))))

example : fibLT.run mkList5.run = fibL [1, 2, 3, 4, 5] := by kernel_rfl

/-! ## The command shows the type of the translation -/

/--
info: lsum : Term Prog.Δ [] ((Ty.data (Ref.here 0).there).fn (Ty.prim LeanPrimTy.nat)) []
-/
#guard_msgs in
#leanscript_to_term lsum
/--
info: sumTo : {ks : List Nat} → {Δ : DSig ks} → Term Δ [] ((Ty.prim LeanPrimTy.nat).fn (Ty.prim LeanPrimTy.nat)) []
-/
#guard_msgs in
#leanscript_to_term sumTo

/-! ## Refusals -/

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
error: LeanScript: the call
  l.length
is not a call of an extern: `List.length` is not the Lean function of an entry of the catalogue of externs (`LeanInitPureExtern`), and its definition cannot be unfolded
-/
#guard_msgs in
#leanscript_to_term lenL

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)
/--
error: LeanScript: the recursive call
  fib n✝
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

/-! ## Delays

`Thunk τ` and `Unit → τ` are the delays `.thunk τ` and `.lazy τ`; `t.get`, `Thunk.pure a`,
`Thunk.mk f`, `fun _ => a`, `f ()` and a parameter `_ : Unit` translate to `thunk_force`,
`thunk_mk`, `lazy_mk` and `lazy_force`, which run as the identity. -/

def forceB (t : Thunk Bool) : Bool := t.get
def forceBT := #leanscript_to_term forceB
example (b : Bool) : (forceBT (Δ := DSig.nil)).run b = forceB (Thunk.pure b) := by
  cases b <;> rfl

def delayN (n : Nat) : Thunk Nat := Thunk.pure (n + 1)
def delayNT := #leanscript_to_term delayN
example : (delayNT (Δ := DSig.nil)).run (4 : Nat) = (5 : Nat) := rfl

def lazyAdd (n : Nat) : Unit → Nat := fun _ => n + 2
def lazyAddT := #leanscript_to_term lazyAdd
example : (lazyAddT (Δ := DSig.nil)).run (4 : Nat) = (6 : Nat) := rfl

def withUnit (_u : Unit) (n : Nat) : Nat := n
def withUnitT := #leanscript_to_term withUnit
example : (withUnitT (Δ := DSig.nil)).run (3 : Nat) = withUnit () 3 := rfl

def callLazy (f : Unit → Nat) : Nat := f () + 1
def callLazyT := #leanscript_to_term callLazy
example : (callLazyT (Δ := DSig.nil)).run (4 : Nat) = callLazy (fun _ => 4) := rfl

/-- `Thunk (Unit → Nat)` is `.thunk nat`: `t.get` (a lazy delay) is the thunk forced, then
    delayed again as a lazy delay, then forced by `()`. -/
def forceTwice (t : Thunk (Unit → Nat)) : Nat := t.get ()
def forceTwiceT := #leanscript_to_term forceTwice
example : (forceTwiceT (Δ := DSig.nil)).run (7 : Nat) = forceTwice (Thunk.pure fun _ => 7) := rfl

def mkThunkFn (n : Nat) : Thunk Nat := Thunk.mk fun _ => n * 2
def mkThunkFnT := #leanscript_to_term mkThunkFn
example : (mkThunkFnT (Δ := DSig.nil)).run (4 : Nat) = (8 : Nat) := rfl

end ToTermTest

end
