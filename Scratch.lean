import LeanScript.Term.Elab
import LeanScript.Term.Compile
open LeanScript LeanScript.Term

inductive Dir where
  | north
  | south

structure Point where
  x : Nat
  y : Nat

inductive T where
  | leaf
  | node : T → T → T

structure Tree where
  n : Nat
  kids : Array Tree

mutual
  inductive Ev where
    | zero
    | succ : Od → Ev
  inductive Od where
    | succ : Ev → Od
end

#leanjs_ty_for Dir
#leanjs_ty_for Point
#leanjs_ty_for T
#leanjs_ty_for Tree
#leanjs_ty_for Ev
#leanjs_ty_for (Option Nat)
#leanjs_ty_for (Nat → Bool)

def dirTy : Ty := leanscript_ty% Dir
def tTy : Ty := leanscript_ty% T
#print dirTy
