import LeanScript.Eval
import LeanScript.Ty.Instances
import LeanScript.Ty.Deriving
import LeanScript.ToTerm.Elab
import Mathlib.Util.CountHeartbeats
open LeanScript
def sig0 : Sig := ⟨[], by decide⟩
def tribArr (a : Array Nat) : Nat := go a.toList
where
  go : List Nat → Nat
    | [] => 0
    | [x] => x
    | [x, y] => x + go [y]
    | x :: y :: z :: xs => x + go (y :: z :: xs) + go (z :: xs) + go xs
def tribArr_term : Term sig0 [] (TyWf.array (.prim .nat) ⇒ TyWf.prim .nat) :=
  #leanscript_to_term tribArr
set_option maxHeartbeats 100000000
#count_heartbeats in
example : (Term.run (Sg := sig0) GlobalEnv.nil tribArr_term) #[1, 2, 3] = 9 := rfl
#count_heartbeats in
example : (Term.run (Sg := sig0) GlobalEnv.nil tribArr_term) #[1, 1, 1, 1] = 9 := rfl
#count_heartbeats in
example : (Term.run (Sg := sig0) GlobalEnv.nil tribArr_term) #[1, 1, 1, 1, 1] = 9 := rfl
