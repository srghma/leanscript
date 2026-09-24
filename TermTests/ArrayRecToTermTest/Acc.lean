module

public import TermTests.ArrayRecToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! Part of the `array_rec k` translation tests; see
`TermTests/ArrayRecToTermTest/Common.lean` for what is checked. -/

namespace TermTests.ArrayRecToTerm

open LeanScript

/-! ## `k = 0` at a function type: an accumulator

A `go` that takes more arguments than the list is compiled with them in the motive, so
the fold is at the function type `nat ⇒ nat`, and the accumulator is passed on the way
down. -/

def sumAccArr (a : Array Nat) : Nat := go a.toList 0
where
  go : List Nat → Nat → Nat
    | [], acc => acc
    | x :: xs, acc => go xs (acc + x)

def sumAccArr_term : Term sig0 [] (TyWf.array (.prim .nat) ⇒ TyWf.prim .nat) :=
  #leanscript_to_term sumAccArr

example : run sumAccArr_term #[] = 0 := by kernel_rfl
example : run sumAccArr_term #[1, 2, 3, 4] = 10 := by kernel_rfl
example : run sumAccArr_term #[1, 2, 3, 4] = sumAccArr #[1, 2, 3, 4] := by kernel_rfl

/-! ## What is refused

The branch of `array_rec` is given the head and the values of the fold at the suffixes —
not the elements after the head.  A `go` that reads the second element is refused. -/

def adjArr (a : Array Nat) : Nat := go a.toList
where
  go : List Nat → Nat
    | [] => 0
    | [_] => 0
    | x :: y :: xs => x + y + go (y :: xs)

/--
error: `#leanscript_to_term`: this recursion on the elements of an array is not the fold of an array — the fold `array_rec k` gives its branch the head and the values at the `k + 1` nearest suffixes of the tail, so a branch that reads an element past the head, or the tail itself, or the value at a list that is not a suffix, has no term
-/
#guard_msgs in
def adjArr_term : Term sig0 [] (TyWf.array (.prim .nat) ⇒ TyWf.prim .nat) :=
  #leanscript_to_term adjArr

end TermTests.ArrayRecToTerm
