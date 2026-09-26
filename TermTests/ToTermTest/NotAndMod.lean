module

public import TermTests.ToTermTest.While
public meta import LeanScript.KernelRfl
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `!b`, `a != b` and `a % b`

* `!b` is `Bool.not b`, which is not an extern: it is defined as `Bool.rec true false b`
  and marked `@[implicit_reducible]` (its compiled form is `Bool.Internal.not`, through
  `@[csimp]`).  The translation inlines it, as it inlines any `@[implicit_reducible]`
  definition (`LeanScript.ToTerm.isInlinable`), and `Bool.rec` with a non-dependent motive
  is a `bool_casesOn`.  `a != b` is `bne a b`, which is `!(a == b)`, inlined the same way.
* `a % b` on `Nat` is `Mod.mod Nat.instMod a b`, whose field is `Nat.mod`, the pure extern
  `lean_nat_mod`.  The projection out of the instance is reduced to that constant only
  (`LeanScript.ToTerm.transProj`), not unfolded further into the `match` that defines
  `Nat.mod`, so the call is `Term.externCall` of `lean_nat_mod__Nat_mod`.

Each program is run on inputs by `kernel_rfl` and compared with a value written out, and
the Lean function is checked against the same value by `#guard`. -/

namespace TermTests.ToTerm.NotAndMod

open LeanScript TermTests.NatRecDepth TermTests.StructRec.Split TermTests.ToTerm.ListLibrary

/-! ## `!` and `!=` -/

def notB (x : Bool) : Bool := !x
def notB_term : Term sigAdd [] (TyWf.prim .bool ⇒ TyWf.prim .bool) := #leanscript_to_term notB

example : runAdd notB_term true = false := by kernel_rfl
example : runAdd notB_term false = true := by kernel_rfl

/-- The translation of `!x` is one `bool_casesOn` on `x`, with the branches swapped. -/
example : notB_term =
    .letE' (.lam (.bool_casesOn (.var .head)
      (.letE (.bool_mk false) (.ret (.var .head)))
      (.letE (.bool_mk true) (.ret (.var .head)))))
      (.ret (.var .head)) := rfl

def neq (x y : Nat) : Bool := x != y
def neq_term : Term sigAdd [] (natT ⇒ natT ⇒ TyWf.prim .bool) := #leanscript_to_term neq

example : runAdd neq_term 17 5 = true := by kernel_rfl
example : runAdd neq_term 5 5 = false := by kernel_rfl
#guard neq 17 5 = true
#guard neq 5 5 = false

/-- `!` on a value that is not a variable, inside `&&` and `||`. -/
def xorB (a b : Bool) : Bool := (a && !b) || (!a && b)
def xorB_term : Term sigAdd [] (TyWf.prim .bool ⇒ TyWf.prim .bool ⇒ TyWf.prim .bool) :=
  #leanscript_to_term xorB

example : runAdd xorB_term true true = false := by kernel_rfl
example : runAdd xorB_term true false = true := by kernel_rfl
example : runAdd xorB_term false true = true := by kernel_rfl
example : runAdd xorB_term false false = false := by kernel_rfl

/-! ## `%` on `Nat` -/

def modNat (x y : Nat) : Nat := x % y
def modNat_term : Term sigAdd [] (natT ⇒ natT ⇒ natT) := #leanscript_to_term modNat

example : runAdd modNat_term 17 5 = 2 := by kernel_rfl
example : runAdd modNat_term 15 5 = 0 := by kernel_rfl
example : runAdd modNat_term 3 0 = 3 := by kernel_rfl
#guard modNat 17 5 = 2
#guard modNat 3 0 = 3

def isOdd (x : Nat) : Bool := x % 2 == 1
def isOdd_term : Term sigAdd [] (natT ⇒ TyWf.prim .bool) := #leanscript_to_term isOdd

example : runAdd isOdd_term 17 = true := by kernel_rfl
example : runAdd isOdd_term 0 = false := by kernel_rfl
#guard isOdd 17 = true

/-- `%` and `!=` in the test of an `if`. -/
def halveOrTriple (x : Nat) : Nat := if x % 2 != 0 then 3 * x + 1 else x / 2
def halveOrTriple_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term halveOrTriple

example : runAdd halveOrTriple_term 7 = 22 := by kernel_rfl
example : runAdd halveOrTriple_term 10 = 5 := by kernel_rfl
#guard halveOrTriple 7 = 22

/-- `%` and `!=` in a `while` loop counting down: how many of `1, …, n` are odd. -/
def countOdd (n : Nat) : Nat := Id.run do
  let mut i := n
  let mut c := 0
  while i != 0 do
    if i % 2 == 1 then c := c + 1
    i := i - 1
  return c

def countOdd_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term countOdd

example : runAdd countOdd_term 0 = 0 := by kernel_rfl
example : runAdd countOdd_term 7 = 4 := by kernel_rfl
example : runAdd countOdd_term 10 = 5 := by kernel_rfl
#guard countOdd 7 = 4

/-- The digit sum, with `%` and `/` in a `while` loop.  `m / 10` is not the predecessor
    of `m`, so the loop is not a structural recursion, and it is rejected (see
    `TermTests/ToTermTest/While.lean`). -/
def digitSum (n : Nat) : Nat := Id.run do
  let mut m := n
  let mut s := 0
  while m != 0 do
    s := s + m % 10
    m := m / 10
  return s

/-- error: `#leanscript_to_term`: this `while` / `repeat` loop is not a structural recursion -/
#guard_msgs (substring := true) in
def digitSum_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term digitSum

/-- Euclid's algorithm with `%`: not a structural recursion either, so rejected. -/
def gcdMod (a b : Nat) : Nat := Id.run do
  let mut x := a
  let mut y := b
  while y != 0 do
    let t := x % y
    x := y
    y := t
  return x

/-- error: `#leanscript_to_term`: this `while` / `repeat` loop is not a structural recursion -/
#guard_msgs (substring := true) in
def gcdMod_term : Term sigAdd [] (natT ⇒ natT ⇒ natT) := #leanscript_to_term gcdMod

end TermTests.ToTerm.NotAndMod

end
