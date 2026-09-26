module

public import TermTests.ToTermTest.ListLibrary
public meta import LeanScript.KernelRfl
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `while` loops: structural recursions only

A `while` loop in the identity monad (`Id.run do …`), and `repeat` / `repeat … until`.
The language has no loop node, no fuel and no measure: `#leanscript_to_term` accepts a
loop only when its syntax shows that it is a structural recursion, and rejects it
otherwise (`LeanScript.ToTerm.whileCounter?`).  A loop is accepted when some `Nat`
variable `x` of its state (a `let mut`) moves by one on every path that goes on with the
loop:

* **down**: to `x - 1` after a test that `x ≠ 0` (`while x > 0`, `while x != 0`,
  `if x == 0 then break`, `if h : x = 0 then break else …`), or to `n` in the case
  `n + 1` of a `match` on `x`.  The loop is the recursion on `x`;
* **up**: to `x + 1` after a test `x < b` or `x ≤ b`, whose bound `b` the loop does not
  change.  The loop is the recursion on `b - x`, as `for x in [x:b]` is.

Paths that leave the loop (the condition failing, `break`, `return` from inside) are
unconstrained.  An accepted loop is translated as the `Nat.rec` on the number of
iterations the counter allows (plus one), folding the step `ForInStep β`
(`LeanScript.ToTerm.whileAsNatRec`); `LeanScript.loop_forIn_eq_natRec` is the equation
with Lean's loop, for every input.

Every accepted program is run on inputs and compared by `kernel_rfl` (the kernel's
evaluation, no `native_decide`) with a value written out; the Lean function it came from
is checked against the same value by `#guard`.  Every rejected program is checked to be
rejected, by `#guard_msgs`. -/

namespace TermTests.ToTerm.While

open LeanScript TermTests.NatRecDepth TermTests.StructRec.Split TermTests.ToTerm.ListLibrary

/-! ## Counting down -/

/-- `1 + 2 + … + n`, counting down. -/
def sumDown (n : Nat) : Nat := Id.run do
  let mut i := n
  let mut s := 0
  while i > 0 do
    s := s + i
    i := i - 1
  return s

def sumDown_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term sumDown

example : runAdd sumDown_term 0 = 0 := by kernel_rfl
example : runAdd sumDown_term 1 = 1 := by kernel_rfl
example : runAdd sumDown_term 10 = 55 := by kernel_rfl
example : runAdd sumDown_term 100 = 5050 := by kernel_rfl
#guard sumDown 0 = 0
#guard sumDown 10 = 55
#guard sumDown 100 = 5050

/-- The numbers in `1, …, n` that are not multiples of `3`: a test `!=`, and a `continue`
    that also counts down. -/
def nonMultiplesOf3 (n : Nat) : Nat := Id.run do
  let mut i := n
  let mut c := 0
  while i != 0 do
    if i % 3 == 0 then
      i := i - 1
      continue
    c := c + 1
    i := i - 1
  return c

def nonMultiplesOf3_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term nonMultiplesOf3

example : runAdd nonMultiplesOf3_term 0 = 0 := by kernel_rfl
example : runAdd nonMultiplesOf3_term 10 = 7 := by kernel_rfl
#guard nonMultiplesOf3 10 = 7

/-- `repeat` with `if i == 0 then break`: `2 * (1 + … + n)`. -/
def doubleSumDown (n : Nat) : Nat := Id.run do
  let mut s := 0
  let mut i := n
  repeat
    if i == 0 then break
    s := s + 2 * i
    i := i - 1
  return s

def doubleSumDown_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term doubleSumDown

example : runAdd doubleSumDown_term 0 = 0 := by kernel_rfl
example : runAdd doubleSumDown_term 10 = 110 := by kernel_rfl
#guard doubleSumDown 10 = 110

/-- A `match` on the counter: the case `k + 1` goes on with `k`. -/
def sumBelowMatch (n : Nat) : Nat := Id.run do
  let mut s := 0
  let mut i := n
  while true do
    match i with
    | 0 => break
    | k + 1 =>
      s := s + k
      i := k
  return s

def sumBelowMatch_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term sumBelowMatch

example : runAdd sumBelowMatch_term 0 = 0 := by kernel_rfl
example : runAdd sumBelowMatch_term 10 = 45 := by kernel_rfl
#guard sumBelowMatch 10 = 45

/-- `if h : i = 0 then break else …`: the test is a `dite`. -/
def drainDite (n : Nat) : Nat := Id.run do
  let mut i := n
  let mut k := 0
  while true do
    if _h : i = 0 then break
    else
      k := k + 2
      i := i - 1
  return k

def drainDite_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term drainDite

example : runAdd drainDite_term 7 = 14 := by kernel_rfl
#guard drainDite 7 = 14

/-- An early `return` from inside a loop counting down: the largest `i ≤ n` with
    `i * i < n`, or `0`. -/
def isqrtBelow (n : Nat) : Nat := Id.run do
  let mut i := n
  while i > 0 do
    if i * i < n then return i
    i := i - 1
  return 0

def isqrtBelow_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term isqrtBelow

example : runAdd isqrtBelow_term 0 = 0 := by kernel_rfl
example : runAdd isqrtBelow_term 50 = 7 := by kernel_rfl
example : runAdd isqrtBelow_term 49 = 6 := by kernel_rfl
#guard isqrtBelow 50 = 7
#guard isqrtBelow 49 = 6

/-- A loop counting down inside another: `1 + 2 + … + n` again. -/
def nestedDown (n : Nat) : Nat := Id.run do
  let mut i := n
  let mut s := 0
  while i > 0 do
    let mut j := i
    while j > 0 do
      s := s + 1
      j := j - 1
    i := i - 1
  return s

def nestedDown_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term nestedDown

example : runAdd nestedDown_term 10 = 55 := by kernel_rfl
#guard nestedDown 10 = 55

/-! ## Counting up to a bound the loop does not change -/

/-- Count up from `1` while `i < n`, stopping early at the first `i` with `i * k > n`. -/
def firstMultiple (k n : Nat) : Nat := Id.run do
  let mut i := 1
  while i < n do
    if i * k > n then break
    i := i + 1
  return i

def firstMultiple_term : Term sigAdd [] (natT ⇒ natT ⇒ natT) :=
  #leanscript_to_term firstMultiple

example : runAdd firstMultiple_term 3 100 = 34 := by kernel_rfl
example : runAdd firstMultiple_term 0 5 = 5 := by kernel_rfl
example : runAdd firstMultiple_term 3 0 = 1 := by kernel_rfl
#guard firstMultiple 3 100 = 34
#guard firstMultiple 0 5 = 5
#guard firstMultiple 3 0 = 1

/-- The sum of the odd numbers below `n`, skipping the even ones with `continue` (the
    counter goes up first, on every path). -/
def sumOddBelow (n : Nat) : Nat := Id.run do
  let mut i := 0
  let mut s := 0
  while i < n do
    i := i + 1
    if i % 2 == 0 then continue
    if i < n then s := s + i
  return s

def sumOddBelow_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term sumOddBelow

example : runAdd sumOddBelow_term 10 = 25 := by kernel_rfl
example : runAdd sumOddBelow_term 0 = 0 := by kernel_rfl
#guard sumOddBelow 10 = 25

/-- `!` on a `Bool` state of a loop: the parity of `n`. -/
def parityOfSteps (n : Nat) : Bool := Id.run do
  let mut i := 0
  let mut odd := false
  while i < n do
    odd := !odd
    i := i + 1
  return odd

def parityOfSteps_term : Term sigAdd [] (natT ⇒ TyWf.prim .bool) :=
  #leanscript_to_term parityOfSteps

example : runAdd parityOfSteps_term 0 = false := by kernel_rfl
example : runAdd parityOfSteps_term 7 = true := by kernel_rfl
example : runAdd parityOfSteps_term 10 = false := by kernel_rfl
#guard parityOfSteps 7 = true

/-- A bound `i ≤ n` (inclusive): `1 + 2 + … + n`, counting up. -/
def sumUpTo (n : Nat) : Nat := Id.run do
  let mut i := 1
  let mut s := 0
  while i ≤ n do
    s := s + i
    i := i + 1
  return s

def sumUpTo_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term sumUpTo

example : runAdd sumUpTo_term 0 = 0 := by kernel_rfl
example : runAdd sumUpTo_term 10 = 55 := by kernel_rfl
#guard sumUpTo 10 = 55

/-- A loop counting up inside another, whose bound is the outer counter:
    `∑_{i < n} ∑_{j < i} 1`. -/
def triangle (n : Nat) : Nat := Id.run do
  let mut i := 0
  let mut s := 0
  while i < n do
    let mut j := 0
    while j < i do
      s := s + 1
      j := j + 1
    i := i + 1
  return s

def triangle_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term triangle

example : runAdd triangle_term 5 = 10 := by kernel_rfl
example : runAdd triangle_term 10 = 45 := by kernel_rfl
#guard triangle 10 = 45

/-! ## Rejected: loops that are not structural recursions -/

/-- The number of halvings that take `n` to `0`: `m / 2` is not the predecessor of `m`
    (the loop terminates, but only by a measure). -/
def halvings (n : Nat) : Nat := Id.run do
  let mut m := n
  let mut k := 0
  while m > 0 do
    m := m / 2
    k := k + 1
  return k

/-- error: `#leanscript_to_term`: this `while` / `repeat` loop is not a structural recursion -/
#guard_msgs (substring := true) in
def halvings_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term halvings

/-- Euclid's algorithm with subtraction: `x - y` and the swap are not a move by one. -/
def gcdLoop (a b : Nat) : Nat := Id.run do
  let mut x := a
  let mut y := b
  while y > 0 do
    if x ≥ y then
      x := x - y
    else
      let t := x
      x := y
      y := t
  return x

/-- error: `#leanscript_to_term`: this `while` / `repeat` loop is not a structural recursion -/
#guard_msgs (substring := true) in
def gcdLoop_term : Term sigAdd [] (natT ⇒ natT ⇒ natT) := #leanscript_to_term gcdLoop

/-- The Collatz steps: nobody knows a measure. -/
def collatzSteps (n : Nat) : Nat := Id.run do
  let mut m := n
  let mut k := 0
  repeat
    if m ≤ 1 then break
    m := if m % 2 == 0 then m / 2 else 3 * m + 1
    k := k + 1
  return k

/-- error: `#leanscript_to_term`: this `while` / `repeat` loop is not a structural recursion -/
#guard_msgs (substring := true) in
def collatzSteps_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term collatzSteps

/-- Counting up with no bound (`while true`): the first `i` with `i * i ≥ n`. -/
def isqrtCeil (n : Nat) : Nat := Id.run do
  let mut i := 0
  while true do
    if i * i ≥ n then return i
    i := i + 1
  return 0

/-- error: `#leanscript_to_term`: this `while` / `repeat` loop is not a structural recursion -/
#guard_msgs (substring := true) in
def isqrtCeil_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term isqrtCeil

/-- `repeat … until`: the counter goes down *before* the test, so nothing shows it was
    not `0` (and at `0` the loop would run forever, `0 - 1 = 0`). -/
def untilZero (n : Nat) : Nat := Id.run do
  let mut i := n
  repeat
    i := i - 1
  until i == 0
  return i

/-- error: `#leanscript_to_term`: this `while` / `repeat` loop is not a structural recursion -/
#guard_msgs (substring := true) in
def untilZero_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term untilZero

/-- A `continue` that does not move the counter. -/
def stuckContinue (n : Nat) : Nat := Id.run do
  let mut i := n
  while i > 0 do
    if i == 5 then continue
    i := i - 1
  return i

/-- error: `#leanscript_to_term`: this `while` / `repeat` loop is not a structural recursion -/
#guard_msgs (substring := true) in
def stuckContinue_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term stuckContinue

/-- Counting up below a bound that the loop changes. -/
def movingBound (n : Nat) : Nat := Id.run do
  let mut i := 0
  let mut b := n
  while i < b do
    i := i + 1
    b := b + 1
  return i

/-- error: `#leanscript_to_term`: this `while` / `repeat` loop is not a structural recursion -/
#guard_msgs (substring := true) in
def movingBound_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term movingBound

/-- A loop that never stops, whose state is the result. -/
def bar (n : Nat) : Nat := Id.run do
  let mut x := n
  while true do
    x := x + 1
  return x

/-- error: `#leanscript_to_term`: this `while` / `repeat` loop is not a structural recursion -/
#guard_msgs (substring := true) in
def bar_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term bar

/-- A loop that never stops and whose result is not used.  In Lean's logic `foo` is `1`
    (`rfl`), and `do` in `Id` would let the translation drop the loop altogether; it is
    still rejected, since it is not a structural recursion. -/
def foo : Id Nat := do
  while true do
    pure ()
  return 1

theorem foo_eq : foo = 1 := rfl

/-- error: `#leanscript_to_term`: this `while` / `repeat` loop is not a structural recursion -/
#guard_msgs (substring := true) in
def foo_term : Term sigAdd [] natT := #leanscript_to_term foo

/-- A structural loop inside a `for` is accepted, but a non-structural one is rejected: the
    total number of halvings of the elements of a list. -/
def totalHalvings (l : List Nat) : Nat := Id.run do
  let mut t := 0
  for x in l do
    let mut m := x
    while m > 0 do
      m := m / 2
      t := t + 1
  return t

/-- error: `#leanscript_to_term`: this `while` / `repeat` loop is not a structural recursion -/
#guard_msgs (substring := true) in
def totalHalvings_term : Term sigAdd [] (natListT ⇒ natT) := #leanscript_to_term totalHalvings

/-- The same count with a loop counting down in the `for`: `∑ x ∈ l, x`. -/
def totalDown (l : List Nat) : Nat := Id.run do
  let mut t := 0
  for x in l do
    let mut m := x
    while m > 0 do
      m := m - 1
      t := t + 1
  return t

def totalDown_term : Term sigAdd [] (natListT ⇒ natT) := #leanscript_to_term totalDown

example : runAdd totalDown_term (natList [1, 8, 10]) = 19 := by kernel_rfl
#guard totalDown [1, 8, 10] = 19

end TermTests.ToTerm.While

end
