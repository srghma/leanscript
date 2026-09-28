module

public import LeanScript.Term.Build
public meta import LeanScript.TermElab.ToTerm
public meta import LeanScript.TacticElab.KernelRfl

@[expose] public section

set_option autoImplicit false

/-!
# `while` loops

`#leanscript_to_term` accepts a `while` loop in `Id` when it is structurally terminating, as
read off its syntax (`LeanScript.TermElab.ToTerm.While`): the condition bounds a `Nat`
variable of the loop that every iteration that goes on moves towards the bound by a literal
step.  The loop becomes a `Comp.nat_rec` of a number of steps fixed before the loop starts
(`x₀ + 1` for a variable counting down, `b₀ - x₀ + 1` for one counting up to `b`), with no
fuel: `LeanScript.boundedLoop_stable` proves that such a number of steps always reaches the
end of the loop.

Each loop is run by `Term.eval` (checked by the kernel) and by Lean itself (`#guard`, on the
compiled `while`, since `Lean.Loop.forIn` is `partial` and does not reduce).  Then the loops
that are refused: an iteration that does not move the variable, a step that is not a literal,
and a loop with no bound at all.
-/

namespace WhileTest

open LeanScript

/-- Counting down by one: `n + (n - 1) + … + 1`. -/
def sumDown (n : Nat) : Nat := Id.run do
  let mut i := n
  let mut s := 0
  while i > 0 do
    s := s + i
    i := i - 1
  return s
def sumDownT := #leanscript_to_term sumDown
-- (moved to `Tests/Main.lean`: too slow for the kernel, run compiled)
example : (sumDownT (Δ := DSig.nil)).run (0 : Nat) = (0 : Nat) := by kernel_rfl
#guard sumDown 10 == 55

/-- Halving, with `!=`: the number of binary digits. -/
def bits (n : Nat) : Nat := Id.run do
  let mut i := n
  let mut c := 0
  while i != 0 do
    i := i / 2
    c := c + 1
  return c
def bitsT := #leanscript_to_term bits
-- (moved to `Tests/Main.lean`: too slow for the kernel, run compiled)
#guard bits 1000 == 10

/-- Counting up to a bound that the loop does not change. -/
def pow2 (n : Nat) : Nat := Id.run do
  let mut i := 0
  let mut acc := 1
  while i < n do
    acc := acc * 2
    i := i + 1
  return acc
def pow2T := #leanscript_to_term pow2
-- (moved to `Tests/Main.lean`: too slow for the kernel, run compiled)
#guard pow2 10 == 1024

/-- Counting up to a bound held in a variable of the loop that the loop passes unchanged,
    by steps of `3`. -/
def countBy3 (n : Nat) : Nat := Id.run do
  let mut hi := n
  let mut i := 0
  let mut c := 0
  while i < hi do
    c := c + 1
    i := i + 3
  return c + hi
def countBy3T := #leanscript_to_term countBy3
-- (moved to `Tests/Main.lean`: too slow for the kernel, run compiled)
#guard countBy3 10 == 14

/-- `≤` and a `break`: the integer square root, rounded up past `n`. -/
def isqrtUp (n : Nat) : Nat := Id.run do
  let mut i := 0
  while i ≤ n do
    if i * i > n then break
    i := i + 1
  return i
def isqrtUpT := #leanscript_to_term isqrtUp
-- (moved to `Tests/Main.lean`: too slow for the kernel, run compiled)
#guard isqrtUp 50 == 8

/-- A conjunction in the condition: one conjunct bounds the loop. -/
def firstMultiple (n k : Nat) : Nat := Id.run do
  let mut i := n
  while i > 0 && i % k != 0 do
    i := i - 1
  return i
def firstMultipleT := #leanscript_to_term firstMultiple
-- (moved to `Tests/Main.lean`: too slow for the kernel, run compiled)
#guard firstMultiple 100 7 == 98

/-! ## Refused loops -/

/-- The variable moves away from the bound. -/
def away (n : Nat) : Nat := Id.run do
  let mut i := n
  while i > 0 do
    i := i + 1
  return i

/--
error: LeanScript: the `while` loop
  forIn { } i fun x __s =>
    have i := __s;
    if i > 0 then
      have i := i + 1;
      pure (ForInStep.yield i)
    else pure (ForInStep.done i)
is not structurally terminating: the language has no unbounded loop, so a `while` loop is only accepted when its condition bounds a `Nat` variable `x` of the loop (`x > 0`, `x ≠ 0`, `x < b`, `x ≤ b`, with `b` unchanged by the loop) and every iteration that goes on moves `x` towards the bound by a literal step (`x := x - k`, `x := x / k`, `x := x + k`)
-/
#guard_msgs in
def awayT := #leanscript_to_term away

/-- Collatz: the step is not a literal step towards a bound (and nobody knows whether this
    loop always stops). -/
def collatz (n : Nat) : Nat := Id.run do
  let mut i := n
  let mut c := 0
  while i > 1 do
    i := if i % 2 == 0 then i / 2 else 3 * i + 1
    c := c + 1
  return c

/--
error: LeanScript: the `while` loop
  forIn { } (i, c) fun x __s =>
    have i := __s.fst;
    have c := __s.snd;
    if i > 1 then
      have i := if (i % 2 == 0) = true then i / 2 else 3 * i + 1;
      have c := c + 1;
      pure (ForInStep.yield (i, c))
    else pure (ForInStep.done (i, c))
is not structurally terminating: the language has no unbounded loop, so a `while` loop is only accepted when its condition bounds a `Nat` variable `x` of the loop (`x > 0`, `x ≠ 0`, `x < b`, `x ≤ b`, with `b` unchanged by the loop) and every iteration that goes on moves `x` towards the bound by a literal step (`x := x - k`, `x := x / k`, `x := x + k`)
-/
#guard_msgs in
def collatzT := #leanscript_to_term collatz

/-- The bound moves with the variable. -/
def chase (n : Nat) : Nat := Id.run do
  let mut i := 0
  let mut hi := n
  while i < hi do
    i := i + 1
    hi := hi + 1
  return i

/--
error: LeanScript: the `while` loop
  forIn { } (i, hi) fun x __s =>
    have i := __s.fst;
    have hi := __s.snd;
    if i < hi then
      have i := i + 1;
      have hi := hi + 1;
      pure (ForInStep.yield (i, hi))
    else pure (ForInStep.done (i, hi))
is not structurally terminating: the language has no unbounded loop, so a `while` loop is only accepted when its condition bounds a `Nat` variable `x` of the loop (`x > 0`, `x ≠ 0`, `x < b`, `x ≤ b`, with `b` unchanged by the loop) and every iteration that goes on moves `x` towards the bound by a literal step (`x := x - k`, `x := x / k`, `x := x + k`)
-/
#guard_msgs in
def chaseT := #leanscript_to_term chase

end WhileTest

end
