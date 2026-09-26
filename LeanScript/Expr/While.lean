module

@[expose] public section

set_option autoImplicit false

/-!
# The meaning of a `while` loop

A `while` loop (and `repeat`, and `repeat … until`) is, after `do` is elaborated, a loop
over `Lean.Loop` in which each iteration answers a step `ForInStep β`: `yield s` to go on
from the state `s`, `done s` to stop with it.  Lean gives it meaning with `repeatM`, whose
implementation is `partial`: the kernel cannot run it, and a loop that never stops has a
value nobody can compute.

The term language keeps its evaluator a total, structural function, so its loop node
(`LeanScript.Term.while_loop`) is given meaning by `LeanScript.whileIter`: the same
iteration, run for at most `LeanScript.whileFuel = 2 ^ 64` iterations.  That bound is a
property of the *model* only — no program runs `2 ^ 64` iterations in practice, and the
backend prints the node as a plain `while`.  `LeanScript.WhileFacts` proves that the model
agrees with Lean's own loop whenever the loop stops within the bound.

`whileIter` is structural in its fuel, so the kernel runs it by unfolding only as many
iterations as the loop takes: `whileIter step (2 ^ 64) s` on a loop of `1000` iterations
unfolds `1000` times (the numeral is taken apart one successor at a time, lazily).
-/

namespace LeanScript

/-- The number of iterations the model of a `while` loop runs at most (`2 ^ 64`).  A loop
    that is still going after that many answers the state it has reached. -/
def whileFuel : Nat := 2 ^ 64

/-- `whileIter step n s`: run the loop whose iteration is `step` from the state `s` for at
    most `n` iterations.  A `done s'` step stops with `s'`; a `yield s'` step goes on from
    `s'`; with no fuel left the answer is the current state. -/
def whileIter {β : Type} (step : β → ForInStep β) : Nat → β → β
  | 0, s => s
  | n + 1, s =>
      match step s with
      | .done s' => s'
      | .yield s' => whileIter step n s'

/-- `whileIter? step n s`: the state the loop stops with **if** it stops (reaches a `done`
    step) within `n` iterations, and `none` otherwise. -/
def whileIter? {β : Type} (step : β → ForInStep β) : Nat → β → Option β
  | 0, _ => none
  | n + 1, s =>
      match step s with
      | .done s' => some s'
      | .yield s' => whileIter? step n s'

end LeanScript

end
