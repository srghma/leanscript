module

public import Init.Internal.Order.While

@[expose] public section

set_option autoImplicit false

/-!
# A `while` loop whose counter moves towards a bound is a structural recursion

`while c do body` (and `repeat …`, `repeat … until c`) in the identity monad is
`forIn Lean.Loop.mk init f`, with `f : Unit → β → Id (ForInStep β)`: each iteration
answers a step, `yield s` to go on from `s`, `done s` to stop with it.  Lean gives the loop
meaning with `repeatM`, whose implementation is `partial`, so the language has no node for
it: it has no fuel and no measure.

`#leanscript_to_term` accepts a loop only when it can read off the loop's syntax that the
loop is a **structural recursion**: a `Nat` component `x` of the state (the *counter*)
that every path which goes on (`yield`) replaces by its predecessor, under a test that
shows it is not `0`, or by its successor, under a test `x < b` for a bound `b` the loop
does not change (`LeanScript.ToTerm.whileCounter?`).  Such a loop takes at most
`x init + 1` (resp. `b - x init + 1`) iterations, so it is the recursion on that number —
`Nat.rec`, the language's `nat_rec` — whose value is the step after each iteration, a
stopped loop staying stopped.  Any other loop is rejected.

* `LeanScript.loopStepAfter step st`: the step after the step `st`: a stopped loop stays
  stopped, and one that goes on from `s` takes the step `step s`.
* `LeanScript.loop_forIn_eq_natRec`: **the rewriting the translator makes**.  If every
  `yield` step of `f` makes `μ` smaller, Lean's loop is the state of the recursion on
  `μ init + 1` whose value is the step (`ForInStep.casesOn`, as the translator emits it).
  The translator uses it with `μ` the counter (resp. `b` minus the counter), which each
  `yield` makes one smaller.

Nothing is assumed about the loop beyond the decrease: no fuel is involved, and the
equation holds for every initial state.
-/

namespace LeanScript

variable {β : Type}

/-- The step after the step `st` of a loop whose iteration is `step`: a stopped loop
    (`done s`) stays stopped, and one that goes on from `s` takes the step `step s`. -/
def loopStepAfter (step : β → ForInStep β) (st : ForInStep β) : ForInStep β :=
  ForInStep.casesOn (motive := fun _ => ForInStep β) st (fun s => .done s) step

/-- The state a step carries, whether the loop goes on or stops. -/
def loopStepState (st : ForInStep β) : β :=
  ForInStep.casesOn (motive := fun _ => β) st (fun s => s) (fun s => s)

/-- `n` steps after the step `st`. -/
def loopStepsAfter (step : β → ForInStep β) : Nat → ForInStep β → ForInStep β
  | 0, st => st
  | n + 1, st => loopStepsAfter step n (loopStepAfter step st)

theorem loopStepsAfter_done (step : β → ForInStep β) :
    ∀ (n : Nat) (s : β), loopStepsAfter step n (.done s) = .done s
  | 0, _ => rfl
  | n + 1, s => loopStepsAfter_done step n s

/-- The recursion on `n` whose value is the step after each iteration, from the step
    `st`, is `n` steps after `st`. -/
theorem natRec_loopStepAfter (step : β → ForInStep β) (st : ForInStep β) :
    ∀ n : Nat, (Nat.rec (motive := fun _ => ForInStep β) st
      (fun _ acc => loopStepAfter step acc) n) = loopStepsAfter step n st
  | 0 => rfl
  | n + 1 => by
      show loopStepAfter step (Nat.rec (motive := fun _ => ForInStep β) st
        (fun _ acc => loopStepAfter step acc) n) = _
      rw [natRec_loopStepAfter step st n]
      clear natRec_loopStepAfter
      induction n generalizing st with
      | zero => rfl
      | succ k ih => exact ih (loopStepAfter step st)

/-- **Lean's loop, from a state whose measure is below `n`, is `n` steps of it**, when
    every `yield` step makes the measure `μ` smaller. -/
theorem loop_forIn_eq_loopStepsAfter (f : Unit → β → Id (ForInStep β)) (μ : β → Nat)
    (hdec : ∀ s s', (f () s).run = .yield s' → μ s' < μ s) :
    ∀ (n : Nat) (s : β), μ s < n →
      (forIn Lean.Loop.mk s f : Id β).run =
        loopStepState (loopStepsAfter (fun b => (f () b).run) n (.yield s))
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, s, h => by
      show (Lean.Loop.forIn Lean.Loop.mk s f).run = _
      rw [Lean.Loop.forIn_eq_of_monadTail]
      show _ = loopStepState (loopStepsAfter (fun b => (f () b).run) n ((f () s).run))
      cases hs : (f () s).run with
      | done s' =>
          simp only [bind, Id.run] at hs ⊢
          rw [hs, loopStepsAfter_done]; rfl
      | yield s' =>
          have h' : μ s' < n := Nat.lt_of_lt_of_le (hdec s s' hs) (Nat.le_of_lt_succ h)
          simp only [bind, Id.run] at hs ⊢
          rw [hs]
          exact loop_forIn_eq_loopStepsAfter f μ hdec n s' h'

/-- **A `while` loop whose measure goes down is a recursion on `Nat`.**  If every `yield`
    step of `f` makes `μ` smaller, Lean's loop `forIn Lean.Loop.mk init f` in `Id` is the
    state of the recursion on `μ init + 1` whose value is the step after each iteration —
    `yield init` at `0`, then the body's step at the state if the loop has not stopped.
    This is the expression `#leanscript_to_term` builds for a loop whose counter goes
    down (`LeanScript.ToTerm.whileAsNatRec`), with `μ` the counter, and for one whose
    counter goes up to `b`, with `μ` `b` minus the counter. -/
theorem loop_forIn_eq_natRec (f : Unit → β → Id (ForInStep β)) (μ : β → Nat)
    (hdec : ∀ s s', (f () s).run = .yield s' → μ s' < μ s) (init : β) :
    (forIn Lean.Loop.mk init f : Id β).run =
      ForInStep.casesOn (motive := fun _ => β)
        (Nat.rec (motive := fun _ => ForInStep β) (ForInStep.yield init)
          (fun _ st => ForInStep.casesOn (motive := fun _ => ForInStep β) st
            (fun s => ForInStep.done s) (fun s => (f () s).run))
          (μ init + 1))
        (fun s => s) (fun s => s) := by
  rw [loop_forIn_eq_loopStepsAfter f μ hdec (μ init + 1) init (Nat.lt_succ_self _)]
  exact congrArg loopStepState
    (natRec_loopStepAfter (fun b => (f () b).run) (.yield init) (μ init + 1)).symm

end LeanScript

end
