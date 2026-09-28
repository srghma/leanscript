module

public import LeanScript.Term.Semantics.Eval

@[expose] public section

set_option autoImplicit false

/-!
# Bounded loops: why a structurally terminating `while` needs no fuel

`#leanscript_to_term` translates a `for` loop over a range and a structurally terminating
`while` loop (`LeanScript.TermElab.ToTerm.While`) to a `Comp.nat_rec` of a fixed number `n` of
steps, whose answer is a `ForInStep β`: it starts at `yield init`, a step runs the body `f` on
the state of a `yield` and keeps a `done`.  This is `boundedLoop f init n` below.

For a `while` loop the translator picks `n` from the syntax: a measure `μ` of the state (the
variable `x` the condition bounds, or `b - x`) that every iteration that goes on (every
`yield`) makes strictly smaller, and `n = μ init + 1`.  This file proves that such an `n` is
enough, so the bound is not fuel:

* `boundedLoop_done`: after `μ init + 1` steps the loop has reached a `done`;
* `boundedLoop_stable`: any number of steps from `μ init + 1` on gives the same state, so the
  answer is the one of the loop run until it stops.
-/

namespace LeanScript

variable {β : Type}

/-- One step of a loop whose body is `f`: the body on the state of a `yield`; a `done` (a
    `break`, a `return`, or the condition that failed) is kept. -/
def loopStep (f : β → ForInStep β) : ForInStep β → ForInStep β
  | .done v => .done v
  | .yield v => f v

/-- `n` steps of a loop whose body is `f`, from the state `init` (as `Comp.nat_rec` runs it). -/
def boundedLoop (f : β → ForInStep β) (init : β) (n : Nat) : ForInStep β :=
  natIter (.yield init) (fun _ acc => loopStep f acc) n

/-- After `n` steps the loop has stopped, or it goes on from a state whose measure is at most
    the initial one minus `n`. -/
theorem boundedLoop_progress (f : β → ForInStep β) (μ : β → Nat)
    (hdec : ∀ v w, f v = .yield w → μ w < μ v) (init : β) :
    ∀ n, (∃ v, boundedLoop f init n = .done v) ∨
      (∃ w, boundedLoop f init n = .yield w ∧ μ w + n ≤ μ init)
  | 0 => .inr ⟨init, rfl, by simp⟩
  | n + 1 => by
    rcases boundedLoop_progress f μ hdec init n with ⟨v, hv⟩ | ⟨w, hw, hμ⟩
    · exact .inl ⟨v, by simp [boundedLoop, natIter] at hv ⊢; rw [hv]; rfl⟩
    · have h : boundedLoop f init (n + 1) = f w := by
        simp [boundedLoop, natIter] at hw ⊢; rw [hw]; rfl
      rw [h]
      cases hf : f w with
      | done v => exact .inl ⟨v, rfl⟩
      | yield w' =>
        have := hdec w w' hf
        exact .inr ⟨w', rfl, by omega⟩

/-- **The bound is enough**: after `μ init + 1` steps the loop has stopped. -/
theorem boundedLoop_done (f : β → ForInStep β) (μ : β → Nat)
    (hdec : ∀ v w, f v = .yield w → μ w < μ v) (init : β) :
    ∃ v, boundedLoop f init (μ init + 1) = .done v := by
  rcases boundedLoop_progress f μ hdec init (μ init + 1) with h | ⟨w, _, hμ⟩
  · exact h
  · omega

/-- A loop that has stopped stays stopped. -/
theorem boundedLoop_add_of_done (f : β → ForInStep β) (init : β) (n : Nat) (v : β)
    (h : boundedLoop f init n = .done v) : ∀ k, boundedLoop f init (n + k) = .done v
  | 0 => h
  | k + 1 => by
    have ih := boundedLoop_add_of_done f init n v h k
    simp [boundedLoop, natIter] at ih ⊢
    rw [ih]
    rfl

/-- **No fuel**: every number of steps from `μ init + 1` on gives the same state, a `done`:
    the answer of the bounded loop is the one of the loop run until it stops. -/
theorem boundedLoop_stable (f : β → ForInStep β) (μ : β → Nat)
    (hdec : ∀ v w, f v = .yield w → μ w < μ v) (init : β) (n : Nat) (hn : μ init + 1 ≤ n) :
    boundedLoop f init n = boundedLoop f init (μ init + 1) := by
  obtain ⟨v, hv⟩ := boundedLoop_done f μ hdec init
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [boundedLoop_add_of_done f init _ v hv k, hv]

end LeanScript

end
