module

public import TyTests.NatRecKTest

@[expose] public section

/-!
# The five `fib`s, and which of them the grammar already writes

`FibProposals.md` is written around five Lean definitions of the same function — the
two-step recursion, the tail-recursive loop, the `for` loop with two mutable variables,
the pair recursion, and fast doubling.  The point of supporting them *as they are* is
that the code the backend prints should look like the code that was written, so the
question "which of these is a term of the grammar today?" has to be answered one
definition at a time rather than for `fib` in general.

This file answers it by writing the terms and proving what they compute.  It is the
evidence behind the table in §2 of `FibProposals.md`:

| definition | what it needs | here |
| :-- | :-- | :-- |
| `fibLoopTR` / `fibTR` | `nat_rec` **at a function type** — already there | `fibTR_term_eval` |
| `fibPair` / `fib2` | `nat_rec` at a record type — already there | `fibPair_term_eval` |
| `fibLoop` (`for` loop) | the same fold, and a case for `for` in the translation | prose below; translated in `TyTests/NatRecDepthTest.lean` |
| `fib` (`n + 2` pattern) | a depth-two fold: a window, or the depth-indexed node | `TyTests/FibWindowTest.lean`, `TyTests/NatRecKTest.lean`, `TyTests/NatRecDepthTest.lean` |
| `fibFast` (`n / 2`) | a descent that is not by a fixed number of steps | prose below |

Since this file was written, the node and the two translation cases it names as missing
have been implemented: `LeanScript.Term.nat_rec k` descends `k + 1` steps, and
`#leanscript_to_term` translates both the `n + 2` pattern and a `for` loop over a range.
`TyTests/NatRecDepthTest.lean` hands each of the five definitions to the translation as
it is written.  What is below is unchanged, and is still the hand-written evidence that
the first two need nothing beyond a fold at a function type and at a record type.

Everything below runs in the signature of `TyTests/FibWindowTest.lean`: one declaration,
`add`.
-/

namespace TyTests.FibAlgorithms

open LeanScript
open TyTests.FibWindow (fib sigAdd envAdd addT)

local macro:max "runAdd" t:term:max : term => `(Term.run (Sg := sigAdd) envAdd $t)

/-! ## 1. The tail-recursive loop: a fold whose value is a function

```lean
def fibLoopTR : Nat → Nat → Nat → Nat
  | 0,     a, _ => a
  | n + 1, a, b => fibLoopTR n b (a + b)

def fibTR (n : Nat) : Nat := fibLoopTR n 0 1
```

The recursion descends one step, but its accumulators change on the way down, so the
value of the fold is not a number: it is the **function** `Nat → Nat → Nat` that takes
the two accumulators.  `Term.nat_rec` folds at any type `τ`, function types included, so
this needs nothing new — which is worth saying, because a first reading of "the branch is
given the value at the predecessor" suggests that an accumulator-passing loop is out of
reach.
-/

/-- The Lean definition to be expressed. -/
def fibLoopTR : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | n + 1, a, b => fibLoopTR n b (a + b)

/-- `fibTR`, the wrapper. -/
def fibTR (n : Nat) : Nat := fibLoopTR n 0 1

/-- The type the fold runs at: the two accumulators. -/
abbrev Acc2 : TyWf := TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat

/-- The base value: `fun a _ => a`. -/
def loopZero {Γ : Ctx} : Term sigAdd Γ Acc2 :=
  .lam (.lam (.var (v♯1)))

/-- The step: it binds the predecessor (index `0`) and the loop at the predecessor
    (index `1`), and answers `fun a b => loop b (a + b)`. -/
def loopStep {Γ : Ctx} : Term sigAdd (TyWf.prim .nat :: Acc2 :: Γ) Acc2 :=
  .lam (.lam
    (.ap (.ap (.var (v♯3)) (.var (v♯0))) (addT (.var (v♯1)) (.var (v♯0)))))

/-- `fibLoopTR`, as a term: a fold at a function type. -/
def loop_term {Γ : Ctx} : Term sigAdd Γ (TyWf.prim .nat ⇒ Acc2) :=
  .lam (.nat_rec 0 (.var (v♯0)) (.cons loopZero .nil) loopStep)

/-- `fibTR`, as a term: the loop started at `(0, 1)`. -/
def fibTR_term : Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  .lam (.ap (.ap (.ap (loop_term (Γ := [TyWf.prim .nat])) (.var (v♯0))) (.nat_mk 0))
    (.nat_mk 1))

/-- The term **is** `fibLoopTR`, at every argument and at both accumulators. -/
theorem loop_term_eval (n a b : Nat) : runAdd loop_term n a b = fibLoopTR n a b := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => exact ih b (a + b)

/-- `fibLoopTR` started at `(fib k, fib (k + 1))` answers `fib (n + k)` — the user's own
    invariant, which is what makes the tail-recursive loop correct. -/
theorem fibLoopTR_eq (n k : Nat) : fibLoopTR n (fib k) (fib (k + 1)) = fib (n + k) := by
  induction n generalizing k with
  | zero =>
      show fib k = fib (0 + k)
      rw [Nat.zero_add]
  | succ n ih =>
      have h : fib k + fib (k + 1) = fib (k + 2) := rfl
      show fibLoopTR n (fib (k + 1)) (fib k + fib (k + 1)) = fib (n + 1 + k)
      rw [h, ih (k + 1)]
      congr 1
      omega

/-- The tail-recursive term computes `fib`, at every argument. -/
theorem fibTR_term_eval (n : Nat) : runAdd fibTR_term n = fib n := by
  have h : runAdd fibTR_term n = runAdd loop_term n 0 1 := rfl
  rw [h, loop_term_eval]
  exact (fibLoopTR_eq n 0).trans (by rw [Nat.add_zero])

example : runAdd fibTR_term 0 = 0 := by rw [fibTR_term_eval]; rfl
example : runAdd fibTR_term 10 = 55 := by rw [fibTR_term_eval]; rfl
example : runAdd fibTR_term 20 = 6765 := by rw [fibTR_term_eval]; rfl

/-! ## 2. The pair recursion: a fold whose value is a record

```lean
def fibPair : Nat → Nat × Nat
  | 0 => (0, 1)
  | n + 1 => let (a, b) := fibPair n; (b, a + b)

def fib2 (n : Nat) : Nat := (fibPair n).1
```

This is the one-step fold at a record type, and it is **exactly** the term
`TyTests/FibWindowTest.lean` already builds: `window` is `fibPair` and `fib_term` is
`fib2`.  Nothing new is needed, and the theorem below says so in the user's own terms.
-/

/-- The Lean definition to be expressed. -/
def fibPair : Nat → Nat × Nat
  | 0 => (0, 1)
  | n + 1 =>
    let (a, b) := fibPair n
    (b, a + b)

/-- `fib2`, the wrapper. -/
def fib2 (n : Nat) : Nat := (fibPair n).1

/-- The user's own invariant: the pair at `n` is `(fib n, fib (n + 1))`. -/
theorem fibPair_eq : (n : Nat) → fibPair n = (fib n, fib (n + 1))
  | 0 => rfl
  | n + 1 => by
      rw [show fibPair (n + 1) = ((fibPair n).2, (fibPair n).1 + (fibPair n).2) from rfl,
        fibPair_eq n]
      rfl

/-- The pair recursion is the fold at a two-field record: the term of
    `TyTests/FibWindowTest.lean` computes `fibPair`, field by field. -/
theorem fibPair_term_eval (n : Nat) :
    runAdd TyTests.FibWindow.window n = ((fibPair n).1, (fibPair n).2, PUnit.unit) := by
  rw [TyTests.FibWindow.window_eval, fibPair_eq n]

/-- And its projection is `fib_term`, so `fib2` is written today. -/
theorem fib2_term_eval (n : Nat) : runAdd TyTests.FibWindow.fib_term n = fib2 n := by
  rw [TyTests.FibWindow.fib_term_eval]
  show fib n = (fibPair n).1
  rw [fibPair_eq n]

/-! ## 3. The `for` loop

```lean
def fibLoop (n : Nat) : Nat := Id.run do
  let mut a := 0
  let mut b := 1
  for _ in [:n] do
    let next := a + b
    a := b
    b := next
  return a
```

Desugared, this is `ForIn.forIn [:n] (a, b) …` in the identity monad: a fold over
`[:n]` whose state is the pair of mutable variables — that is, `fibPair` written with
different syntax, and so the *same* term as §2, at the same record type.

What is missing is therefore nothing in `Term` and nothing in `Term.eval`: it is a case
in `#leanscript_to_term` for `ForIn.forIn` on a range with a literal-free bound, turning
the loop body into the step of a `nat_rec` whose type is the record of the mutable
variables.  That case now exists — `LeanScript.ToTerm.transForInRange?` — and
`TyTests/NatRecDepthTest.lean` translates `fibLoop` as it is written.

## 4. `fib` itself

The `n + 2` pattern was the one definition of the five that the grammar could not write
directly, and it is the subject of `FibProposals.md`.  It is now the depth-two instance
of `Term.nat_rec`, written out and translated in `TyTests/NatRecDepthTest.lean`.  Two
further things are proved elsewhere in the test suite:

* `TyTests.FibWindow.fib_term_eval` — it is writable **today** as a one-step fold whose
  value is the window of the last two answers;
* `TyTests.NatRecK.natFoldK_fib` — and the depth-indexed fold the node evaluates to
  computes it directly, at `k = 1`.

## 5. `fibFast`

```lean
def fibFastAux (n : Nat) : Nat × Nat :=
  if h : n = 0 then (0, 1) else
    let (a, b) := fibFastAux (n / 2)
    …
termination_by n
```

This one is **out of reach of every proposal in the note**, and it is worth being precise
about why: the recursive call is at `n / 2`, so the argument does not descend by a fixed
number of steps, and no depth-`k` fold — window, a two-step node, or the general
`nat_rec k` — reaches it.  It is genuinely a well-founded recursion, and Lean's own elaboration says so
(`termination_by`).

There is one way to write it without well-foundedness, and it is worth recording: fast
doubling is a **fold over the binary digits of `n`, most significant first**, which is a
`recTaggedUnion_rec` over a list.  The catch is that producing those digits is itself a
recursion at `n / 2`, so the digits would have to come from a declaration in the
signature (an external `Nat.toBits`) rather than from a term.  Until the language has
well-founded recursion, that is the honest shape of the answer: the *algorithm* is a
fold, the *bit decomposition* is not.
-/

end TyTests.FibAlgorithms
