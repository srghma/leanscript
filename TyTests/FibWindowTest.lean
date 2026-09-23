module

public import LeanScript.Eval

@[expose] public section

/-!
# `fib` in the grammar as it stands: the sliding-window fold

`FibProposals.md` proposes five ways to give the language a recursion that descends more
than one step at a time.  This file *runs* the first of them, the one that needs no new
constructor (the grammar has since gained the depth-indexed node as well): a recursion that reads its own value at `n` and at `n + 1` is a fold whose
value is the **window** of the last two answers, a record of two `nat`s, and the answer
is the first field of that window.

Everything here is a term of the grammar exactly as it is today — `Term.nat_rec`,
`Term.record_mk`, `Term.record_casesOn` — and `fib_term_eval` proves that the term's
value **is** `fib n`, at every `n`, rather than only at the arguments a test would try.
-/

namespace TyTests.FibWindow

open LeanScript

/-- The definition to be expressed: it reads its own value at `n` and at `n + 1`.  Since
    this file was written the grammar has gained the depth-indexed fold
    `Term.nat_rec k`, so `#leanscript_to_term` translates it directly
    (`TyTests/NatRecDepthTest.lean`); what is written here is the *other* way of saying
    it, as a one-step fold whose value is a window, and it still typechecks and still
    computes `fib`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- A signature with one declaration, `add : nat ⇒ nat ⇒ nat`: the language's arithmetic
    is external, so the step of the fold calls it. -/
def sigAdd : Sig := ⟨[⟨"add", TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat⟩], by decide⟩

/-- The values of the declarations of `sigAdd`. -/
def envAdd : GlobalEnv sigAdd.decls := (Nat.add, PUnit.unit)

/-- Running a closed term of `sigAdd`. -/
local macro:max "runAdd" t:term:max : term => `(Term.run (Sg := sigAdd) envAdd $t)

/-- The window: the pair `(fib n, fib (n + 1))`. -/
abbrev winSchema : LeanRecordSchema TyWf := ⟨TyWf.prim .nat, TyWf.prim .nat, []⟩

/-- The type of the window. -/
abbrev Win : TyWf := TyWf.record winSchema

/-- `add a b`, for two terms in hand. -/
def addT {Γ : Ctx} (a b : Term sigAdd Γ (TyWf.prim .nat)) : Term sigAdd Γ (TyWf.prim .nat) :=
  .ap (.ap (.global .here) a) b

/-- The window at `0`: `(fib 0, fib 1) = (0, 1)`.  These are the base branches of the
    Lean definition, which read nothing of the recursion. -/
def seed {Γ : Ctx} : Term sigAdd Γ Win :=
  .record_mk winSchema (.cons (.nat_mk 0) (.cons (.nat_mk 1) .nil))

/-- The step of the fold: it binds the predecessor `k` (index `0`) and the window at `k`
    (index `1`), takes the window apart — so inside, index `0` is `fib k` and index `1`
    is `fib (k + 1)` — and answers with the window at `k + 1`,
    `(fib (k + 1), fib k + fib (k + 1))`.

    The recursion that the branch of the Lean definition writes at `n` and at `n + 1` is
    read off the window: nothing is called, so the term is still terminating by
    construction. -/
def step {Γ : Ctx} : Term sigAdd (TyWf.prim .nat :: Win :: Γ) Win :=
  .record_casesOn (.var (v♯1))
    (.record_mk winSchema
      (.cons (.var (v♯1)) (.cons (addT (.var (v♯0)) (.var (v♯1))) .nil)))

/-- The fold itself: the window at the argument. -/
def window {Γ : Ctx} : Term sigAdd Γ (TyWf.prim .nat ⇒ Win) :=
  .lam (.nat_rec 0 (.var (v♯0)) (.cons seed .nil) step)

/-- `fib`, as a term of the language: the first field of the window. -/
def fib_term : Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  .lam (.record_casesOn (fs := winSchema) (.ap window (.var (v♯0))) (.var (v♯0)))

/-! ## What it computes

First a few values, checked by the kernel, and then the general statement. -/

example : runAdd fib_term 0 = 0 := rfl
example : runAdd fib_term 1 = 1 := rfl
example : runAdd fib_term 2 = 1 := rfl
example : runAdd fib_term 10 = 55 := rfl

example : runAdd fib_term 12 = fib 12 := rfl
example : runAdd fib_term 15 = 610 := rfl

/-- The window term's value at `n` is the pair `(fib n, fib (n + 1))` — at **every**
    argument, not only at the ones checked above. -/
theorem window_eval (n : Nat) :
    runAdd window n = (fib n, fib (n + 1), PUnit.unit) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hstep : runAdd window (n + 1) =
          ((runAdd window n).2.1,
            (runAdd window n).1 + (runAdd window n).2.1, PUnit.unit) := rfl
      rw [hstep, ih]
      show ((fib (n + 1), fib n + fib (n + 1), PUnit.unit) : Nat × Nat × PUnit) =
        (fib (n + 1), fib (n + 2), PUnit.unit)
      rw [show fib (n + 2) = fib n + fib (n + 1) from rfl]

/-- `fib_term` computes `fib`, at every argument. -/
theorem fib_term_eval (n : Nat) : runAdd fib_term n = fib n := by
  have h : runAdd fib_term n = (runAdd window n).1 := rfl
  rw [h, window_eval]

/-! ## The semantics a two-step fold would have

`FibProposals.md`'s second proposal adds a constructor `Term.nat_rec2` whose branch is
given the value of the recursion at the **two** predecessors.  Its clause in the
evaluator would be the fold below, and the point of writing it here is that it is
*linear*: the fold carries the window internally, so a branch that reads both
predecessors still costs one step per number, which a naive double recursion would not.

`natFold2_succ_succ` is the equation such a constructor promises, and it is proved, so
the design is checked rather than asserted. -/

/-- The window of a two-step fold: `(f n, f (n + 1))`. -/
def natFold2Aux {α : Type} (z0 z1 : α) (s : Nat → α → α → α) : Nat → α × α
  | 0 => (z0, z1)
  | n + 1 => let w := natFold2Aux z0 z1 s n; (w.2, s n w.1 w.2)

/-- `Nat.rec` that descends two steps: the value at `n + 2` is the branch applied to the
    values at `n` and at `n + 1`. -/
def natFold2 {α : Type} (z0 z1 : α) (s : Nat → α → α → α) (n : Nat) : α :=
  (natFold2Aux z0 z1 s n).1

@[simp] theorem natFold2_zero {α : Type} (z0 z1 : α) (s : Nat → α → α → α) :
    natFold2 z0 z1 s 0 = z0 := rfl

@[simp] theorem natFold2_one {α : Type} (z0 z1 : α) (s : Nat → α → α → α) :
    natFold2 z0 z1 s 1 = z1 := rfl

/-- The equation the proposed constructor promises: the branch at `n + 2` is given the
    value at `n` and the value at `n + 1`. -/
theorem natFold2_succ_succ {α : Type} (z0 z1 : α) (s : Nat → α → α → α) (n : Nat) :
    natFold2 z0 z1 s (n + 2) = s n (natFold2 z0 z1 s n) (natFold2 z0 z1 s (n + 1)) := rfl

/-- And it does compute `fib`. -/
theorem natFold2_fib (n : Nat) : natFold2 0 1 (fun _ a b => a + b) n = fib n := by
  induction n using fib.induct with
  | case1 => rfl
  | case2 => rfl
  | case3 n ih1 ih2 =>
      rw [natFold2_succ_succ, ih1, ih2]
      rfl

end TyTests.FibWindow
