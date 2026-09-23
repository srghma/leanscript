module

public import LeanScript.Eval

@[expose] public section

/-!
# `fib` in the grammar as it stands: the sliding-window fold

`FibProposals.md` proposes four ways to give the language a recursion that descends more
than one step at a time.  This file *runs* the first of them, the one that needs no new
constructor: a recursion that reads its own value at `n` and at `n + 1` is a fold whose
value is the **window** of the last two answers, a record of two `nat`s, and the answer
is the first field of that window.

Everything here is a term of the grammar exactly as it is today — `Term.nat_rec`,
`Term.record_mk`, `Term.record_casesOn` — and the check at the end is by the kernel: the
term's value is the one Lean's `fib` has.
-/

namespace TyTests.FibWindow

open LeanScript

/-- The definition to be expressed: it reads its own value at `n` and at `n + 1`, so it
    is the example `#leanscript_to_term` refuses today. -/
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
  .lam (.nat_rec (.var (v♯0)) seed step)

/-- `fib`, as a term of the language: the first field of the window. -/
def fib_term : Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  .lam (.record_casesOn (fs := winSchema) (.ap window (.var (v♯0))) (.var (v♯0)))

/-! ## What it computes

The kernel checks, by `rfl`, that the term's value is the one Lean's `fib` has. -/

example : runAdd fib_term 0 = 0 := rfl
example : runAdd fib_term 1 = 1 := rfl
example : runAdd fib_term 2 = 1 := rfl
example : runAdd fib_term 10 = 55 := rfl

example : runAdd fib_term 12 = fib 12 := rfl
example : runAdd fib_term 15 = 610 := rfl

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


def fib : Nat → Nat
| 0 => 0
| 1 => 1
| n + 2 => fib n + fib (n + 1)

#eval fib 10

#print fib

def fibLoopTR : Nat → Nat → Nat → Nat
  | 0,     a, _ => a
  | n + 1, a, b => fibLoopTR n b (a + b)

#print fibLoopTR

def fibTR (n : Nat) : Nat :=
  fibLoopTR n 0 1

#eval fibTR 10

def fibLoop (n : Nat) : Nat := Id.run do
  let mut a := 0
  let mut b := 1
  for _ in [:n] do
    let next := a + b
    a := b
    b := next
  return a

#print fibLoop

#eval fibLoop 100

def fibPair : Nat → Nat × Nat
  | 0 => (0, 1)
  | n + 1 =>
    let (a, b) := fibPair n
    (b, a + b)

#print fibPair
def fib2 (n : Nat) : Nat :=
  (fibPair n).1

#eval fib 10

def fibFastAux (n : Nat) : Nat × Nat :=
  if h : n = 0 then
    (0, 1)
  else
    have : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
    let (a, b) := fibFastAux (n / 2)
    let c := a * (2 * b - a)
    let d := a * a + b * b
    if n % 2 == 0 then
      (c, d)
    else
      (d, c + d)
termination_by n

#print fibFastAux

def fibFast (n : Nat) : Nat :=
  (fibFastAux n).1

#eval fibFast 100000  -- Computes almost instantly

theorem fibPair_eq (n : Nat) : fibPair n = (fib n, fib (n + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [fibPair, ih]
    -- fib (n + 2) is definitionally equal to fib n + fib (n + 1)
    rfl

-- Main theorem:
theorem fibPair_fst_eq_fib (n : Nat) : (fibPair n).1 = fib n := by
  rw [fibPair_eq]

theorem fibLoopTR_eq (n k : Nat) :
    fibLoopTR n (fib k) (fib (k + 1)) = fib (n + k) := by
  induction n generalizing k with
  | zero =>
    grind [= fibLoopTR, = fib]
  | succ n ih =>
    -- Step 1: fib k + fib (k + 1) is definitionally fib (k + 2)
    have h : fib k + fib (k + 1) = fib (k + 2) := rfl
    -- Step 2: Unfold one iteration of the loop
    rw [fibLoopTR, h]
    -- Step 3: Apply induction hypothesis with (k + 1)
    rw [ih (k + 1)]
    -- Step 4: Show (n + (k + 1)) = ((n + 1) + k)
    congr 1
    omega

-- Main theorem: set k = 0
theorem fibTR_eq_fib (n : Nat) : fibTR n = fib n := by
  have h : fibTR n = fibLoopTR n (fib 0) (fib 1) := rfl
  rw [h, fibLoopTR_eq n 0]
  rw [Nat.add_zero]


def tribonacci : Nat → Nat
  | 0     => 0
  | 1     => 0
  | 2     => 1
  | n + 3 => tribonacci n + tribonacci (n + 1) + tribonacci (n + 2)

#print tribonacci

def tetranacci : Nat → Nat
  | 0     => 0
  | 1     => 0
  | 2     => 0
  | 3     => 1
  | n + 4 => tetranacci n + tetranacci (n + 1) + tetranacci (n + 2) + tetranacci (n + 3)

#print tetranacci

def pentanacci : Nat → Nat
  | 0     => 0
  | 1     => 0
  | 2     => 0
  | 3     => 0
  | 4     => 1
  | n + 5 => pentanacci n + pentanacci (n + 1) + pentanacci (n + 2)
           + pentanacci (n + 3) + pentanacci (n + 4)

#print pentanacci

def hexanacci : Nat → Nat
  | 0     => 0
  | 1     => 0
  | 2     => 0
  | 3     => 0
  | 4     => 0
  | 5     => 1
  | n + 6 => hexanacci n + hexanacci (n + 1) + hexanacci (n + 2)
           + hexanacci (n + 3) + hexanacci (n + 4) + hexanacci (n + 5)

#print hexanacci

def sumList (l : List Nat) : Nat :=
  l.foldr (· + ·) 0

#print List.foldr
#print sumList
