module

public import LeanScript.NatRecFacts
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-!
# A recursion that descends more than one step, written and translated

`LeanScript.Term.nat_rec k` is the fold of a natural number that descends `k + 1` steps.
Its base values are the answers at `k, …, 1, 0` — **nearest first** — and its branch, at
`n + k + 1`, binds `n` (de Bruijn index `0`) and then the answers at `n + k, …, n + 1, n`
(indices `1 … k + 1`).  The depth defaults to `0`, at which the node is `Nat.rec` with a
non-dependent motive.

This file checks the node from both ends:

* **written out.**  `fibTerm` is `fib` as a term of the grammar, at depth two, and
  `fibTerm_eval` proves that its value is `fib n` at **every** `n` — by the two equations
  of `LeanScript.NatRecFacts`, not by testing.
* **translated.**  Each of the Fibonacci programs of the request is handed to
  `#leanscript_to_term` as it is written, and the kernel checks the value of the term it
  produces: the two-step `fib`, the tail-recursive loop, the pair recursion, the `for`
  loop over a range, and the tribonacci … hexanacci numbers, which descend three to six
  steps.  The one program that is refused is `fibFast`, whose recursive call is at
  `n / 2`: that is not a descent by a fixed number of steps, and no fold of this kind can
  express it.
-/

namespace TyTests.NatRecDepth

open LeanScript

/-- A signature with one declaration, `add : nat ⇒ nat ⇒ nat`: arithmetic is external to
    the language, so every one of these programs calls it. -/
def sigAdd : Sig := ⟨[⟨"add", TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat⟩], by decide⟩

/-- The values of the declarations of `sigAdd`. -/
def envAdd : GlobalEnv sigAdd.decls := (Nat.add, PUnit.unit)

/-- Running a closed term of `sigAdd`. -/
local macro:max "runAdd" t:term:max : term => `(Term.run (Sg := sigAdd) envAdd $t)

/-- `add a b`, for two terms in hand. -/
def addT {Γ : Ctx} (a b : Term sigAdd Γ (TyWf.prim .nat)) : Term sigAdd Γ (TyWf.prim .nat) :=
  .ap (.ap (.global .here) a) b

/-- The definition every term below computes. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-! ## `fib`, written out at depth two

The base values are `(fib 1, fib 0) = (1, 0)`, nearest first, and the branch at `n + 2`
binds `n` at index `0`, `fib (n + 1)` at index `1` and `fib n` at index `2`. -/

/-- `fib`, as a term of the grammar: the depth-two fold. -/
def fibTerm : Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  .lam (.nat_rec 1 (.var (v♯0))
    (.cons (.nat_mk 1) (.cons (.nat_mk 0) .nil))
    (addT (.var (v♯2)) (.var (v♯1))))

example : runAdd fibTerm 0 = 0 := rfl
example : runAdd fibTerm 1 = 1 := rfl
example : runAdd fibTerm 10 = 55 := rfl

/-- The fold the term evaluates to, named so that the two equations can be read off it:
    its base window is `(1, 0)` and its branch adds the two answers the window holds. -/
def fibFold : Nat → Nat :=
  natFoldK (τ := TyWf.prim .nat) (k := 1) (1, 0, PUnit.unit) (fun _ w => w.2.1 + w.1)

/-- The term's value **is** that fold, at every argument. -/
theorem fibTerm_eq_fibFold (n : Nat) : runAdd fibTerm n = fibFold n := rfl

/-- The base equation, read off `natFoldK_base`: below the depth the answer is the base
    value written for the argument. -/
theorem fibFold_zero : fibFold 0 = 0 :=
  natFoldK_base (τ := TyWf.prim .nat) (k := 1) _ _ 0 (by omega)

theorem fibFold_one : fibFold 1 = 1 :=
  natFoldK_base (τ := TyWf.prim .nat) (k := 1) _ _ 1 (by omega)

/-- The step equation, read off `natFoldK_step`: at `n + 2` the branch is given the
    answers at `n` and at `n + 1`. -/
theorem fibFold_step (n : Nat) : fibFold (n + 2) = fibFold n + fibFold (n + 1) :=
  natFoldK_step (τ := TyWf.prim .nat) (k := 1) _ _ n

/-- **The term computes `fib`, at every argument** — not only at the ones checked by
    `rfl` above. -/
theorem fibTerm_eval (n : Nat) : runAdd fibTerm n = fib n := by
  rw [fibTerm_eq_fibFold]
  induction n using fib.induct with
  | case1 => exact fibFold_zero
  | case2 => exact fibFold_one
  | case3 n ih0 ih1 =>
      rw [show n.succ.succ = n + 2 from rfl, fibFold_step, ih0, ih1]
      rfl

/-! ## The same definitions, translated

`#leanscript_to_term` reads the depth off the compiled recursion: it is the smallest
number of steps at which the history the `brecOn` hands the branch is fully read. -/

/-- `fib` as the request writes it. -/
def fibDef : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fibDef n + fibDef (n + 1)

def fibDef_term : Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term fibDef

example : runAdd fibDef_term 0 = 0 := rfl
example : runAdd fibDef_term 1 = 1 := rfl
example : runAdd fibDef_term 12 = fibDef 12 := rfl

/-! ### `fibLoopTR` and `fibTR`: the accumulator-passing loop

The recursion descends one step, but its accumulators change on the way down, so the
value of the fold is the **function** of the two accumulators.  The node folds at any
type, function types included, so this is the depth-zero instance. -/

@[inline] def fibLoopTR : Nat → Nat → Nat → Nat
  | 0,     a, _ => a
  | n + 1, a, b => fibLoopTR n b (a + b)

def fibLoopTR_term :
    Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term fibLoopTR

example : runAdd fibLoopTR_term 0 0 1 = 0 := rfl
example : runAdd fibLoopTR_term 1 0 1 = 1 := rfl

/-- `fibTR n = fibLoopTR n 0 1`, which is the loop applied to the two starting
    accumulators.  The value of this fold is a *function*, so the kernel has a closure to
    reduce at every step and the checks are kept small. -/
example : runAdd fibLoopTR_term 3 0 1 = 2 := rfl

/-- And the wrapper itself: `fibLoopTR` is marked `@[inline]`, so the call is built in
    place and `fibTR` translates as it is written. -/
def fibTR (n : Nat) : Nat := fibLoopTR n 0 1

def fibTR_term : Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term fibTR

example : runAdd fibTR_term 0 = 0 := rfl
example : runAdd fibTR_term 1 = 1 := rfl

/-! ### `fibPair` and `fib2`: the fold at a pair

A `Nat × Nat` is a record of two fields here, so the fold runs at that record and the
answer is its first field. -/

def fibPair : Nat → Nat × Nat
  | 0 => (0, 1)
  | n + 1 =>
    let (a, b) := fibPair n
    (b, a + b)

def fibPair_term : Term sigAdd [] (TyWf.prim .nat ⇒ tyWfOf (Nat × Nat)) :=
  #leanscript_to_term fibPair

example : runAdd fibPair_term 0 = ((0, 1, PUnit.unit) : Nat × Nat × PUnit) := rfl
example : runAdd fibPair_term 6 = ((8, 13, PUnit.unit) : Nat × Nat × PUnit) := rfl

/-! ### `fibLoop`: the `for` loop

`do` in the identity monad is not an effect, and a `for` over `[:n]` is the fold of `n`
whose value is the state of the loop — the depth-zero node again, at the record of the
two mutable variables. -/

def fibLoop (n : Nat) : Nat := Id.run do
  let mut a := 0
  let mut b := 1
  for _ in [:n] do
    let next := a + b
    a := b
    b := next
  return a

def fibLoop_term : Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term fibLoop

example : runAdd fibLoop_term 0 = 0 := rfl
example : runAdd fibLoop_term 1 = 1 := rfl
example : runAdd fibLoop_term 4 = 3 := rfl

/-! ### Three steps and more

The depth is not fixed by the grammar, so the whole family translates: the tribonacci
numbers descend three steps, the tetranacci four, the pentanacci five and the hexanacci
six. -/

def tribonacci : Nat → Nat
  | 0     => 0
  | 1     => 0
  | 2     => 1
  | n + 3 => tribonacci n + tribonacci (n + 1) + tribonacci (n + 2)

def tribonacci_term : Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term tribonacci

example : runAdd tribonacci_term 2 = 1 := rfl
example : runAdd tribonacci_term 10 = tribonacci 10 := rfl

def tetranacci : Nat → Nat
  | 0     => 0
  | 1     => 0
  | 2     => 0
  | 3     => 1
  | n + 4 => tetranacci n + tetranacci (n + 1) + tetranacci (n + 2) + tetranacci (n + 3)

def tetranacci_term : Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term tetranacci

example : runAdd tetranacci_term 3 = 1 := rfl
example : runAdd tetranacci_term 8 = tetranacci 8 := rfl

def pentanacci : Nat → Nat
  | 0     => 0
  | 1     => 0
  | 2     => 0
  | 3     => 0
  | 4     => 1
  | n + 5 => pentanacci n + pentanacci (n + 1) + pentanacci (n + 2)
           + pentanacci (n + 3) + pentanacci (n + 4)

def pentanacci_term : Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term pentanacci

example : runAdd pentanacci_term 4 = 1 := rfl
example : runAdd pentanacci_term 8 = pentanacci 8 := rfl

def hexanacci : Nat → Nat
  | 0     => 0
  | 1     => 0
  | 2     => 0
  | 3     => 0
  | 4     => 0
  | 5     => 1
  | n + 6 => hexanacci n + hexanacci (n + 1) + hexanacci (n + 2)
           + hexanacci (n + 3) + hexanacci (n + 4) + hexanacci (n + 5)

def hexanacci_term : Term sigAdd [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term hexanacci

example : runAdd hexanacci_term 5 = 1 := rfl

-- The kernel check is the same as the ones above; only the elaborator's `isDefEq` budget
-- is raised, because the six-deep window makes this the largest of them.
set_option maxHeartbeats 1000000 in
example : runAdd hexanacci_term 8 = hexanacci 8 := rfl

/-! ## What is still refused

`fibFast` calls itself at `n / 2`.  That is not a descent by a fixed number of steps, so
no depth makes it a fold of this kind; Lean compiles it by well-founded recursion, which
the translation refuses. -/

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

/-- error: `#leanscript_to_term`: well-founded recursion (WellFounded.Nat.fix) is not supported — the only folds the translation produces are `nat_rec` and `recTaggedUnion_rec`, so write the recursion as `Nat.rec` or `List.rec` with a non-dependent motive -/
#guard_msgs (error) in
example : Term sigAdd [] (TyWf.prim .nat ⇒ tyWfOf (Nat × Nat)) :=
  #leanscript_to_term fibFastAux

end TyTests.NatRecDepth

end
