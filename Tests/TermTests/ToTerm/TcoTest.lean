module

public import LeanScript.Term.Build
public meta import LeanScript.TermElab.ToTerm
public meta import LeanScript.TacticElab.KernelRfl

@[expose] public section

set_option autoImplicit false

/-!
# `#leanscript_to_term` on higher-order and tail-recursive functions

The definitions of `TcoAck.lean`, `TcoHyper.lean` and `TcoMc91.lean`, translated:

* `hyperLoop`, `iter`: the recursive call changes the accumulator, so the fold (`nat_rec`)
  answers a function of it;
* `hyperTCO`: the recursive call `hyperTCO n a` is partially applied (it leaves out `b`), and
  it is passed to the helper `hyperLoop`, whose own translation is used;
* `ack2`: returns a function; the helper `ackInner` is translated and applied;
* `hyperWhile`: a `for` loop over `[0:b]` in `Id`, a `nat_rec` over the steps of the loop.

`hyperBase` is a helper too: a call of it is a call of its own translation (only library
functions that are the Lean functions of entries of the catalogue are externs).

For all inputs, the translations of `iter`, `hyperLoop`, `ackInner`, `ack2`, `hyperBase` and
`hyperTCO` compute the Lean functions (`iterT_run`, …).  `hyperWhile` (and `stepSum`, a loop
with a start, a step and a `break`) are checked on values.

The checks on values (`ack2T.run 2 3 = ack2 2 3`, `hyperWhileT.run 3 2 3 = hyperWhile 3 2 3`,
…) are slow in the kernel: `Term.eval` unfolds through the structural recursors of the term
families (`brecOn` and its `below` tuples), and a `nat_rec` over `n` through `n` steps of
`natIter`.  They are run compiled, by `Tests/Main.lean` (`lake test`), which needs the
definitions here: so everything here is public.
-/

namespace Tco
open LeanScript

def ackInner (f : Nat → Nat) : Nat → Nat
  | 0     => f 1
  | n + 1 => f (ackInner f n)

def ack2 : Nat → (Nat → Nat)
  | 0     => fun n => n + 1
  | m + 1 => ackInner (ack2 m)

def hyperLoop (f : Nat → Nat) : Nat → Nat → Nat
  | 0,     acc => acc
  | b + 1, acc => hyperLoop f b (f acc)

def hyperBase : Nat → Nat → Nat
  | 0,     _ => 1
  | 1,     a => a
  | 2,     _ => 0
  | _ + 3, _ => 1

def hyperTCO : Nat → Nat → Nat → Nat
  | 0,     _, b => b + 1
  | n + 1, a, b => hyperLoop (hyperTCO n a) b (hyperBase (n + 1) a)

def hyperWhile : Nat → Nat → Nat → Nat
  | 0,     _, b => b + 1
  | n + 1, a, b => Id.run do
    let mut acc := hyperBase (n + 1) a
    for _ in [0:b] do
      acc := hyperWhile n a acc
    return acc

def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0,     x => x
  | c + 1, x => iter f c (f x)

def ackInnerT := #leanscript_to_term ackInner
def ack2T := #leanscript_to_term ack2
def hyperLoopT := #leanscript_to_term hyperLoop
def hyperBaseT := #leanscript_to_term hyperBase
def hyperTCOT := #leanscript_to_term hyperTCO
def hyperWhileT := #leanscript_to_term hyperWhile
def iterT := #leanscript_to_term iter

-- (moved to `Tests/Main.lean`: too slow for the kernel, run compiled)

/-! ## A `for` loop over a range with a start, a step and a `break` -/

def stepSum (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [a:b:3] do
    if acc > 20 then break
    acc := acc + i
  return acc

def stepSumT := #leanscript_to_term stepSum

-- (moved to `Tests/Main.lean`: too slow for the kernel, run compiled)

#eval stepSum 2 30
#eval stepSum 5 12
#eval ack2 2 3
#eval hyperWhile 1 2 3
#eval hyperTCO 3 2 3
#eval hyperWhile 3 2 3

end Tco

namespace Tco
open LeanScript

theorem iterT_run (f : Nat → Nat) (c x : Nat) :
    (iterT (Δ := DSig.nil)).run f c x = iter f c x := by
  have key : ∀ c x, natIter (fun x => x) (fun _ r x => r (f x)) c x = iter f c x := by
    intro c; induction c <;> intro x <;> simp_all [natIter, iter]
  exact key c x

theorem ackInner_natIter (f : Nat → Nat) (n : Nat) :
    natIter (f 1) (fun _ r => f r) n = ackInner f n := by
  induction n <;> simp_all [natIter, ackInner]

theorem hyperLoop_natIter (f : Nat → Nat) (b acc : Nat) :
    natIter (fun x => x) (fun _ r x => r (f x)) b acc = hyperLoop f b acc := by
  induction b generalizing acc <;> simp_all [natIter, hyperLoop]

theorem hyperLoopT_run (f : Nat → Nat) (b acc : Nat) :
    (hyperLoopT (Δ := DSig.nil)).run f b acc = hyperLoop f b acc :=
  hyperLoop_natIter f b acc

theorem ackInnerT_run (f : Nat → Nat) (n : Nat) :
    (ackInnerT (Δ := DSig.nil)).run f n = ackInner f n :=
  ackInner_natIter f n

theorem ack2T_run (m n : Nat) : (ack2T (Δ := DSig.nil)).run m n = ack2 m n := by
  have key : ∀ m, natIter (fun n => n + 1)
      (fun _ r => fun n => natIter (r 1) (fun _ s => r s) n) m = ack2 m := by
    intro m; induction m with
    | zero => rfl
    | succ m ih =>
      simp only [ackInner_natIter] at ih
      funext n; simp only [natIter, ackInner_natIter, ih, ack2]
  exact congrFun (key m) n

/-- The translation of `hyperBase` (a helper: its match on `0`, `1`, `2`, `_ + 3` is a nest of
    `nat_rec`s) computes `hyperBase`. -/
theorem hyperBaseT_run (k a : Nat) : (hyperBaseT (Δ := DSig.nil)).run k a = hyperBase k a := by
  rcases k with _ | _ | _ | k <;> rfl

/-- The translation of `hyperTCO` computes `hyperTCO`.

    The translated term is first evaluated **by the kernel** (`kernel_rfl`), with the
    arguments left as variables, to its shape: two nested `natIter`s, the inner one on the
    translation of the helper `hyperBase`.  The elaborator's own check of this equation
    (`refine`/`rfl`, which must also *find* the function of the helper by higher-order
    unification) took ~30 s and 4 000 000 heartbeats; the kernel's takes a fraction of a
    second.  The rest is an induction on the Lean side only. -/
theorem hyperTCOT_run (n a b : Nat) :
    (hyperTCOT (Δ := DSig.nil)).run n a b = hyperTCO n a b := by
  have e : @Eq Nat ((hyperTCOT (Δ := DSig.nil)).run n a b) <| natIter (α := Nat → Nat)
      (fun b => b + 1) (fun k r b => natIter (α := Nat → Nat) (fun x => x) (fun _ s x => s (r x))
        b ((hyperBaseT (Δ := DSig.nil)).run (k + 1 : Nat) a)) n b := by kernel_rfl
  have key : ∀ n, natIter (α := Nat → Nat) (fun b => b + 1)
      (fun k r b => hyperLoop r b (hyperBase (k + 1) a)) n = hyperTCO n a := by
    intro n; induction n with
    | zero => funext b; rfl
    | succ n ih => funext b; simp only [natIter, ih, hyperTCO]
  rw [e]
  simp only [hyperBaseT_run, hyperLoop_natIter]
  exact congrFun (key n) b

end Tco

end
