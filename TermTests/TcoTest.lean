module

public import LeanScript.Eval
public meta import LeanScript.ToTerm
public meta import LeanScript.KernelRfl

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

`hyperBase` takes and returns numbers only, so a call of it is an extern.

For all inputs, the translations of `iter`, `hyperLoop`, `ackInner`, `ack2` and `hyperTCO`
compute the Lean functions (`iterT_run`, …).  `hyperWhile` (and `stepSum`, a loop with a start,
a step and a `break`) are checked on values: the Lean side is computed by `native_decide`
(`Std.Legacy.Range.forIn'` is well-founded recursion, which the kernel does not unfold), the
translation by the kernel (`kernel_rfl`).

The file has no public section: `ackInner` is private, and a public `ack2` could not use it.
-/

namespace Tco
open LeanScript

private def ackInner (f : Nat → Nat) : Nat → Nat
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

example : (ackInnerT (Δ := DSig.nil)).run ((fun x => x + 2 : Nat → Nat)) (3 : Nat) = ackInner (fun x => x + 2) 3 := rfl
example : (ack2T (Δ := DSig.nil)).run (2 : Nat) (3 : Nat) = ack2 2 3 := by kernel_rfl
example : (hyperLoopT (Δ := DSig.nil)).run ((fun x => 2 * x : Nat → Nat)) (5 : Nat) (1 : Nat) = hyperLoop (fun x => 2 * x) 5 1 := rfl
example : (hyperTCOT (Δ := DSig.nil)).run (1 : Nat) (2 : Nat) (3 : Nat) = hyperTCO 1 2 3 := by kernel_rfl
example : (hyperWhileT (Δ := DSig.nil)).run (1 : Nat) (2 : Nat) (3 : Nat) = hyperWhile 1 2 3 := by
  rw [show hyperWhile 1 2 3 = 5 by native_decide]; kernel_rfl
example : (hyperTCOT (Δ := DSig.nil)).run (3 : Nat) (2 : Nat) (3 : Nat) = hyperTCO 3 2 3 := by kernel_rfl
example : (hyperWhileT (Δ := DSig.nil)).run (3 : Nat) (2 : Nat) (3 : Nat) = hyperWhile 3 2 3 := by
  rw [show hyperWhile 3 2 3 = 8 by native_decide]; kernel_rfl
example : (iterT (Δ := DSig.nil)).run ((fun x => x + 3 : Nat → Nat)) (4 : Nat) (1 : Nat) = iter (fun x => x + 3) 4 1 := rfl

/-! ## A `for` loop over a range with a start, a step and a `break` -/

def stepSum (a b : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [a:b:3] do
    if acc > 20 then break
    acc := acc + i
  return acc

def stepSumT := #leanscript_to_term stepSum

example : (stepSumT (Δ := DSig.nil)).run (2 : Nat) (30 : Nat) = stepSum 2 30 := by
  rw [show stepSum 2 30 = 26 by native_decide]; kernel_rfl
example : (stepSumT (Δ := DSig.nil)).run (5 : Nat) (12 : Nat) = stepSum 5 12 := by
  rw [show stepSum 5 12 = 24 by native_decide]; kernel_rfl
example : (stepSumT (Δ := DSig.nil)).run (7 : Nat) (3 : Nat) = stepSum 7 3 := by
  rw [show stepSum 7 3 = 0 by native_decide]; kernel_rfl

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

theorem hyperTCOT_run (n a b : Nat) :
    (hyperTCOT (Δ := DSig.nil)).run n a b = hyperTCO n a b := by
  have key : ∀ n b, natIter (fun b => b + 1)
      (fun k r b => natIter (fun x => x) (fun _ s x => s (r x)) b (hyperBase (k + 1) a)) n b =
      hyperTCO n a b := by
    intro n; induction n with
    | zero => intro b; rfl
    | succ n ih =>
      intro b
      have : (natIter (fun b => b + 1) (fun k r b =>
          natIter (fun x => x) (fun _ s x => s (r x)) b (hyperBase (k + 1) a)) n) = hyperTCO n a :=
        funext ih
      simp only [hyperLoop_natIter] at this
      simp only [natIter, hyperLoop_natIter, this, hyperTCO]
  exact key n b

end Tco

