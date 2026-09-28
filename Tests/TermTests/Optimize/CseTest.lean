module

public import LeanScript.Term.Optimize.Basic
public import LeanScript.Term.Optimize.CountOptimize
public import LeanScript.Term.Build
public meta import LeanScript.TermElab.ToTerm
public meta import LeanScript.TacticElab.KernelRfl

@[expose] public section

set_option autoImplicit false

/-!
# Common subexpression elimination on `EsPrecedence01.test1`

`Tests/SnapshotsPBOPure/EsPrecedence01.lean`'s `test1` evaluates the pure `f a` three times
(and `f b`, `f ()`, which are the same call since `a b : Unit`).  The optimiser computes it
once: the number of calls (`Term.numCalls`) goes from five to one, and the value is unchanged.
-/

namespace CseTest

open LeanScript

def test1 (f : Unit → Bool) (a b : Unit) : Bool :=
  let x := if f a then f b else false
  let y := if x then f a else true
  if y then f a else f ()

def test1T := #leanscript_to_term test1

/-- The translation calls the lazy argument `f` five times; the optimised statement calls it
    once (the repeated `f a` are shared, the join points collapse), and computes `test1`. -/

example : (test1T (Δ := DSig.nil)).numCalls = 5 := by kernel_rfl
example : ((test1T (Δ := DSig.nil)).optimizeN 3).numCalls = 1 := by kernel_rfl
example (b : Bool) : ((test1T (Δ := DSig.nil)).optimizeN 3).run b = test1 (fun _ => b) () () := by
  rw [Term.optimizeN_run]; cases b <;> rfl

/-- In general the optimiser never adds calls (`Term.numCalls_optimizeN`). -/
example : ((test1T (Δ := DSig.nil)).optimizeN 3).numCalls ≤ (test1T (Δ := DSig.nil)).numCalls :=
  Term.numCalls_optimizeN 3 _

end CseTest

end
