module

public import LeanScript.Term.Rewrite.SimpStep
public import TermTests.Optimize.OptimizeTest

@[expose] public section

set_option autoImplicit false

/-!
# The rewrites of normal-form terms (`Term.Step`) on small statements

The optimiser's rewriting pass is a rewrite sequence (`Term.simp_star`), so the rewrites of
`OptimizeTest` are sequences of `Term.Step`; a single step is also built by hand, and the
Church–Rosser property gives a common reduct with the value of both sides.
-/

namespace ChurchRosserTest

open LeanScript LeanScript.Rewriting OptimizeTest

/-- `fun n => let a := share (n * 7); a` rewrites to `fun n => n * 7`. -/
example : Star Term.Step sharedTail sharedTailOpt := by
  have h := Term.simp_star sharedTail
  have e : sharedTail.simp = sharedTailOpt := by rfl
  rwa [e] at h

/-- The same rewrite, as a single step inside the closure. -/
example : Term.Step sharedTail sharedTailOpt :=
  .letV_val _ _ (.lam (.closed (.share_ret _ _ rfl rfl rfl)))

/-- Two statements related by rewrites have a common reduct, with the same result. -/
example : ∃ t₃, Star Term.Step sharedTail t₃ ∧ Star Term.Step sharedTailOpt t₃ ∧
    t₃.run = sharedTail.run ∧ t₃.run = sharedTailOpt.run :=
  Term.run_churchRosser (.fwd (.letV_val _ _ (.lam (.closed (.share_ret _ _ rfl rfl rfl)))))

end ChurchRosserTest

end
