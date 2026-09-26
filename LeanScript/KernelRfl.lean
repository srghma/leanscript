module

public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.AppBuilder

public section

/-!
# `kernel_rfl`: an equation checked by the kernel only

`rfl` (the term, or the tactic) first asks the elaborator's definitional-equality check
whether the two sides agree, and only then hands the proof to the kernel.  For a
large evaluation (a program run by `Term.eval`) the elaborator's check can be much slower
than the kernel's.  It is
also the check that counts heartbeats.

`kernel_rfl` closes a goal `a = b` with `Eq.refl a` **without** that first check.  It is
sound: the kernel type-checks the finished declaration, so if `a` and `b` are not
definitionally equal the declaration is rejected (with a kernel error at the declaration,
not at the tactic).  Use it where `rfl` is correct but slow; for a *closed* proposition
`decide +kernel` does the same job.
-/

namespace LeanScript

open Lean Elab Tactic Meta in
/-- Close a goal `a = b` by `Eq.refl a`, leaving the check that `a` and `b` are
    definitionally equal to the kernel alone (see the module doc). -/
elab "kernel_rfl" : tactic => liftMetaTactic fun g => do
  let t ← whnfR (← g.getType)
  let some (_, lhs, _) := t.eq? | throwError "kernel_rfl: the goal is not an equation{indentExpr t}"
  g.assign (← mkEqRefl lhs)
  return []

end LeanScript

end
