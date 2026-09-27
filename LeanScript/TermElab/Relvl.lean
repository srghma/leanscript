module

public import LeanScript.Term.Build
public meta import Lean.Elab.Term
public meta import Lean.Elab.SyntheticMVars

@[expose] public section

set_option autoImplicit false

/-!
# `ls_relvl% e`: elaborating a normal form against its expected type, level last

The level index of a normal-form statement (`LeanScript.Term`, `PExpr`, `Neu`, …) is computed
by its constructors (`Lvl.meet o o'`, …).  When the expected type fixes the level (`none`, say)
the elaborator cannot propagate it into such a constructor (`Lvl.meet ?o ?o' =?= none` has no
first-order solution), and so it propagates *nothing*: not the signature, not the contexts.
Elaborating a term whose contexts are not known yet can then fail (a variable of a case
analysis, whose context is computed from the constructor's fields).

`ls_relvl% e` elaborates `e` against the expected type with its **last index** (the level)
replaced by a fresh metavariable, so that everything else propagates, and only then checks
the level.
-/

namespace LeanScript.Relvl

open Lean Meta Elab Term

/-- `ls_relvl% e`: elaborate `e` against its expected type, the last index (the level) left
    to unification until the end. -/
syntax (name := lsRelvl) "ls_relvl% " term:max : term

/-- Replace the last argument of an application by a fresh metavariable (of the same type). -/
meta def relaxLast (t : Expr) : MetaM Expr := do
  let args := t.getAppArgs
  if args.isEmpty then return t
  let last := args[args.size - 1]!
  let m ← mkFreshExprMVar (← inferType last)
  return mkAppN t.getAppFn (args.set! (args.size - 1) m)

@[term_elab lsRelvl]
meta def elabRelvl : TermElab := fun stx expected? => do
  tryPostponeIfNoneOrMVar expected?
  let some expected := expected? | elabTerm stx[1] none
  let expected ← instantiateMVars expected
  let relaxed ← relaxLast (← whnfR expected)
  let e ← elabTermEnsuringType stx[1] relaxed
  mkExpectedTypeHint (← ensureHasType expected e) expected

end LeanScript.Relvl

end
