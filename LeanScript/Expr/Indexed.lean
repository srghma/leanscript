module

public import LeanScript.Expr.Term
public meta import Lean.Elab.Term

@[expose] public section

/-!
# `indexed% t`: a term written out, checked against the indices its type states

A declaration holding a term states the term's grade vector and head in its type
(`LeanScript.Expr.Term`, "Writing down the type of a term"):

```lean
def idNat : Term sg [] 0 (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam :=
  indexed% .lam (.var (v♯0))
```

The grade vector a constructor computes (here `(Usage.single (v♯0)).tail`) is equal to the
stated one (`0`) by computation, but only once the types of the variables are known, and
Lean compares the indices of an expected type from left to right — the grade vector
before the type — so it cannot use such an expected type to elaborate the term.
`indexed% t` elaborates `t` against the expected type with its grade vector and head
left open, as a term whose indices are read off it, and **then** checks that they are
the stated ones.  A stated head that is not the term's is an error that names both.
Where nothing is expected (a side of an equation, say), `indexed% t` is the term with the
indices it has.
-/

meta section

open Lean Meta Elab Term

namespace LeanScript

/-- Is `u` the grade vector `0`, as written? -/
def isZeroUsage (u : Expr) : MetaM Bool := do
  let u ← instantiateMVars u
  return (u.isAppOfArity ``OfNat.ofNat 3 && u.getArg! 1 == mkRawNatLit 0) ||
    u.isAppOf ``Zero.zero || u.isAppOf ``LeanScript.Usage.zero

/-- `e`, at the type `expected`, both of them `LeanScript.Term`s.

    The signature, the context, the type and the head are compared as usual.  The grade
    vector of a closed term stated as `0` is not compared by the elaborator: it is `0` by
    computation (`LeanScript.Expr.Term`), but the computation re-evaluates a shared
    subterm's grades once per use, which is slow for a large term, and the kernel, which
    checks the declaration anyway, caches it.  Any other grade vector is compared as
    usual. -/
def ensureTermHasType (expected e : Expr) : TermElabM Expr := do
  let expected ← instantiateMVars expected
  let ty ← instantiateMVars (← inferType e)
  match (← whnfR expected).getAppFnArgs, (← whnfR ty).getAppFnArgs with
  | (``LeanScript.Term, #[sg, γ, u, τ, k]), (``LeanScript.Term, #[sg', γ', _, τ', k']) =>
      if (← isZeroUsage u) && (← isDefEq γ γ') && (← whnf γ).isAppOf ``List.nil then
        if (← isDefEq sg sg') && (← isDefEq τ τ') && (← isDefEq k k') then
          return ← mkExpectedTypeHint e expected
        throwTypeMismatchError none expected ty e
      Lean.Elab.Term.ensureHasType expected e
  | _, _ => Lean.Elab.Term.ensureHasType expected e

/-- `indexed% t`: elaborate the term `t` with its grade vector and head inferred, then check
    them against the ones of the expected type. -/
syntax:lead (name := indexedTerm) "indexed% " term:lead : term

@[term_elab indexedTerm]
def elabIndexedTerm : TermElab := fun stx expected? => do
  tryPostponeIfNoneOrMVar expected?
  -- the signature, the context and the type the expected type states, when it states them
  let parts? ← match expected? with
    | some expected =>
        match (← whnfR (← instantiateMVars expected)).getAppFnArgs with
        | (``LeanScript.Term, #[sg, γ, _, τ, _]) => pure (some (sg, γ, τ))
        | _ => pure none
    | none => pure none
  let (sg, γ, τ) ← match parts? with
    | some p => pure p
    | none =>
        let γ ← mkFreshExprMVar (mkConst ``LeanScript.Ctx)
        pure (← mkFreshExprMVar (mkConst ``LeanScript.Sig), γ,
          ← mkFreshExprMVar (mkConst ``LeanScript.TyWf))
  let u ← mkFreshExprMVar (mkApp (mkConst ``LeanScript.Usage) γ)
  let k ← mkFreshExprMVar (mkConst ``LeanScript.Head)
  let e ← elabTermEnsuringType stx[1] (mkAppN (mkConst ``LeanScript.Term) #[sg, γ, u, τ, k])
  synthesizeSyntheticMVarsNoPostponing
  match expected? with
  | some expected => ensureTermHasType expected e
  | none => return e

end LeanScript

end

end
