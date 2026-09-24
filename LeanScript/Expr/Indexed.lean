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
-/

meta section

open Lean Meta Elab Term

namespace LeanScript

/-- `indexed% t`: elaborate the term `t` with its grade vector and head inferred, then check
    them against the ones of the expected type. -/
syntax:lead (name := indexedTerm) "indexed% " term:lead : term

@[term_elab indexedTerm]
def elabIndexedTerm : TermElab := fun stx expected? => do
  let some expected := expected?
    | throwError "`indexed%`: the expected type must be a `LeanScript.Term`"
  let expected ← instantiateMVars expected
  match (← whnfR expected).getAppFnArgs with
  | (``LeanScript.Term, #[sg, γ, _, τ, _]) =>
      let u ← mkFreshExprMVar (mkApp (mkConst ``LeanScript.Usage) γ)
      let k ← mkFreshExprMVar (mkConst ``LeanScript.Head)
      let e ← elabTermEnsuringType stx[1] (mkAppN (mkConst ``LeanScript.Term) #[sg, γ, u, τ, k])
      synthesizeSyntheticMVarsNoPostponing
      Lean.Elab.Term.ensureHasType (some expected) e
  | _ => throwError "`indexed%`: the expected type{indentExpr expected}\nis not a `LeanScript.Term`"

end LeanScript

end

end
