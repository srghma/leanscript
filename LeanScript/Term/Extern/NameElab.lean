module

public meta import Lean.Elab.Term

@[expose] public section

set_option autoImplicit false

/-!
# `ctor_names% T`: the names of the constructors of an inductive, as an array of strings

Used by `LeanScript.Term.Extern.Name` to name every entry of the catalogue of externs without
listing the 400-odd names by hand: `(ctor_names% PreludeExtern)[e.ctorIdx]!` is the name of
the entry `e`.
-/

namespace LeanScript

open Lean Elab Term Meta

/-- `ctor_names% T`: the last components of the names of the constructors of `T`, in order. -/
syntax (name := ctorNamesStx) "ctor_names% " ident : term

@[term_elab ctorNamesStx]
meta def elabCtorNames : TermElab := fun stx _ => do
  let n ← realizeGlobalConstNoOverloadWithInfo stx[1]
  let some (.inductInfo i) := (← getEnv).find? n
    | throwError "`{n}` is not an inductive type"
  return toExpr (i.ctors.map fun c => c.getString!).toArray

end LeanScript

end
