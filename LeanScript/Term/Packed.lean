module

public import LeanScript.Term.Term

@[expose] public section

set_option autoImplicit false

/-!
# A closed program with its signature, packed

`#leanscript_to_term f` elaborates to a `Term Δ 0 [] [] τ [] none` whose indices (the block
sizes `ks`, the signature `Δ`, the type `τ`) depend on `f`.  A tool that handles many
translations at run time (the `leanscript` command line tool, which evaluates the elaborated
translations to values it then optimises and prints) needs one type for all of them:
`ClosedTerm` packs the indices with the term.
-/

namespace LeanScript

/-- A closed statement at depth `0`, together with its signature and its type. -/
structure ClosedTerm where
  /-- The block sizes of the signature. -/
  ks : List Nat
  /-- The signature: the declared datatypes the program speaks about. -/
  Δ : DSig ks
  /-- The type of the program. -/
  τ : Ty ks
  /-- Its level (always `none` for a closed term, kept for generality). -/
  o : Lvl
  /-- The statement. -/
  term : Term Δ 0 [] [] τ [] o

end LeanScript

end
