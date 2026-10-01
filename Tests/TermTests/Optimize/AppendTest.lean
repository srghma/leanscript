module

public import LeanScript.Term.Optimize.Basic
public import LeanScript.Term.Optimize.CountOptimize
public import LeanScript.Term.Build
public meta import LeanScript.TermElab.ToTerm

@[expose] public section

set_option autoImplicit false

/-!
# Append chains (`Term.appendWalk`) on `AssocArrayAppend`

Array functions of `Tests/SnapshotsPBOPure/AssocArrayAppend.lean`, translated (the list
functions, which the command-line tool translates too, are checked by its snapshot
`AssocArrayAppend-Term-optimized.txt`).  The optimiser regroups their chains of `++` to the
left (the grouping `Array.append` is cheapest with) and merges the neighbouring literals, so
that `x ++ (y ++ (arr ++ (arr ++ (arr ++ (arr ++ z))))) ++ w` (with `x = #["a"]`, …) becomes
`((((#["a", "b"] ++ arr) ++ arr) ++ arr) ++ arr) ++ #["c", "d"]`.  The printed optimised
statements and their values (compiled) are checked by `lake exe tests`
(`Tests/Main.lean`, `appendSpec`); here the value is unchanged for every input, by
`Term.optimizeN_run`, and no call is added, by `Term.numCalls_optimizeN`.
-/

namespace AppendTest

open LeanScript

def arrTest1 (arr : Array String) : Array String :=
  let x := #["a"]
  let y := #["b"]
  let z := #["c"]
  let w := #["d"]
  x ++ (y ++ (arr ++ (arr ++ (arr ++ (arr ++ z))))) ++ w

def arrTest3 (arr : Array String) : Array String :=
  #["a"] ++ (#["b"] ++ (arr ++ (arr ++ (arr ++ (arr ++ #["c"]))))) ++ #["d"] ++
    (#["e"] ++ arr ++ arr ++ arr ++ arr ++ #["f"]) ++ #["g"]

/-- An empty literal in a chain is dropped. -/
def arrEmpty (arr : Array Nat) : Array Nat :=
  #[1] ++ (#[2] ++ (arr ++ #[])) ++ #[3]

/-- A record built with a constant array literal and appended to another one: once the
    append is inlined, its operand names the literal (`val k := #["h"]`); the optimiser writes
    the literal in place (`Term.knownLits`), so that the append starts with it. -/
structure RA where
  s : String
  a : Array String

def appendRA (x y : RA) : RA := { s := x.s ++ y.s, a := x.a ++ y.a }

def knownLit (y : RA) : RA := appendRA { s := "h", a := #["h"] } y

def arrTest1T := #leanscript_to_term arrTest1
def arrTest3T := #leanscript_to_term arrTest3
def arrEmptyT := #leanscript_to_term arrEmpty
def knownLitT := #leanscript_to_term knownLit

/-- The optimised statement computes the function, for every input. -/
example (arr : Array String) :
    ((arrTest1T (Δ := DSig.nil)).optimizeN 3).run arr = arrTest1 arr := by
  rw [Term.optimizeN_run]; rfl

/-- The regrouping itself, on any statement: the value is unchanged, and no call is added. -/
example : ∀ arr : Array String,
    ((arrTest3T (Δ := DSig.nil)).appendWalk).run arr = (arrTest3T (Δ := DSig.nil)).run arr :=
  fun _ => congrFun (Term.appendWalk_eval _ _ _ _) _

example :
    ((arrTest3T (Δ := DSig.nil)).appendWalk).numCalls = (arrTest3T (Δ := DSig.nil)).numCalls :=
  Term.numCalls_appendWalk _

end AppendTest

end
