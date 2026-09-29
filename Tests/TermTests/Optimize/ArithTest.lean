module

public import LeanScript.Term.Optimize.Basic
public import LeanScript.Term.Optimize.CountOptimize
public import LeanScript.Term.Build
public meta import LeanScript.TermElab.ToTerm

@[expose] public section

set_option autoImplicit false

/-!
# Chains of additions and multiplications (`Term.arithWalk`) on `AssocIntOps`

Functions of `Tests/SnapshotsPBOPure/AssocIntOps.lean`, translated, plus a fixed-width one.
The optimiser folds the literals of each chain, counts the copies of the unknown in a sum and
combines the operands from the left: `1 + (((((2 + x) + x) + x) + x) + 3) + 4` becomes
`x * 4 + 10`, and `1 * (2 * (x * (x * (x * (x * 3))))) * 4` becomes `x ^ 4 * 24`
(`lean_int_pow`, `x ** 4n` in JavaScript: three copies of an unknown or more in a product of
`Int`s or `Nat`s are a power).
The printed optimised statements and their values (compiled) are checked by `lake exe tests`
(`Tests/Main.lean`, `arithSpec`); here the value is unchanged for every input, by
`Term.optimizeN_run`, and no call is added, by `Term.numCalls_arithWalk`.
-/

namespace ArithTest

open LeanScript

def test1 (x : Int) : Int :=
  1 + (((((2 + x) + x) + x) + x) + 3) + 4

def test3 (x : Int) : Int :=
  1 + (2 + (x + (x + (x + (x + 3))))) + 4 + (((((5 + x) + x) + x) + x) + 6) + 7

def test5 (x : Int) : Int :=
  1 * (2 * (x * (x * (x * (x * 3))))) * 4

/-- The literals are folded modulo `2⁸`: `200 + x + 200` is `x + 144`. -/
def wrap8 (x : UInt8) : UInt8 :=
  200 + x + 200

/-- Two unknowns, counted separately wherever their copies stand: `a * 3 + b * 2 + 1`. -/
def twoVars (a b : Nat) : Nat :=
  a + (b + 1) + (a + b) + a

/-- A product of `Nat`s: `x ^ 3 * 7` (`lean_nat_pow`); `x * x` stays. -/
def natCube (x : Nat) : Nat :=
  x * 7 * x * x + x * x

def test1T := #leanscript_to_term test1
def test3T := #leanscript_to_term test3
def test5T := #leanscript_to_term test5
def wrap8T := #leanscript_to_term wrap8
def twoVarsT := #leanscript_to_term twoVars
def natCubeT := #leanscript_to_term natCube

/-- The optimised statements compute the functions, for every input. -/
example (x : Int) : ((test1T (Δ := DSig.nil)).optimizeN 3).run x = test1 x := by
  rw [Term.optimizeN_run]; rfl

example (x : Int) : ((test3T (Δ := DSig.nil)).optimizeN 3).run x = test3 x := by
  rw [Term.optimizeN_run]; rfl

example (x : Int) : ((test5T (Δ := DSig.nil)).optimizeN 3).run x = test5 x := by
  rw [Term.optimizeN_run]; rfl

example (x : UInt8) : ((wrap8T (Δ := DSig.nil)).optimizeN 3).run x = wrap8 x := by
  rw [Term.optimizeN_run]; rfl

example (a b : Nat) : ((twoVarsT (Δ := DSig.nil)).optimizeN 3).run a b = twoVars a b := by
  rw [Term.optimizeN_run]; rfl

example (x : Nat) : ((natCubeT (Δ := DSig.nil)).optimizeN 3).run x = natCube x := by
  rw [Term.optimizeN_run]; rfl

/-- The normalisation itself, on any statement: the value is unchanged, and no call is
    added. -/
example : ∀ x : Int,
    ((test3T (Δ := DSig.nil)).arithWalk).run x = (test3T (Δ := DSig.nil)).run x :=
  fun _ => congrFun (Term.arithWalk_eval _ _ _ _) _

example : ((test3T (Δ := DSig.nil)).arithWalk).numCalls = (test3T (Δ := DSig.nil)).numCalls :=
  Term.numCalls_arithWalk _

end ArithTest

end
