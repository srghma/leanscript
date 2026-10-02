module

public import LeanScript.Term.Optimize.Basic
public import LeanScript.Term.Pretty
public import LeanScript.Term.Build
public meta import LeanScript.TermElab.ToTerm
public meta import LeanScript.Term.Pretty
public meta import LeanScript.Term.Optimize.Basic

@[expose] public section

set_option autoImplicit false

/-!
# `Tests/SnapshotsPBOPure/FunctionCompose01.lean`, formally

The definitions of the snapshot (copies), translated to `Term` (`#leanscript_to_term`) and
optimised (`Term.optimizeN 3`).  The translation of a composition `f ∘ g` (read in eta-long
form, `fun a => f (g a)`) declares a closure for each function it composes and calls them in a
chain (`test4` declares five and makes five calls).  Every one of those closures is closed and
returns a literal, so the optimiser inlines the calls (`Term.inlineKnown`, `Term.inlineRet`) and
drops the closures (dead-code elimination): each `testN` becomes `fun x => ret "a"` (or `"b"`),
no call left, and the JavaScript is `export const test1 = (a) => "a";`, as
purescript-backend-optimizer's `legacy-backend/FunctionCompose01.js`
(`const test1 = (_ignored) => "a";`).

* `…_optimized_run`: the optimised translation computes the Lean function, for every input.
* `…_optimized_pretty`: the optimised statements (as in `FunctionCompose01-Term-optimized.txt`).
* `…_numCalls`: the calls the translation makes, and none after optimisation.
* `Tests/Main.lean` (`functionCompose01Spec`) runs them, compiled, and runs `leanscript
  --check` and node on the snapshot.
-/

namespace FunctionComposeTest

open LeanScript

def f (_ : String) : String := "a"
def g (_ : String) : String := "b"

def test1 := f ∘ g
def test2 := g ∘ (f ∘ g)
def test3 := (f ∘ g) ∘ (f ∘ g)
def test4 := ((g ∘ f) ∘ g) ∘ (f ∘ g)

def test1T := #leanscript_to_term test1
def test2T := #leanscript_to_term test2
def test3T := #leanscript_to_term test3
def test4T := #leanscript_to_term test4

/-! ## The optimiser keeps the value -/

theorem test1_optimized_run (s : String) :
    (((test1T (Δ := DSig.nil)).optimizeN 3).run s : String) = test1 s := by
  rw [Term.optimizeN_run]; rfl

theorem test2_optimized_run (s : String) :
    (((test2T (Δ := DSig.nil)).optimizeN 3).run s : String) = test2 s := by
  rw [Term.optimizeN_run]; rfl

theorem test3_optimized_run (s : String) :
    (((test3T (Δ := DSig.nil)).optimizeN 3).run s : String) = test3 s := by
  rw [Term.optimizeN_run]; rfl

theorem test4_optimized_run (s : String) :
    (((test4T (Δ := DSig.nil)).optimizeN 3).run s : String) = test4 s := by
  rw [Term.optimizeN_run]; rfl

/-! ## The optimised statements: a closure that returns the literal -/

/-- The optimised statements of a function that ignores its argument and returns `lit`. -/
def constPrinted (lit : String) : String :=
  "\n".intercalate [
    "val k1 [1] : (String → String) := fun x2 [0] : String => (closed)",
    s!"  ret \"{lit}\"",
    "ret k1"]

theorem test1_optimized_pretty :
    ((test1T (Δ := DSig.nil)).optimizeN 3).pretty = constPrinted "a" := by
  native_decide

theorem test2_optimized_pretty :
    ((test2T (Δ := DSig.nil)).optimizeN 3).pretty = constPrinted "b" := by
  native_decide

theorem test3_optimized_pretty :
    ((test3T (Δ := DSig.nil)).optimizeN 3).pretty = constPrinted "a" := by
  native_decide

theorem test4_optimized_pretty :
    ((test4T (Δ := DSig.nil)).optimizeN 3).pretty = constPrinted "b" := by
  native_decide

/-! ## Calls: one per composed function in the translation, none after optimisation -/

theorem test1_numCalls : (test1T (Δ := DSig.nil)).numCalls = 2 := by rfl
theorem test2_numCalls : (test2T (Δ := DSig.nil)).numCalls = 3 := by rfl
theorem test3_numCalls : (test3T (Δ := DSig.nil)).numCalls = 4 := by rfl
theorem test4_numCalls : (test4T (Δ := DSig.nil)).numCalls = 5 := by rfl

theorem test1_optimized_numCalls : ((test1T (Δ := DSig.nil)).optimizeN 3).numCalls = 0 := by
  native_decide
theorem test2_optimized_numCalls : ((test2T (Δ := DSig.nil)).optimizeN 3).numCalls = 0 := by
  native_decide
theorem test3_optimized_numCalls : ((test3T (Δ := DSig.nil)).optimizeN 3).numCalls = 0 := by
  native_decide
theorem test4_optimized_numCalls : ((test4T (Δ := DSig.nil)).optimizeN 3).numCalls = 0 := by
  native_decide

end FunctionComposeTest
