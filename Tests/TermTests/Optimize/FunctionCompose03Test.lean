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
# `Tests/SnapshotsPBOPure/FunctionCompose03.lean`, formally

The definitions of the snapshot (copies), translated to `Term` (`#leanscript_to_term`) and
optimised (`Term.optimizeN 3`).  Here `f` and `g` are thunks (`Unit → Int → Int`), and each
composition forces them again (`f () ∘ g ()`): the translation of `test4` forces five thunks.
The optimiser shares the repeated `f ()` and `g ()` (common subexpressions), so each thunk is
forced once per call, as in purescript-backend-optimizer's `legacy-backend/FunctionCompose03.js`
(`const $0 = g(); const $1 = f(); return (x) => $0($1($0($1($0(x)))));`).

* `…_optimized_run`: the optimised translation computes the Lean function, for every input
  (a `Lazy` value denotes the value it holds: the thunks are passed forced).
* `…_numCalls`: the calls before optimisation (a thunk forced per composed function, then one
  call per composed function) and after (each of `f`, `g` forced once).
* `Tests/Main.lean` (`functionCompose03Spec`) runs them, compiled, and runs the JavaScript
  with node, counting how many times each thunk is forced.
-/

namespace FunctionCompose03Test

open LeanScript

abbrev F := Unit → Int → Int

def test1 (f g : F) : Int → Int := f () ∘ g ()
def test2 (f g : F) : Int → Int := g () ∘ (f () ∘ g ())
def test3 (f g : F) : Int → Int := (f () ∘ g ()) ∘ (f () ∘ g ())
def test4 (f g : F) : Int → Int := ((g () ∘ f ()) ∘ g ()) ∘ (f () ∘ g ())

def test1T := #leanscript_to_term test1
def test2T := #leanscript_to_term test2
def test3T := #leanscript_to_term test3
def test4T := #leanscript_to_term test4

/-! ## The optimiser keeps the value -/

theorem test1_optimized_run (f g : F) (x : Int) :
    (((test1T (Δ := DSig.nil)).optimizeN 3).run (f ()) (g ()) x : Int) = test1 f g x := by
  rw [Term.optimizeN_run]; rfl

theorem test2_optimized_run (f g : F) (x : Int) :
    (((test2T (Δ := DSig.nil)).optimizeN 3).run (f ()) (g ()) x : Int) = test2 f g x := by
  rw [Term.optimizeN_run]; rfl

theorem test3_optimized_run (f g : F) (x : Int) :
    (((test3T (Δ := DSig.nil)).optimizeN 3).run (f ()) (g ()) x : Int) = test3 f g x := by
  rw [Term.optimizeN_run]; rfl

theorem test4_optimized_run (f g : F) (x : Int) :
    (((test4T (Δ := DSig.nil)).optimizeN 3).run (f ()) (g ()) x : Int) = test4 f g x := by
  rw [Term.optimizeN_run]; rfl

/-! ## Calls: every thunk forced again before optimisation, each once after -/

theorem test1_numCalls : (test1T (Δ := DSig.nil)).numCalls = 4 := by rfl
theorem test2_numCalls : (test2T (Δ := DSig.nil)).numCalls = 6 := by rfl
theorem test3_numCalls : (test3T (Δ := DSig.nil)).numCalls = 8 := by rfl
theorem test4_numCalls : (test4T (Δ := DSig.nil)).numCalls = 10 := by rfl

theorem test1_optimized_numCalls : ((test1T (Δ := DSig.nil)).optimizeN 3).numCalls = 4 := by
  native_decide
theorem test2_optimized_numCalls : ((test2T (Δ := DSig.nil)).optimizeN 3).numCalls = 5 := by
  native_decide
theorem test3_optimized_numCalls : ((test3T (Δ := DSig.nil)).optimizeN 3).numCalls = 6 := by
  native_decide
theorem test4_optimized_numCalls : ((test4T (Δ := DSig.nil)).optimizeN 3).numCalls = 7 := by
  native_decide

end FunctionCompose03Test
