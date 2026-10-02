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
# `Tests/SnapshotsPBOPure/FunctionCompose02.lean`, formally

The definitions of the snapshot (copies), translated to `Term` (`#leanscript_to_term`) and
optimised (`Term.optimizeN 3`).  Here `f` and `g` are parameters (unknown functions), so the
calls cannot be inlined: `testN f g` is, read in eta-long form, `fun x => g (f (g x))` and so on,
a chain of calls with no intermediate closure.  The JavaScript is
`export const test2 = (f, g, a) => g(f(g(a)));`, as purescript-backend-optimizer's
`legacy-backend/FunctionCompose02.js` (`const test2 = (f) => (g) => (x) => g(f(g(x)));`), and
uncurried.

* `…_optimized_run`: the optimised translation computes the Lean function, for every input.
* `…_optimized_pretty`: the optimised statements (as in `FunctionCompose02-Term-optimized.txt`).
* `…_numCalls`: one call per composed function, before and after optimisation.
* `Tests/Main.lean` (`functionCompose02Spec`) runs them, compiled, and runs the JavaScript
  with node.
-/

namespace FunctionCompose02Test

open LeanScript

abbrev F := Int → Int

def test1 (f g : F) : F := f ∘ g
def test2 (f g : F) : F := g ∘ (f ∘ g)
def test3 (f g : F) : F := (f ∘ g) ∘ (f ∘ g)
def test4 (f g : F) : F := ((g ∘ f) ∘ g) ∘ (f ∘ g)

def test1T := #leanscript_to_term test1
def test2T := #leanscript_to_term test2
def test3T := #leanscript_to_term test3
def test4T := #leanscript_to_term test4

/-! ## The optimiser keeps the value -/

theorem test1_optimized_run (f g : F) (x : Int) :
    (((test1T (Δ := DSig.nil)).optimizeN 3).run f g x : Int) = test1 f g x := by
  rw [Term.optimizeN_run]; rfl

theorem test2_optimized_run (f g : F) (x : Int) :
    (((test2T (Δ := DSig.nil)).optimizeN 3).run f g x : Int) = test2 f g x := by
  rw [Term.optimizeN_run]; rfl

theorem test3_optimized_run (f g : F) (x : Int) :
    (((test3T (Δ := DSig.nil)).optimizeN 3).run f g x : Int) = test3 f g x := by
  rw [Term.optimizeN_run]; rfl

theorem test4_optimized_run (f g : F) (x : Int) :
    (((test4T (Δ := DSig.nil)).optimizeN 3).run f g x : Int) = test4 f g x := by
  rw [Term.optimizeN_run]; rfl

/-! ## The optimised statements: three nested closures and a chain of calls -/

/-- The optimised statements of `fun f g x => h_n (… (h_1 x))`, where `calls` lists, innermost
    first, whether each `h_i` is `f` (`true`) or `g` (`false`). -/
def chainPrinted (calls : List Bool) : String :=
  let lets := (List.range calls.length).zip calls |>.map fun (i, isF) =>
    let arg := if i = 0 then "x6" else s!"x{i + 6}"
    s!"      let x{i + 7} [1] : Int := {if isF then "x2" else "x4"} {arg}"
  "\n".intercalate (
    ["val k1 [1] : ((Int → Int) → ((Int → Int) → (Int → Int))) := fun x2 [ω] : (Int → Int) => (closed)",
     "  val k3 [1] : ((Int → Int) → (Int → Int)) := fun x4 [ω] : (Int → Int) => (open)",
     "    val k5 [1] : (Int → Int) := fun x6 [1] : Int => (open)"] ++ lets ++
    [s!"      ret x{calls.length + 6}",
     "    ret k5",
     "  ret k3",
     "ret k1"])

theorem test1_optimized_pretty :
    ((test1T (Δ := DSig.nil)).optimizeN 3).pretty = chainPrinted [false, true] := by
  native_decide

theorem test2_optimized_pretty :
    ((test2T (Δ := DSig.nil)).optimizeN 3).pretty = chainPrinted [false, true, false] := by
  native_decide

theorem test3_optimized_pretty :
    ((test3T (Δ := DSig.nil)).optimizeN 3).pretty =
      chainPrinted [false, true, false, true] := by
  native_decide

theorem test4_optimized_pretty :
    ((test4T (Δ := DSig.nil)).optimizeN 3).pretty =
      chainPrinted [false, true, false, true, false] := by
  native_decide

/-! ## Calls: one per composed function, before and after optimisation -/

theorem test1_numCalls : (test1T (Δ := DSig.nil)).numCalls = 2 := by rfl
theorem test2_numCalls : (test2T (Δ := DSig.nil)).numCalls = 3 := by rfl
theorem test3_numCalls : (test3T (Δ := DSig.nil)).numCalls = 4 := by rfl
theorem test4_numCalls : (test4T (Δ := DSig.nil)).numCalls = 5 := by rfl

theorem test1_optimized_numCalls : ((test1T (Δ := DSig.nil)).optimizeN 3).numCalls = 2 := by
  native_decide
theorem test2_optimized_numCalls : ((test2T (Δ := DSig.nil)).optimizeN 3).numCalls = 3 := by
  native_decide
theorem test3_optimized_numCalls : ((test3T (Δ := DSig.nil)).optimizeN 3).numCalls = 4 := by
  native_decide
theorem test4_optimized_numCalls : ((test4T (Δ := DSig.nil)).optimizeN 3).numCalls = 5 := by
  native_decide

end FunctionCompose02Test
