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
# `Tests/SnapshotsPBOPure/FloatLetRegression01.lean`, formally

`test` of the snapshot (a copy), translated to `Term` (`#leanscript_to_term`) and optimised
(`Term.optimizeN 3`).  The translation computes `f 2` twice (the projections out of the
structure literal are reduced, which substitutes the `let c := f 2`); the optimiser

* computes it once: the literal `2` is an atom argument (`Atom.int`, `Atom.ofArg?`), so `x2 2` is
  a simple computation that common subexpression elimination recognises (`Term.cseLetE`);
* moves `let x [1] := x2 1`, used once, down past `x2 2` to its use (`Term.sinkWalk`), so that
  the JavaScript printer writes `f(1)` in the record:
  `const x$1 = f(2); return { _1: f(1), _2: x$1, _3: x$1 };`, the shape of
  purescript-backend-optimizer's `legacy-backend/FloatLetRegression01.js`.

`litShare` checks the same for literals of `String` and `Nat` (`Atom.str`, `Atom.nat`).

* `…_optimized_run`: the optimised translation computes the Lean function, for every input.
* `…_optimized_pretty`: the optimised statements (`test` as in
  `FloatLetRegression01-Term-optimized.txt`).
* `Tests/Main.lean` (`floatLetRegressionSpec`) runs them, compiled, and runs `leanscript
  --check` and node on the snapshot.
-/

namespace SinkLetTest

open LeanScript

structure FloatLetResult where
  b  : Int
  c1 : Int
  c2 : Int

structure WrapY where
  y : FloatLetResult

structure WrapX where
  x : WrapY

def test (f : Int → Int) : FloatLetResult :=
  ( let b := f 1
    ( let c := f 2
      ({ x := { y := { b := b, c1 := c, c2 := c } } } : WrapX)
    ).x
  ).y

/-- Two calls on a `String` literal and two on a `Nat` literal, each repeated. -/
def litShare (g : String → Nat) (h : Nat → Nat) : Nat × Nat × Nat × Nat :=
  (h 3, g "a", g "a", h 3)

def testT := #leanscript_to_term test
def litShareT := #leanscript_to_term litShare

/-! ## The optimiser keeps the value -/

/-- The optimised translation of `test` computes `test`, for every `f`. -/
theorem test_optimized_run (f : Int → Int) :
    (((testT (Δ := DSig.nil)).optimizeN 3).run f : Int × Int × Int) =
      ((test f).b, (test f).c1, (test f).c2) := by
  rw [Term.optimizeN_run]; rfl

/-- The optimised translation of `litShare` computes `litShare`, for every `g` and `h`. -/
theorem litShare_optimized_run (g : String → Nat) (h : Nat → Nat) :
    (((litShareT (Δ := DSig.nil)).optimizeN 3).run g h : Nat × Nat × Nat × Nat) =
      litShare g h := by
  rw [Term.optimizeN_run]; rfl

/-! ## The optimised statements -/

/-- `test`: `f 2` computed once, then `f 1` (used once) right before the record. -/
def testPrinted : String :=
  "\n".intercalate [
    "val k1 [1] : ((Int → Int) → (Int × Int × Int)) := fun x2 [ω] : (Int → Int) => (closed)",
    "  let x3 [ω] : Int := x2 2",
    "  let x4 [1] : Int := x2 1",
    "  ret ⟨x4, x3, x3⟩",
    "ret k1"]

theorem test_optimized_pretty : ((testT (Δ := DSig.nil)).optimizeN 3).pretty = testPrinted := by
  native_decide

/-- `litShare`: `h 3` and `g "a"` computed once each (the translation computes each twice). -/
def litSharePrinted : String :=
  "\n".intercalate [
    "val k1 [1] : ((String → Nat) → ((Nat → Nat) → (Nat × (Nat × (Nat × Nat))))) := fun x2 [ω] : (String → Nat) => (closed)",
    "  val k3 [1] : ((Nat → Nat) → (Nat × (Nat × (Nat × Nat)))) := fun x4 [1] : (Nat → Nat) => (open)",
    "    let x5 [ω] : Nat := x4 3",
    "    let x6 [ω] : Nat := x2 \"a\"",
    "    ret ⟨x5, ⟨x6, ⟨x6, x5⟩⟩⟩",
    "  ret k3",
    "ret k1"]

theorem litShare_optimized_pretty :
    ((litShareT (Δ := DSig.nil)).optimizeN 3).pretty = litSharePrinted := by
  native_decide

/-! ## Calls -/

/-- The translation of `test` makes three calls (`f 1`, and `f 2` twice). -/
theorem test_numCalls : (testT (Δ := DSig.nil)).numCalls = 3 := by
  rfl

/-- The optimised translation of `test` makes two: `f 2` is computed once. -/
theorem test_optimized_numCalls : ((testT (Δ := DSig.nil)).optimizeN 3).numCalls = 2 := by
  native_decide

/-- The translation of `litShare` makes four calls (`h 3` and `g "a"` twice each). -/
theorem litShare_numCalls : (litShareT (Δ := DSig.nil)).numCalls = 4 := by
  rfl

/-- The optimised translation of `litShare` makes two. -/
theorem litShare_optimized_numCalls :
    ((litShareT (Δ := DSig.nil)).optimizeN 3).numCalls = 2 := by
  native_decide

end SinkLetTest
