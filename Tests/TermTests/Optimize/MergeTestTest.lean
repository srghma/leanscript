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
# `Tests/SnapshotsPBOPure/EsSharedElse.lean`, formally

`test1` of the snapshot, and four more nested `if`s, translated to `Term`
(`#leanscript_to_term`) and optimised (`Term.optimizeN 3`).  `Branch.mergeTest`
(`LeanScript.Term.Optimize.MergeTest`) merges two tests that end in the same answer into one
condition, `p && q` (`p ? q : false`) or `p || q` (`p ? true : q`), with `!q` when the shared
answer is the other arm of the inner test:

| function | Lean | optimised (as JavaScript) |
|---|---|---|
| `test1` | `if a then (if b then 1 else E) else E` | `if (a && b) return 1; return c ? 2 : 3;` |
| `andChain` | three nested tests, all ending in `3` | `a && b && c ? 1 : 3` |
| `orChain` | `if a then 1 else if b then 1 else 2` | `a \|\| b ? 1 : 2` |
| `andNot` | `if a then (if b then 3 else …) else 3` | `if (a && !b) return c ? 1 : 2; return 3;` |
| `orNot` | `if a then 1 else if b then 2 else 1` | `a \|\| !b ? 1 : 2` |

* `…_optimized_run`: the optimised translation computes what the translation computes, for
  every input (the general `Term.optimizeN_run`).
* `…_optimized_pretty`: the optimised statements (`test1` as in
  `EsSharedElse-Term-optimized.txt`).
* `Tests/Main.lean` (`esSharedElseSpec`) runs them, compiled, on every input, and runs
  `leanscript --check` and node on the snapshot.
-/

namespace MergeTestTest

open LeanScript

def test1 (a b c : Bool) : Int :=
  if a then
    if b then
      1
    else if c then
      2
    else
      3
  else if c then
    2
  else
    3

def andChain (a b c : Bool) : Nat :=
  if a then (if b then (if c then 1 else 3) else 3) else 3

def orChain (a b : Bool) : Nat :=
  if a then 1 else if b then 1 else 2

def andNot (a b c : Bool) : Nat :=
  if a then (if b then 3 else (if c then 1 else 2)) else 3

def orNot (a b : Bool) : Nat :=
  if a then 1 else if b then 2 else 1

def test1T := #leanscript_to_term test1
def andChainT := #leanscript_to_term andChain
def orChainT := #leanscript_to_term orChain
def andNotT := #leanscript_to_term andNot
def orNotT := #leanscript_to_term orNot

/-! ## The optimiser keeps the value -/

theorem test1_optimized_run (a b c : Bool) :
    ((test1T (Δ := DSig.nil)).optimizeN 3).run a b c = (test1T (Δ := DSig.nil)).run a b c := by
  rw [Term.optimizeN_run]

theorem andChain_optimized_run (a b c : Bool) :
    ((andChainT (Δ := DSig.nil)).optimizeN 3).run a b c =
      (andChainT (Δ := DSig.nil)).run a b c := by
  rw [Term.optimizeN_run]

theorem orChain_optimized_run (a b : Bool) :
    ((orChainT (Δ := DSig.nil)).optimizeN 3).run a b = (orChainT (Δ := DSig.nil)).run a b := by
  rw [Term.optimizeN_run]

/-! ## The optimised statements -/

/-- `EsSharedElse.test1`: the shared `else` (`c ? 2 : 3`) is written once, after one test
    `a && b`; the answers are a conditional already, so the `if` stays a statement
    (`Term.condRet`). -/
def test1Printed : String :=
  "\n".intercalate [
    "val k1 [1] : (Bool → (Bool → (Bool → Int))) := fun x2 [ω] : Bool => (closed)",
    "  val k3 [1] : (Bool → (Bool → Int)) := fun x4 [ω] : Bool => (open)",
    "    val k5 [1] : (Bool → Int) := fun x6 [1] : Bool => (open)",
    "      if cond(x2, x4, false) then",
    "        ret 1",
    "      else",
    "        ret cond(x6, 2, 3)",
    "    ret k5",
    "  ret k3",
    "ret k1"]

theorem test1_optimized_pretty : ((test1T (Δ := DSig.nil)).optimizeN 3).pretty = test1Printed := by
  native_decide

/-- Three tests ending in `3`: one condition `a && b && c`, grouped to the left. -/
def andChainPrinted : String :=
  "\n".intercalate [
    "val k1 [1] : (Bool → (Bool → (Bool → Nat))) := fun x2 [ω] : Bool => (closed)",
    "  val k3 [1] : (Bool → (Bool → Nat)) := fun x4 [ω] : Bool => (open)",
    "    val k5 [1] : (Bool → Nat) := fun x6 [1] : Bool => (open)",
    "      ret cond(cond(cond(x2, x4, false), x6, false), 1, 3)",
    "    ret k5",
    "  ret k3",
    "ret k1"]

theorem andChain_optimized_pretty :
    ((andChainT (Δ := DSig.nil)).optimizeN 3).pretty = andChainPrinted := by
  native_decide

/-- `if a then 1 else if b then 1 else 2`: `a || b ? 1 : 2`. -/
def orChainPrinted : String :=
  "\n".intercalate [
    "val k1 [1] : (Bool → (Bool → Nat)) := fun x2 [ω] : Bool => (closed)",
    "  val k3 [1] : (Bool → Nat) := fun x4 [1] : Bool => (open)",
    "    ret cond(cond(x2, true, x4), 1, 2)",
    "  ret k3",
    "ret k1"]

theorem orChain_optimized_pretty :
    ((orChainT (Δ := DSig.nil)).optimizeN 3).pretty = orChainPrinted := by
  native_decide

/-- The shared answer is the `then` arm of the inner test: `a && !b`. -/
def andNotPrinted : String :=
  "\n".intercalate [
    "val k1 [1] : (Bool → (Bool → (Bool → Nat))) := fun x2 [ω] : Bool => (closed)",
    "  val k3 [1] : (Bool → (Bool → Nat)) := fun x4 [ω] : Bool => (open)",
    "    val k5 [1] : (Bool → Nat) := fun x6 [1] : Bool => (open)",
    "      if cond(x2, cond(x4, false, true), false) then",
    "        ret cond(x6, 1, 2)",
    "      else",
    "        ret 3",
    "    ret k5",
    "  ret k3",
    "ret k1"]

theorem andNot_optimized_pretty :
    ((andNotT (Δ := DSig.nil)).optimizeN 3).pretty = andNotPrinted := by
  native_decide

/-- The shared answer is the `else` arm of the inner test: `a || !b ? 1 : 2`. -/
def orNotPrinted : String :=
  "\n".intercalate [
    "val k1 [1] : (Bool → (Bool → Nat)) := fun x2 [ω] : Bool => (closed)",
    "  val k3 [1] : (Bool → Nat) := fun x4 [1] : Bool => (open)",
    "    ret cond(cond(x2, true, cond(x4, false, true)), 1, 2)",
    "  ret k3",
    "ret k1"]

theorem orNot_optimized_pretty :
    ((orNotT (Δ := DSig.nil)).optimizeN 3).pretty = orNotPrinted := by
  native_decide

end MergeTestTest

end
