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
# `Tests/SnapshotsPBOPure/AssocStringAppend.lean`, formally

The three functions of the snapshot, translated to `Term` (`#leanscript_to_term`) and optimised
(`Term.optimizeN 3`, the pipeline's `Term → Term` phase, whose string append chain
normalisation is `StrApp.normNeu`, run by `Term.appendWalk`).  For each function `testN`:

* `testN_optimized_run`: for **every** input `x`, the optimised statement computes the
  left-grouped chain the legacy backend writes (`"ab" ++ x ++ x ++ x ++ x ++ "cd"`, …), through
  the general theorem `Term.optimizeN_run` and a proof about the Lean function (`testN_eq`);
* `testN_optimized_pretty`: the optimised statement is exactly the left-grouped chain of
  `Tests/SnapshotsPBOPure/AssocStringAppend-Term-optimized.txt`, with the literals merged
  (checked with `native_decide`, since the printer is compiled code).  The JavaScript backend
  writes it without parentheses, as `Tests/SnapshotsPBOPure/legacy-backend/AssocStringAppend.js`
  does.
-/

namespace AssocStringAppendTest

open LeanScript

/-- The printed form of an optimised `String → String` function whose body returns `body`. -/
def printedStrFn (body : String) : String :=
  "val k1 [1] : (String → String) := fun x2 [ω] : String => (closed)\n  ret " ++ body ++ "\nret k1"

/-- `lean_string_append__String_append(a, b)`, printed. -/
def app (a b : String) : String := "lean_string_append__String_append(" ++ a ++ ", " ++ b ++ ")"

/-- The printed left-grouped chain of the operands. -/
def chain : List String → String
  | [] => ""
  | a :: as => as.foldl app a

def test1 (x : String) : String :=
  "a" ++ (((((("b" ++ x) ++ x) ++ x) ++ x) ++ "c")) ++ "d"

def test1T := #leanscript_to_term test1

def test2 (x : String) : String :=
  "a" ++ ("b" ++ (x ++ (x ++ (x ++ (x ++ "c"))))) ++ "d"

def test2T := #leanscript_to_term test2

def test3 (x : String) : String :=
  "a" ++ ("b" ++ (x ++ (x ++ (x ++ (x ++ "c"))))) ++ "d" ++
    (((((("e" ++ x) ++ x) ++ x) ++ x) ++ "f")) ++ "g"

def test3T := #leanscript_to_term test3

theorem test1_eq (x : String) : test1 x = "ab" ++ x ++ x ++ x ++ x ++ "cd" := by
  have hab : "a" ++ "b" = "ab" := by decide
  have hcd : "c" ++ "d" = "cd" := by decide
  simp only [test1, ← hab, ← hcd, String.append_assoc]

theorem test1_optimized_run (x : String) :
    ((test1T (Δ := DSig.nil)).optimizeN 3).run x = "ab" ++ x ++ x ++ x ++ x ++ "cd" := by
  rw [Term.optimizeN_run]
  exact test1_eq x

theorem test1_optimized_pretty :
    ((test1T (Δ := DSig.nil)).optimizeN 3).pretty =
      printedStrFn (chain ["\"ab\"", "x2", "x2", "x2", "x2", "\"cd\""]) := by
  native_decide

theorem test2_eq (x : String) : test2 x = "ab" ++ x ++ x ++ x ++ x ++ "cd" := by
  have hab : "a" ++ "b" = "ab" := by decide
  have hcd : "c" ++ "d" = "cd" := by decide
  simp only [test2, ← hab, ← hcd, String.append_assoc]

theorem test2_optimized_run (x : String) :
    ((test2T (Δ := DSig.nil)).optimizeN 3).run x = "ab" ++ x ++ x ++ x ++ x ++ "cd" := by
  rw [Term.optimizeN_run]
  exact test2_eq x

theorem test2_optimized_pretty :
    ((test2T (Δ := DSig.nil)).optimizeN 3).pretty =
      printedStrFn (chain ["\"ab\"", "x2", "x2", "x2", "x2", "\"cd\""]) := by
  native_decide

theorem test3_eq (x : String) :
    test3 x = "ab" ++ x ++ x ++ x ++ x ++ "cde" ++ x ++ x ++ x ++ x ++ "fg" := by
  have hab : "a" ++ "b" = "ab" := by decide
  have hcde : "c" ++ ("d" ++ "e") = "cde" := by decide
  have hfg : "f" ++ "g" = "fg" := by decide
  simp only [test3, ← hab, ← hcde, ← hfg, String.append_assoc]

theorem test3_optimized_run (x : String) :
    ((test3T (Δ := DSig.nil)).optimizeN 3).run x =
      "ab" ++ x ++ x ++ x ++ x ++ "cde" ++ x ++ x ++ x ++ x ++ "fg" := by
  rw [Term.optimizeN_run]
  exact test3_eq x

theorem test3_optimized_pretty :
    ((test3T (Δ := DSig.nil)).optimizeN 3).pretty =
      printedStrFn (chain ["\"ab\"", "x2", "x2", "x2", "x2", "\"cde\"",
        "x2", "x2", "x2", "x2", "\"fg\""]) := by
  native_decide

end AssocStringAppendTest

end
