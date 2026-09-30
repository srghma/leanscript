module

public import LeanScript.Term.Optimize.Basic
public import LeanScript.Term.Pretty
public import LeanScript.Term.Build
public meta import LeanScript.TermElab.ToTerm
public meta import LeanScript.Term.Pretty
public meta import LeanScript.Term.Optimize.Basic
public meta import LeanScript.TacticElab.KernelRfl

@[expose] public section

set_option autoImplicit false

/-!
# `test1` of `Tests/SnapshotsPBOPure/CaseProduct.lean`, formally

Lean's `match` on `⟨1, 2, 3⟩ | ⟨_, 4, _⟩ | ⟨4, 5, 6⟩ | _` tests the first field first; when it is
neither `1` nor `4`, and when it is `4`, the next test is `b == 4 → "2"` in both arms.  The
optimiser makes that test first (`Term.shareTestWalk`): `if a == 4 then (if b == 4 then "2"
else …) else (b == 4 ? "2" : "catch")` is `if b == 4 then "2" else if a == 4 then … else
"catch"`, the order of purescript-backend-optimizer's `legacy-backend/CaseProduct.js`.

* `test1T_run`: the translated statement is Lean's decision tree.
* `test1_optimized_run`: for **every** `⟨a, b, c⟩`, the optimised statement (`Term.optimizeN 3`,
  the `Term → Term` phase of the pipeline) computes `test1 ⟨a, b, c⟩`.
* `test1_optimized_pretty`: the optimised statement is the one of
  `CaseProduct-Term-optimized.txt`, with the test of `b == 4` made first.
-/

namespace CaseProductTest

open LeanScript

structure Product3 (α β γ : Type) where
  a : α
  b : β
  c : γ

def test1 : Product3 Nat Nat Nat → String
  | ⟨1, 2, 3⟩ => "1"
  | ⟨_, 4, _⟩ => "2"
  | ⟨4, 5, 6⟩ => "3"
  | _ => "catch"

def test1T := #leanscript_to_term test1

/-- The translated statement of `test1`, run on `⟨a, b, c⟩`: the decision tree of Lean's
    `match` (the first field first, then the second, then the third). -/
theorem test1T_run (a b c : Nat) : (test1T (Δ := DSig.nil)).run (a, b, c) =
    (match decide (a = 1) with
    | true =>
      match decide (b = 2) with
      | true => match decide (c = 3) with
        | true => "1"
        | false => "catch"
      | false => match decide (b = 4) with
        | true => "2"
        | false => "catch"
    | false =>
      match decide (a = 4) with
      | true =>
        match decide (b = 4) with
        | true => "2"
        | false => match decide (b = 5) with
          | true => match decide (c = 6) with
            | true => "3"
            | false => "catch"
          | false => "catch"
      | false => match decide (b = 4) with
        | true => "2"
        | false => "catch" : String) := by kernel_rfl

/-- For **every** `⟨a, b, c⟩`, the optimised statement of `test1` computes `test1 ⟨a, b, c⟩`. -/
theorem test1_optimized_run (a b c : Nat) :
    ((test1T (Δ := DSig.nil)).optimizeN 3).run (a, b, c) = test1 ⟨a, b, c⟩ := by
  rw [Term.optimizeN_run, test1T_run]
  unfold test1
  by_cases h1 : a = 1 <;> by_cases h2 : b = 2 <;> by_cases h3 : c = 3 <;> by_cases h4 : b = 4 <;>
    by_cases h5 : a = 4 <;> by_cases h6 : b = 5 <;> by_cases h7 : c = 6 <;>
    subst_vars <;> simp_all <;> rfl

/-- The optimised statement of `test1` is the one of
    `Tests/SnapshotsPBOPure/CaseProduct-Term-optimized.txt` (checked with `native_decide`, since
    the printer is compiled code): when the first field is not `1`, `b == 4` is tested first. -/
theorem test1_optimized_pretty :
    ((test1T (Δ := DSig.nil)).optimizeN 3).pretty =
      "val k1 [1] : ((Nat × Nat × Nat) → String) := fun x2 [1] : (Nat × Nat × Nat) => (closed)\n" ++
      "  let ⟨f3 [ω] : Nat, f4 [ω] : Nat, f5 [1] : Nat⟩ := x2\n" ++
      "  if lean_nat_dec_eq__Nat_decEq(f3, 1) then\n" ++
      "    if lean_nat_dec_eq__Nat_decEq(f4, 2) then\n" ++
      "      ret cond(lean_nat_dec_eq__Nat_decEq(f5, 3), \"1\", \"catch\")\n" ++
      "    else\n" ++
      "      ret cond(lean_nat_dec_eq__Nat_decEq(f4, 4), \"2\", \"catch\")\n" ++
      "  else\n" ++
      "    if lean_nat_dec_eq__Nat_decEq(f4, 4) then\n" ++
      "      ret \"2\"\n" ++
      "    else\n" ++
      "      if lean_nat_dec_eq__Nat_decEq(f3, 4) then\n" ++
      "        if lean_nat_dec_eq__Nat_decEq(f4, 5) then\n" ++
      "          ret cond(lean_nat_dec_eq__Nat_decEq(f5, 6), \"3\", \"catch\")\n" ++
      "        else\n" ++
      "          ret \"catch\"\n" ++
      "      else\n" ++
      "        ret \"catch\"\n" ++
      "ret k1" := by
  native_decide

end CaseProductTest

end
