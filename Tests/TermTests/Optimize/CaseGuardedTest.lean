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
# `test1` of `Tests/SnapshotsPBOPure/CaseGuarded.lean`, formally

`toString n` of an `Int` is `Int.repr n`, which the translation calls as the extern
`lean_int_repr` (and `toString` of a `Nat` as `lean_nat_repr`): an entry of the catalogue whose
meaning is the Lean function itself (`IntBasicExtern.eval`).

* `eval_lean_int_repr`, `eval_lean_nat_repr`: the meaning of the two externs is `toString`.
* `test1T_run`: the translated statement of `test1`, run on `n`, is its three tests and the
  strings built with `Int.repr` (checked by the kernel, `kernel_rfl`).
* `test1_optimized_run`: for **every** `n`, the optimised statement (`Term.optimizeN 3`, the
  `Term → Term` phase of the pipeline) computes `test1 n`.
* `test1_optimized_pretty`: the optimised statement is the one of
  `CaseGuarded-Term-optimized.txt`.
-/

namespace CaseGuardedTest

open LeanScript

def test1 (n : Int) : String :=
  if n < 1 then "n: " ++ toString n
  else if n > 1 && n < 100 then "1 < x < 100: " ++ toString n
  else "catch"

def test1T := #leanscript_to_term test1

/-- The meaning of the extern `lean_int_repr` is `toString` of an `Int`. -/
theorem eval_lean_int_repr (n : Int) :
    Extern.eval DSig.nil.refDen LeanInitPureExtern.lean_int_repr (Tuple.cons n PUnit.unit) =
      toString n := rfl

/-- The meaning of the extern `lean_nat_repr` is `toString` of a `Nat`. -/
theorem eval_lean_nat_repr (n : Nat) :
    Extern.eval DSig.nil.refDen LeanInitPureExtern.lean_nat_repr (Tuple.cons n PUnit.unit) =
      toString n := rfl

/-- The translated statement of `test1`, run on `n`: its three tests on `decide`, each branch
    computing its string with the externs `lean_string_append` and `lean_int_repr`
    (`Int.repr`, the `toString` of an `Int`). -/
theorem test1T_run (n : Int) : (test1T (Δ := DSig.nil)).run n =
    (match decide (n < 1) with
    | true => "n: " ++ Int.repr n
    | false =>
      match (match decide (1 < n) with | true => decide (n < 100) | false => false) with
      | true => "1 < x < 100: " ++ Int.repr n
      | false => "catch") := by kernel_rfl

/-- For **every** `n`, the optimised statement of `test1` computes `test1 n`. -/
theorem test1_optimized_run (n : Int) :
    ((test1T (Δ := DSig.nil)).optimizeN 3).run n = test1 n := by
  rw [Term.optimizeN_run, test1T_run]
  unfold test1
  by_cases h1 : n < 1 <;> by_cases h2 : 1 < n <;> by_cases h3 : n < 100 <;>
    simp [h1, h2, h3, toString] <;> rfl

/-- The optimised statement of `test1` is exactly the one of
    `Tests/SnapshotsPBOPure/CaseGuarded-Term-optimized.txt`: the first test an `if`, the second a
    conditional whose condition is `cond(1 < x2, x2 < 100, false)` (printed `1 < n && n < 100`
    in JavaScript), both strings computed by `lean_int_repr` (checked with `native_decide`, since
    the printer is compiled code). -/
theorem test1_optimized_pretty :
    ((test1T (Δ := DSig.nil)).optimizeN 3).pretty =
      "val k1 [1] : (Int → String) := fun x2 [ω] : Int => (closed)\n" ++
      "  if lean_int_dec_lt(x2, 1) then\n" ++
      "    ret lean_string_append__String_append(\"n: \", lean_int_repr(x2))\n" ++
      "  else\n" ++
      "    ret cond(cond(lean_int_dec_lt(1, x2), lean_int_dec_lt(x2, 100), false), " ++
      "lean_string_append__String_append(\"1 < x < 100: \", lean_int_repr(x2)), \"catch\")\n" ++
      "ret k1" := by
  native_decide

end CaseGuardedTest

end
