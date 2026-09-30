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
# `test1` of `Tests/SnapshotsPBOPure/CasePartial.lean`, formally

`panic! msg` is `panicCore msg`, which the translation calls as the extern `lean_panic_fn` on
the default of the `Inhabited` instance and the message: an entry of the catalogue whose
meaning is the Lean function itself, the default (`PreludeExtern.eval`).  The JavaScript throws
the message instead (`JsBlock.retOrRaise`); Lean's runtime prints it and goes on with the
default, which is what the language computes.

* `eval_lean_panic_fn`: the meaning of the extern is `panicCore`.
* `test1_optimized_run`: for **every** `n`, the optimised statement (`Term.optimizeN 3`, the
  `Term → Term` phase of the pipeline) computes `test1 n` (the default `0` where it panics).
* `test1_optimized_pretty`: the optimised statement is the one of
  `CasePartial-Term-optimized.txt` (the message's literals merged into one, across
  `String.Internal.append`, with which `mkPanicMessageWithDecl` appends).
-/

namespace CasePartialTest

open LeanScript

def test1 : Int → Int
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | n => panic! ("mypanic " ++ toString n)

def test1T := #leanscript_to_term test1

/-- The meaning of the extern `lean_panic_fn` is `panicCore`: the default (the message is only
    printed by Lean's runtime). -/
theorem eval_lean_panic_fn (d : Ty.den DSig.nil.refDen (.prim .int))
    (msg : Ty.den DSig.nil.refDen (.prim .string)) :
    Extern.eval DSig.nil.refDen (LeanInitPureExtern.lean_panic_fn (.prim .int))
      (Tuple.cons d (Tuple.cons msg PUnit.unit)) = @panicCore Int ⟨d⟩ msg := rfl

/-- The translated statement of `test1`, run on `n`: its three tests, and the default `0` of the
    panic. -/
theorem test1T_run (n : Int) : (test1T (Δ := DSig.nil)).run n =
    ((match decide (n = 1) with
    | true => 1
    | false =>
      match decide (n = 2) with
      | true => 2
      | false =>
        match decide (n = 3) with
        | true => 3
        | false => 0) : Int) := by kernel_rfl

/-- For **every** `n`, the optimised statement of `test1` computes `test1 n`. -/
theorem test1_optimized_run (n : Int) :
    ((test1T (Δ := DSig.nil)).optimizeN 3).run n = test1 n := by
  rw [Term.optimizeN_run, test1T_run]
  unfold test1
  by_cases h1 : n = 1
  · subst h1; rfl
  by_cases h2 : n = 2
  · subst h2; rfl
  by_cases h3 : n = 3
  · subst h3; rfl
  simp only [h1, h2, h3, decide_false]
  rfl

/-- The optimised statement of `test1` is the one of
    `Tests/SnapshotsPBOPure/CasePartial-Term-optimized.txt`, up to the module name in the message
    (checked with `native_decide`, since the printer is compiled code): the three tests, the
    last one a conditional whose other arm is the panic, its message one append of a literal
    and `toString n` (the literals of `mkPanicMessageWithDecl` and of `"mypanic " ++ …` merged,
    across `String.Internal.append`). -/
theorem test1_optimized_pretty :
    let p := ((test1T (Δ := DSig.nil)).optimizeN 3).pretty
    p.startsWith
      ("val k1 [1] : (Int → Int) := fun x2 [ω] : Int => (closed)\n" ++
      "  if lean_int_dec_eq(x2, 1) then\n" ++
      "    ret 1\n" ++
      "  else\n" ++
      "    if lean_int_dec_eq(x2, 2) then\n" ++
      "      ret 2\n" ++
      "    else\n" ++
      "      ret cond(lean_int_dec_eq(x2, 3), 3, lean_panic_fn(0, " ++
      "lean_string_append__String_append(\"PANIC at CasePartialTest.test1 ") = true ∧
    p.endsWith ":40:9: mypanic \", lean_int_repr(x2))))\nret k1" = true ∧
    (p.splitOn "lean_string_append").length = 2 := by
  native_decide

end CasePartialTest

end
