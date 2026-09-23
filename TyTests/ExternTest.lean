module

public import LeanScript.Expr.Term
public import LeanScript.Eval

/-!
# Externs as terms

`Term.extern` holds a pure extern of `Init` applied to its arguments, and `Term.eval`
gives it the value of the Lean function it implements.  Each check below is settled by the
kernel.
-/

namespace TyTests

open LeanScript

/-- `Nat.add 2 3`, as a term. -/
def externAdd : Term ⟨[], rfl⟩ [] (.prim .nat) := .extern (.lean_nat_add 2 3)

example : Term.run' externAdd = 5 := by decide

/-- An extern used inside a larger term: `if 2 < 3 then 7 * 6 else 0`. -/
def externIf : Term ⟨[], rfl⟩ [] (.prim .nat) :=
  .bool_casesOn (.extern (.lean_nat_dec_lt 2 3)) (.extern (.lean_nat_mul 7 6)) (.nat_mk 0)

example : Term.run' externIf = 42 := by decide

/-- An extern applied through a `let`: the bound value is an extern, the body a variable. -/
def externLet : Term ⟨[], rfl⟩ [] (.prim .string) :=
  .letE (.extern (.lean_string_append__String_append "lean" "script")) (.var .head)

example : Term.run' externLet = "leanscript" := by decide

/-- An extern of `UInt32`. -/
example : Term.run' (.extern (.lean_uint32_add 4000000000 500000000) :
    Term ⟨[], rfl⟩ [] (.prim .uint32)) = 205032704 := by decide

/-- An extern whose result is an array: arrays denote lists. -/
example : Term.run' (.extern (.lean_array_push (TyWf.prim .nat) #[1, 2] 3) :
    Term ⟨[], rfl⟩ [] (.array (.prim .nat))) = [1, 2, 3] := by decide

/-- An extern whose result is an `Ordering`: the enum with three constructors. -/
example (a b : String) : Term.run' (.extern (.lean_string_compare a b) :
    Term ⟨[], rfl⟩ [] TyWf.ordering) = TyWf.Den.ofOrdering (String.compare a b) := rfl

/-- An extern whose result is an `Option`: the tagged union `none | some α`. -/
example : Term.run' (.extern (.lean_string_utf8_get_opt__String_Pos_Raw_get? "ab" ⟨1⟩) :
    Term ⟨[], rfl⟩ [] (TyWf.option (.prim .char))) = TyWf.Den.ofOption (some 'b') :=
  rfl

/-- `Nat.gcd`, as a term. -/
example : Term.run' (.extern (.lean_nat_gcd__Nat_gcd 12 18) :
    Term ⟨[], rfl⟩ [] (.prim .nat)) = 6 := by decide

/-- An extern whose result is a pair: the record of its two fields.  `Float.frExp` does not
    reduce in the kernel, so this only checks that the value is the pair `Float.frExp`
    answers with. -/
example (x : Float) : Term.run' (.extern (.lean_float_frexp x) :
    Term ⟨[], rfl⟩ [] (TyWf.prod (.prim .float) (.prim .int))) =
      TyWf.Den.ofProd (α := .prim .float) (β := .prim .int) (Float.frExp x) := rfl

end TyTests
