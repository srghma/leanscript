module

public import LeanScript.Expr.Term
public import LeanScript.Eval
-- The kernel checks of `Lean.Name.beq` below need its body, which `Init` does not expose.
import all Init.Prelude

/-!
# Externs as terms

`Term.extern` holds a pure extern of `Init` applied to its arguments (and to the proofs it
takes), and `Term.eval` gives it the value of the Lean function it implements, called on
them.  Each check below is settled by the kernel.

The catalogue is in two levels (a family of entries per section of `Init`, and
`LeanInitPureExtern` with one constructor per family), so no inductive has more
constructors than compiled code can build (the runtime keeps a constructor's number in
8 bits, and only `0 … 243` are for ordinary constructors): a *definition* may build any
entry, `lean_string_compare` included (`externCompare` below).
-/

namespace TermTests

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

/-- An extern whose result is an array: arrays denote Lean arrays. -/
example : Term.run' (.extern (.lean_array_push (TyWf.prim .nat) #[1, 2] 3) :
    Term ⟨[], rfl⟩ [] (.array (.prim .nat))) = #[1, 2, 3] := rfl

/-- `String.compare "a" "b"`, as a (compiled) definition.  `lean_string_compare` is the last
    entry of the catalogue; with the catalogue in one inductive of 460 constructors, its
    number (459) was too big for compiled code, and this definition did not compile. -/
def externCompare : Term ⟨[], rfl⟩ [] TyWf.ordering := .extern (.lean_string_compare "a" "b")

example : Term.run' externCompare = TyWf.Den.ofOrdering (String.compare "a" "b") := rfl

/-- An entry is written through its shorthand, `.lean_nat_add 2 3`, which unfolds to the
    constructor of its family wrapped in the one of the catalogue. -/
example : (.lean_nat_add 2 3 : Extern (.prim .nat)) = .preludeExtern (.lean_nat_add 2 3) := rfl

/-- The shorthands are patterns too. -/
def isNatAdd : {τ : TyWf} → Extern τ → Bool
  | _, .lean_nat_add _ _ => true
  | _, _ => false

example : isNatAdd (.lean_nat_add 2 3 : Extern (.prim .nat)) = true := by decide
example : isNatAdd (.lean_nat_sub 2 3 : Extern (.prim .nat)) = false := by decide

/-- An extern whose result is an `Ordering`: the enum with three constructors. -/
example (a b : String) : Term.run' (.extern (.lean_string_compare a b) :
    Term ⟨[], rfl⟩ [] TyWf.ordering) = TyWf.Den.ofOrdering (String.compare a b) := rfl

/-- An extern whose result is an `Option`: the tagged union `none | some α`. -/
example : Term.run' (.extern (.lean_string_utf8_get_opt__String_Pos_Raw_get? "ab" ⟨1⟩) :
    Term ⟨[], rfl⟩ [] (TyWf.option (.prim .char))) = TyWf.Den.ofOption (α := .prim .char) (some 'b') :=
  rfl

/-- An extern that takes a proof holds it: `Array.getInternal #[1, 2, 3] 1 h`, with the
    proof `h : 1 < #[1, 2, 3].size`, is `Array.getInternal` called with that proof. -/
example : Term.run' (.extern (.lean_array_fget (TyWf.prim .nat) #[1, 2, 3] 1 (by decide)) :
    Term ⟨[], rfl⟩ [] (.prim .nat)) = 2 := by decide

/-- `String.Pos.next`: its argument is a position into the string `s`, whose type names
    `s`, so `s` is a parameter of the entry, fixed where the term is written. -/
example : Term.run' (.extern (.lean_string_utf8_next_fast__String_Pos_next
      ("ab" : String).startPos (by decide)) :
    Term ⟨[], rfl⟩ [] (.prim (.stringPos "ab"))) = ("ab" : String).startPos.next (by decide) :=
  rfl

/-- `Lean.Name.beq`: a `Lean.Name` is the recursive tagged union
    `anonymous | str self String | num self Nat` (`TyWf.leanName`). -/
example : Term.run' (.extern (.lean_name_eq (TyWf.Den.ofName `a.b) (TyWf.Den.ofName `a.b)) :
    Term ⟨[], rfl⟩ [] (.prim .bool)) = true := by decide +kernel

example : Term.run' (.extern (.lean_name_eq (TyWf.Den.ofName `a.b) (TyWf.Den.ofName `a.«1»)) :
    Term ⟨[], rfl⟩ [] (.prim .bool)) = false := by decide +kernel

example : tyWfOf Lean.Name = TyWf.leanName := rfl

/-- An extern whose result is a pair: the record of its two fields.  `Float.frExp` does not
    reduce in the kernel, so this only checks that the value is the pair `Float.frExp`
    answers with. -/
example (x : Float) : Term.run' (.extern (.lean_float_frexp x) :
    Term ⟨[], rfl⟩ [] (TyWf.prod (.prim .float) (.prim .int))) =
      TyWf.Den.ofProd (α := .prim .float) (β := .prim .int) (Float.frExp x) := rfl

/-- An extern whose result is a list: the recursive tagged union `nil | cons α self`, the
    model of `List`; `Ty.DenRec.toList` reads it back. -/
example : Ty.DenRec.toList (.prim .nat) (Term.run' (.extern (.lean_array_to_list (TyWf.prim .nat)
    #[1, 2, 3]) : Term ⟨[], rfl⟩ [] (TyWf.list (.prim .nat)))) = [1, 2, 3] := by decide

example : Ty.DenRec.toList (.prim .char) (Term.run' (.extern (.lean_string_data__String_toList "ab") :
    Term ⟨[], rfl⟩ [] (TyWf.list (.prim .char)))) = ['a', 'b'] := by decide

/-! ## The derived type formers are the models of the Lean types

The externs use the same model of `List`, `Option`, `×` and `Ordering` as the rest of the
language: the model `LeanScriptTyWf` gives the Lean type. -/

example : tyWfOf (List Nat) = TyWf.list (.prim .nat) := rfl
example : tyWfOf (Option Char) = TyWf.option (.prim .char) := rfl
example : tyWfOf (Float × Int) = TyWf.prod (.prim .float) (.prim .int) := rfl
example : tyWfOf Ordering = TyWf.ordering := rfl
example : tyOf Ordering = .enum ⟨0, -1⟩ := rfl

end TermTests
