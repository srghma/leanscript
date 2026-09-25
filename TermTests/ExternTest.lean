module

public import LeanScript.Expr.Term
public import LeanScript.Eval
-- The kernel checks of `Lean.Name.beq` below need its body, which `Init` does not expose.
import all Init.Prelude

/-!
# Externs as terms

`LeanScript.Extern` is a pure extern of `Init` applied to its arguments (and to the proofs
it takes), and `Extern.eval` gives it the value of the Lean function it implements, called
on them.  `Term.extern` holds one — but only when its value cannot be written as a term
(`TyWf.quotable`): an extern on values whose result holds no function (a literal, an enum
constructor, a list, an option, a pair, …) is a redex, and the grammar asks for the value
instead.  Only an extern that answers with a function, or with a value holding one, is
left as `Term.extern`.
Each check below is settled by the kernel.

The catalogue is in two levels (a family of entries per section of `Init`, and
`LeanInitPureExtern` with one constructor per family), so no inductive has more
constructors than compiled code can build (the runtime keeps a constructor's number in
8 bits, and only `0 … 243` are for ordinary constructors): a *definition* may build any
entry, `lean_string_compare` included (`externCompare` below).
-/

namespace TermTests

open LeanScript

/-- The value of an extern on values: `Extern.eval`, the Lean function called on them. -/
example : Extern.eval (τ := TyWf.prim .nat) (.lean_nat_add 2 3) = 5 := by decide

-- `Nat.add 2 3` is **not** a term: its value can be written (`5` is a literal), so the
-- call is a redex, and the grammar asks for the value instead.
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  (TyWf.prim LeanPrimTy.nat).quotable = false
is false
-/
#guard_msgs in
example := (.extern (.lean_nat_add 2 3) : Term ⟨[], rfl⟩ [] _ (.prim .nat) .comp)

-- Nor is an extern on values that answers with a list (`"ab".toList` is `['a', 'b']`), an
-- option, a pair or a checked position: every value of those can be written as a term.
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  (TyWf.prim LeanPrimTy.char).list.quotable = false
is false
-/
#guard_msgs in
example := (.extern (.lean_string_data__String_toList "ab") :
  Term ⟨[], rfl⟩ [] _ (TyWf.list (.prim .char)) .comp)

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  (TyWf.prim (LeanPrimTy.stringPos "ab")).quotable = false
is false
-/
#guard_msgs in
example := (.extern (.lean_string_utf8_next_fast__String_Pos_next ("ab" : String).startPos
    (by decide)) : Term ⟨[], rfl⟩ [] _ (.prim (.stringPos "ab")) .comp)

/-- An extern on values that answers with a **function** stays `Term.extern`: a function
    cannot be read back as a term.  (Here the element of an array of functions.) -/
example : (Term.run' (.extern (.lean_array_fget ((TyWf.prim .nat ⇒ TyWf.prim .nat : TyWf))
      #[fun n => n + 1] 0 (by decide)) :
    Term ⟨[], rfl⟩ [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .comp)) 4 = 5 := rfl

-- Nor is an extern applied to terms that are all literals (`Term.externCall`).
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  Head.allValue [Head.lit, Head.lit] = false
is false
---
error: could not synthesize default value for parameter 'hClosed' using tactics
---
error: Tactic `decide` proved that the proposition
  Head.closedComp (0 + (0 + 0)) (TyWf.prim LeanPrimTy.nat) Head.comp = false
is false
-/
#guard_msgs in
example := (.externCall (.cons (.nat_mk 2) (.cons (.nat_mk 3) .nil))
    (fun vs => .lean_nat_add vs.1 vs.2.1) : Term ⟨[], rfl⟩ [] _ (.prim .nat) .comp)

-- Nor `somearray[1]'h` on an array literal (`Term.externCallChecked`): an array of
-- literals is a closed value (`Head.val`).
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  Head.allValue [Head.ctorOf [Head.lit, Head.lit, Head.lit], Head.lit] = false
is false
---
error: could not synthesize default value for parameter 'hClosed' using tactics
---
error: Tactic `decide` proved that the proposition
  Head.closedComp (0 + (0 + (0 + 0)) + (0 + 0) + 0) (TyWf.prim LeanPrimTy.nat) Head.comp = false
is false
-/
#guard_msgs in
example := (.externCallChecked
    (.cons (.array_mk (.cons (.nat_mk 1) (.cons (.nat_mk 2) (.cons (.nat_mk 3) .nil))))
      (.cons (.nat_mk 1) .nil))
    (fun vs => if h : vs.2.1 < vs.1.size then some (.lean_array_fget (TyWf.prim .nat) vs.1 vs.2.1 h)
      else none)
    (.nat_mk 0) : Term ⟨[], rfl⟩ [] _ (.prim .nat) .comp)

/-- `fun n => n + 3`: an extern applied to a term that is not a value. -/
def externAdd :=
  (.lam (.externCall (.cons (.var .head) (.cons (.nat_mk 3) .nil))
      (fun vs => .lean_nat_add vs.1 vs.2.1)) :
    Term ⟨[], rfl⟩ [] _ (.prim .nat ⇒ .prim .nat) .lam)

example : (Term.run' externAdd) 2 = 5 := by decide

/-- An extern used inside a larger term: `fun n => if n < 3 then n * 6 else 0`. -/
def externIf :=
  (.lam (.bool_casesOn
      (.externCall (.cons (.var .head) (.cons (.nat_mk 3) .nil))
        (fun vs => .lean_nat_dec_lt vs.1 vs.2.1))
      (.externCall (.cons (.var .head) (.cons (.nat_mk 6) .nil))
        (fun vs => .lean_nat_mul vs.1 vs.2.1))
      (.nat_mk 0)) :
    Term ⟨[], rfl⟩ [] _ (.prim .nat ⇒ .prim .nat) .lam)

example : (Term.run' externIf) 2 = 12 := by decide
example : (Term.run' externIf) 7 = 0 := by decide

/-- An extern applied through a `let`: the bound value is an extern, and the body uses it
    twice — a `let` whose variable is used once is a redex, and is not a term. -/
def externLet :=
  (.lam (.letE (.externCall (.cons (.var .head) (.cons (.string_mk "script") .nil))
      (fun vs => .lean_string_append__String_append vs.1 vs.2.1))
     (.externCall (.cons (.var .head) (.cons (.var .head) .nil))
       (fun vs => .lean_string_append__String_append vs.1 vs.2.1))) :
    Term ⟨[], rfl⟩ [] _ (.prim .string ⇒ .prim .string) .lam)

example : (Term.run' externLet) "lean" = "leanscriptleanscript" := by decide

/-- An extern of `UInt32`. -/
example : Extern.eval (τ := TyWf.prim .uint32) (.lean_uint32_add 4000000000 500000000) =
    205032704 := by decide

/-- An extern whose result is an array: arrays denote Lean arrays. -/
example : (Extern.eval (.lean_array_push (TyWf.prim .nat) #[1, 2] 3 :
    Extern (TyWf.array (TyWf.prim .nat))) : Array Nat) = #[1, 2, 3] := rfl

/-- `String.compare "a" "b"`, as a (compiled) definition.  `lean_string_compare` is the last
    entry of the catalogue; with the catalogue in one inductive of 460 constructors, its
    number (459) was too big for compiled code, and this definition did not compile. -/
def externCompare : Extern TyWf.ordering := .lean_string_compare "a" "b"

example : Extern.eval externCompare = TyWf.Den.ofOrdering (String.compare "a" "b") := rfl

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
example (a b : String) : Extern.eval (.lean_string_compare a b : Extern TyWf.ordering) =
    TyWf.Den.ofOrdering (String.compare a b) := rfl

/-- An extern whose result is an `Option`: the tagged union `none | some α`. -/
example : Extern.eval (.lean_string_utf8_get_opt__String_Pos_Raw_get? "ab" ⟨1⟩ :
    Extern (TyWf.option (.prim .char))) = TyWf.Den.ofOption (α := .prim .char) (some 'b') :=
  rfl

/-- An extern that takes a proof holds it: `Array.getInternal #[1, 2, 3] 1 h`, with the
    proof `h : 1 < #[1, 2, 3].size`, is `Array.getInternal` called with that proof. -/
example : (Extern.eval (.lean_array_fget (TyWf.prim .nat) #[1, 2, 3] 1 (by decide) :
    Extern (TyWf.prim .nat)) : Nat) = 2 := by decide

/-- `String.Pos.next`: its argument is a position into the string `s`, whose type names
    `s`, so `s` is a parameter of the entry, fixed where the term is written. -/
example : Extern.eval (.lean_string_utf8_next_fast__String_Pos_next
      ("ab" : String).startPos (by decide) :
    Extern (.prim (.stringPos "ab"))) = ("ab" : String).startPos.next (by decide) :=
  rfl

/-- `Lean.Name.beq`: a `Lean.Name` is the recursive tagged union
    `anonymous | str self String | num self Nat` (`TyWf.leanName`). -/
example : Extern.eval (τ := TyWf.prim .bool)
    (.lean_name_eq (TyWf.Den.ofName `a.b) (TyWf.Den.ofName `a.b)) = true := by decide +kernel

example : Extern.eval (τ := TyWf.prim .bool)
    (.lean_name_eq (TyWf.Den.ofName `a.b) (TyWf.Den.ofName `a.«1»)) = false := by decide +kernel

example : tyWfOf Lean.Name = TyWf.leanName := rfl

/-- An extern whose result is a pair: the record of its two fields.  `Float.frExp` does not
    reduce in the kernel, so this only checks that the value is the pair `Float.frExp`
    answers with. -/
example (x : Float) : Extern.eval (.lean_float_frexp x :
    Extern (TyWf.prod (.prim .float) (.prim .int))) =
      TyWf.Den.ofProd (α := .prim .float) (β := .prim .int) (Float.frExp x) := rfl

/-- An extern whose result is a list: the recursive tagged union `nil | cons α self`, the
    model of `List`; `Ty.DenRec.toList` reads it back. -/
example : Ty.DenRec.toList (.prim .nat) (Extern.eval (.lean_array_to_list (TyWf.prim .nat)
    #[1, 2, 3] : Extern (TyWf.list (.prim .nat)))) = [1, 2, 3] := by decide

example : Ty.DenRec.toList (.prim .char) (Extern.eval (.lean_string_data__String_toList "ab" :
    Extern (TyWf.list (.prim .char)))) = ['a', 'b'] := by decide

/-! ## The derived type formers are the models of the Lean types

The externs use the same model of `List`, `Option`, `×` and `Ordering` as the rest of the
language: the model `LeanScriptTyWf` gives the Lean type. -/

example : tyWfOf (List Nat) = TyWf.list (.prim .nat) := rfl
example : tyWfOf (Option Char) = TyWf.option (.prim .char) := rfl
example : tyWfOf (Float × Int) = TyWf.prod (.prim .float) (.prim .int) := rfl
example : tyWfOf Ordering = TyWf.ordering := rfl
example : tyOf Ordering = .enum ⟨0, -1⟩ := rfl

end TermTests
