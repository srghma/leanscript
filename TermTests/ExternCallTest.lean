module

public import LeanScript.Term.Build
public import LeanScript.Term.ExternShorthands
public meta import LeanScript.Term.Eval
public meta import LeanScript.Term.ExternShorthands

@[expose] public section

set_option autoImplicit false

/-!
# Calls of externs (`Neu.extern`)

An extern is an entry of the catalogue `LeanInitPureExtern` (instantiated to the types of the
language: `Extern ks σs τ`), not a name: the call holds the entry and the pure expressions of
its arguments.  There is one kind of extern and one way to use it, the call: an extern that
builds a value (`Array.emptyWithCapacity`, a constant such as `Lean.version.getMajor`) is called
exactly like one that computes with values (`String.contains`).  Each entry `c` has the term
formers `PExpr.c` and `Neu.c`, and Lean literals may be written for literal arguments.
-/

namespace ExternCallTest

open LeanScript

/-- The closed programs over no datatypes. -/
abbrev P (τ : Ty []) : Type := PExpr (ks := []) .nil [] τ

/-- `"12345".contains '4'`, with the arguments written as Lean literals. -/
def containsT : P .bool := PExpr.lean_string_contains "12345" '4'

/-- The same call, with the literals written out. -/
example : containsT = PExpr.lean_string_contains (.lit .string "12345") (.lit .char '4') := rfl

/-- The term former is the call of the entry on its arguments. -/
example : containsT =
    .neu (.extern .lean_string_contains
      (.cons (.lit .string "12345") (.cons (.lit .char '4') .nil))) := rfl

#guard id (α := Bool) (containsT.eval ()) == true
#guard id (α := Bool) ((PExpr.lean_string_contains (Δ := .nil) (Γ := []) "12345" '9').eval ()) == false

/-- `String.Internal.any "12345" f` where the predicate `f : Char → Bool` is a variable (a
    function is a value of the language, so it is an argument like any other). -/
def anyT : PExpr (ks := []) .nil [.fn (.prim .char) .bool] .bool :=
  PExpr.lean_string_any "12345" (.bvar 0)

#guard id (α := Bool) (anyT.eval (fun (c : Char) => c == '4')) == true
#guard id (α := Bool) (anyT.eval (fun (c : Char) => c == 'x')) == false

/-- Numerals and booleans. -/
def addT : P .nat := PExpr.lean_nat_add 3 4
example : id (α := Nat) (addT.eval ()) = 7 := rfl

/-- A value built by externs: `(Array.emptyWithCapacity 2).push 1 |>.push 2`.  The type
    argument of the entry (`αt`) comes first. -/
def arrT : P (.array .nat) :=
  PExpr.lean_array_push .nat
    (PExpr.lean_array_push .nat
      (PExpr.lean_mk_empty_array_with_capacity__Array_emptyWithCapacity .nat 2) 1) 2

#guard id (α := Array Nat) (arrT.eval ()) == #[1, 2]

/-- An extern with no argument is called on no argument. -/
def majorT : P (.lazy (.prim .nat)) := PExpr.lean_version_get_major

#guard id (α := Nat) (majorT.eval ()) == Lean.version.major

end ExternCallTest

end
