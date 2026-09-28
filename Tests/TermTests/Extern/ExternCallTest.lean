module

public import LeanScript.Term.Build
public import LeanScript.Term.Extern.Shorthands
public meta import LeanScript.Term.Semantics.Eval
public meta import LeanScript.Term.Extern.Shorthands

@[expose] public section

set_option autoImplicit false

/-!
# Calls of externs (`Neu.extern`)

An extern is an entry of the catalogue `LeanInitPureExtern` (instantiated to the types of the
language: `Extern ks σs τ`), not a name: the call holds the entry and the pure expressions of
its arguments.  There is one kind of extern and one way to use it, the call: an extern that
builds a value (`Array.emptyWithCapacity`) is called exactly like one that computes with values
(`String.contains`).  Each entry `c` has the term formers `PExpr.c` and `Neu.c`.

In the grammar of normal forms a call is a *neutral* expression, so at least one of its
arguments is open (mentions an unknown).  A call on closed arguments only is computed when the
term is built, and written as a literal (`PExpr.externLit`).
-/

namespace ExternCallTest

open LeanScript

/-- Pure expressions over no datatypes, with the unknowns `Γ`. -/
abbrev P (Γ : UCtx []) (τ : Ty []) (ℓ : Nat) : Type := PExpr (ks := []) .nil [] Γ τ (some ℓ)

/-- The innermost unknown. -/
abbrev x0 {τ : Ty []} {Γ : UCtx []} : PExpr (ks := []) .nil [] (⟨τ, .many, 0⟩ :: Γ) τ (some 0) :=
  .neu (.var (.head (by decide)))

/-- One unknown string. -/
abbrev S : UCtx [] := [⟨.prim .string, .many, 0⟩]

/-- `s.contains '4'`, for an unknown string `s`. -/
def containsT : P S .bool 0 := PExpr.lean_string_contains x0 (.lit .char '4')

/-- The term former is the call of the entry on its arguments. -/
example : containsT =
    .neu (.extern .lean_string_contains (.cons x0 (.cons (.lit .char '4') .nil)) rfl) := rfl

#guard id (α := Bool) (containsT.eval PUnit.unit ("12345" : String)) == true
#guard id (α := Bool) (containsT.eval PUnit.unit ("12395" : String)) == false

/-- The call on literals only cannot be written as a call… -/
example : True := by
  fail_if_success
    have : P [] .bool 0 := PExpr.lean_string_contains (.lit .string "12345") (.lit .char '4')
  trivial

/-- …it is computed, and written as a literal. -/
example : (PExpr.externLit (Δ := .nil) (Φ := []) (Γ := []) .lean_nat_add
    (.cons (.lit .nat 3) (.cons (.lit .nat 4) .nil))) = .lit .nat 7 := rfl

/-- `String.Internal.any s f` where the predicate `f : Char → Bool` is an unknown too (a
    function is a value of the language, so it is an argument like any other). -/
def anyT : P [⟨.fn (.prim .char) .bool, .many, 0⟩] .bool 0 :=
  PExpr.lean_string_any (.lit .string "12345") x0

#guard id (α := Bool) (anyT.eval PUnit.unit (fun (c : Char) => c == '4')) == true
#guard id (α := Bool) (anyT.eval PUnit.unit (fun (c : Char) => c == 'x')) == false

/-- Numerals: `n + 4`. -/
def addT : P [⟨.nat, .many, 0⟩] .nat 0 := PExpr.lean_nat_add x0 (.lit .nat 4)
example : id (α := Nat) (addT.eval PUnit.unit (3 : Nat)) = 7 := rfl

/-- A value built by externs: `#[].push n |>.push 2`.  The type argument of the entry
    (`αt`) comes first. -/
def arrT : P [⟨.nat, .many, 0⟩] (.array .nat) 0 :=
  PExpr.lean_array_push .nat
    (PExpr.lean_array_push .nat
      (.array_mk .nil) x0) (.lit .nat 2)

#guard id (α := Array Nat) (arrT.eval PUnit.unit (1 : Nat)) == #[1, 2]

end ExternCallTest

end
