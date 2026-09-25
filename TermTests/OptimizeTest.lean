module

public import LeanScript.Eval
-- The kernel checks of `Lean.Name.beq` below need its body, which `Init` does not expose.
import all Init.Prelude
public import LeanScript.Ty.Instances
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-!
# Optimizing a term written by hand: `#leanscript_optimize`

`Term.extern` is a constructor, so it can only *check* that its extern is not a redex; it
cannot turn itself into the value.  `#leanscript_optimize t` does: the redexes of `t` are
reduced while the term is built, exactly as `#leanscript_to_term` does.
-/

namespace TermTests.Optimize

open LeanScript

/-- `"ab".toList`, written as an extern, is the list literal `['a', 'b']`. -/
def abList := (#leanscript_optimize (.extern (.lean_string_data__String_toList "ab")) :
  Term ⟨[], rfl⟩ [] _ (TyWf.list (.prim .char)) _)

-- no extern is left: the root is a constructor of the list
example : abList = (.recTaggedUnion_mk _ _ _ _ :
    Term ⟨[], rfl⟩ [] _ (TyWf.list (.prim .char)) _) := rfl

example : Ty.DenRec.toList (.prim .char) (Term.run' abList) = ['a', 'b'] := by decide

/-- `Nat.add 2 3`, written as an extern, is the literal `5`. -/
example : (#leanscript_optimize (.extern (.lean_nat_add 2 3)) :
    Term ⟨[], rfl⟩ [] _ (.prim .nat) _) = .nat_mk 5 := rfl

/-- An extern applied to literals (`Term.externCall`) is its value too. -/
example : (#leanscript_optimize (.externCall (.cons (.nat_mk 2) (.cons (.nat_mk 3) .nil))
      (fun vs => .lean_nat_add vs.1 vs.2.1)) :
    Term ⟨[], rfl⟩ [] _ (.prim .nat) _) = .nat_mk 5 := rfl

/-- Redexes nested under a `fun`: `fun n => n + ("ab".length)` becomes `fun n => n + 2`. -/
def addLen := (#leanscript_optimize
    (.lam (.externCall (.cons (.var .head)
      (.cons (.extern (.lean_string_length__String_length "ab")) .nil))
      (fun vs => .lean_nat_add vs.1 vs.2.1))) :
  Term ⟨[], rfl⟩ [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) _)

example : addLen = .lam (.externCall (.cons (.var .head) (.cons (.nat_mk 2) .nil))
      (fun vs => .lean_nat_add vs.1 vs.2.1)) := rfl

example : Term.run' addLen 3 = 5 := rfl

/-- An extern that answers with a function cannot be written as a value: it stays. -/
example : ((#leanscript_optimize (.extern (.lean_array_fget ((TyWf.prim .nat ⇒ TyWf.prim .nat : TyWf))
      #[fun n => n + 1] 0 (by decide))) :
    Term ⟨[], rfl⟩ [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) _) matches .extern _ _) = true := rfl

-- An error that is not a side condition is still reported.
/--
error: Application type mismatch: The argument
  "ab"
has type
  String
but is expected to have type
  Nat
in the application
  LeanInitPureExtern.lean_nat_add "ab"
-/
#guard_msgs in
example := (#leanscript_optimize (.extern (.lean_nat_add "ab" 3)) :
  Term ⟨[], rfl⟩ [] _ (.prim .nat) _)

end TermTests.Optimize
