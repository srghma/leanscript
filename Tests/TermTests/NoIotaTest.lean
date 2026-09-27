module

public import LeanScript.TermElab.Notation
public import TermTests.TermTest
public meta import LeanScript.TermElab.ToTerm

@[expose] public section

set_option autoImplicit false

/-!
# No ι-redexes (`LeanScript.Neu`)

The grammar of `LeanScript.Term` rules out the elimination of an explicitly constructed value:
everything that takes a value apart takes a *neutral* expression (`Neu`: a variable, an
elimination of a neutral expression, an extern), never a literal nor a constructor.

1. The kinds of ι-redex do not type-check, not even on a *known* value (bound by `letV`): a
   known value is never taken apart.
2. The notation and the translator reduce the ι-redexes of the source while normalising.
-/

namespace NoIotaTest

open LeanScript TermTest

/-! ## 1. The grammar rules ι-redexes out -/

/-- A pair of numbers. -/
abbrev pairT : Ty [0, 0] := .record .nat (.one .nat)

/-- The pair `(1, 2)`. -/
def pair12 {Φ : KCtx [0, 0]} {Γ : UCtx [0, 0]} : PExpr Δ Φ Γ pairT none :=
  .record_mk (.cons (natT 1) (.cons (natT 2) .nil))

/-- Data unfolding: `data_out b j (data_in b j e)`, and `data_out` of a known value. -/
example : True := by
  fail_if_success
    have : PExpr Δ [] [] ((Δ.block listB).unfold 0) (some 0) := .neu (.data_out listB 0 nilT)
  fail_if_success
    have : Neu Δ [⟨listNat, .one, none, true⟩] [] ((Δ.block listB).unfold 0) 0 :=
      .data_out listB 0 (.kvar .head)
  trivial

/-- Record elimination: `record_casesOn (record_mk args) body`, or of a known record. -/
example : True := by
  fail_if_success
    have : Term Δ 0 [] [] .nat [] (some 0) := .record_casesOn [] pair12 (.ret (natT 0))
  fail_if_success
    have : Term Δ 0 [] [] .nat [] (some 0) :=
      .letV .one pair12 (.record_casesOn [] (.kvar .head) (.ret (natT 0)))
  trivial

/-- `some 3`. -/
def some3 {Φ : KCtx [0, 0]} {Γ : UCtx [0, 0]} : PExpr Δ Φ Γ (.option .nat) none :=
  .union_mk .two₂ (.cons (natT 3) .nil)

/-- Union elimination: `union_casesOn (union_mk ix args) branches`. -/
example : True := by
  fail_if_success
    have : Branch Δ 0 [] [] .nat [] 0 := .union_casesOn some3 (.two [] [] (.ret (natT 0)) (.ret (natT 1)))
  trivial

/-- Conditions on a literal: `cond (lit .bool true) a b`, `ite (lit .bool true) t e`, and an
    enum case analysis of a constructor. -/
example : True := by
  fail_if_success
    have : Neu Δ [] [] .nat 0 := .cond (.lit .bool true) (natT 1) (natT 2)
  fail_if_success
    have : Branch Δ 0 [] [] .nat [] 0 := .ite (.lit .bool true) (.ret (natT 1)) (.ret (natT 2))
  fail_if_success
    have : Branch Δ 0 [] [] .nat [] 0 := .enum_casesOn (.enum_mk {} 0) (fun _ => .ret (natT 1))
  trivial

/-- The values taken apart above are well-typed pure expressions: only their elimination is
    ruled out. -/
example : PExpr Δ [] [] .bool none := .lit .bool true
example : PExpr Δ [] [] (.enum {}) none := .enum_mk {} 0

-- [SKIPPED BY PROFILE_LAKE] /-- The same eliminations of an unknown are fine. -/
-- [SKIPPED BY PROFILE_LAKE] example : Term Δ 0 [] [⟨pairT, .one, 0⟩] .nat [] (some 0) :=
-- [SKIPPED BY PROFILE_LAKE]   .record_casesOn (t := .nat) (fs := .one .nat) [.zero, .one] (.var (.head (by decide)))
-- [SKIPPED BY PROFILE_LAKE]     (.ret (.neu (.var (.tail (.head (u := Usage01ω.one) (by decide))))))
-- [SKIPPED BY PROFILE_LAKE] example : Neu Δ [] [⟨.bool, .one, 0⟩] .nat 0 := .cond (.var (.head (by decide))) (natT 1) (natT 2)
-- [SKIPPED BY PROFILE_LAKE] example : Neu Δ [] [⟨listNat, .one, 0⟩] ((Δ.block listB).unfold 0) 0 :=
-- [SKIPPED BY PROFILE_LAKE]   .data_out listB 0 (.var (.head (by decide)))

/-! ## 2. The notation reduces the ι-redexes of the source -/

-- [SKIPPED BY PROFILE_LAKE] example : ([Term| let (_, _) := (1, 2); #1] : Prog .nat) = .ret (natT 2) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Term| if true then 1 else 2] : Prog .nat) = .ret (natT 1) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Term| cond false 1 2] : Prog .nat) = .ret (natT 2) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Term| match enum_mk 2 with | 0 => 10 | 1 => 11 | _ => 12] : Prog .nat) =
-- [SKIPPED BY PROFILE_LAKE]     .ret (natT 12) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Term| match union_mk 1 7 with | · => 0 | _ => #0] : Prog .nat) = .ret (natT 7) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Term| data_out ‹listB› 0 (data_in ‹listB› 0 #0)] :
-- [SKIPPED BY PROFILE_LAKE]     Term Δ 0 [] [⟨(Δ.block listB).unfold 0, .many, 0⟩] ((Δ.block listB).unfold 0) [] (some 0)) =
-- [SKIPPED BY PROFILE_LAKE]     .ret (.neu (.var (.head (by decide)))) := rfl

-- A value of unknown shape (a Lean term) cannot be taken apart while normalising.
/--
error: cannot take apart a value of unknown shape (a Lean term) while normalising: the scrutinee of a record
-/
#guard_msgs in
example : Prog .nat := [Term| let (_, _) := ‹pair12›; #1]

/-! ## The translator -/

/-- A `match` on a pair just built. -/
def fstOfPair (a b : Nat) : Nat := match (a, b) with | (x, _) => x
def fstOfPairT := #leanscript_to_term fstOfPair
-- [SKIPPED BY PROFILE_LAKE] example : (fstOfPairT (Δ := DSig.nil)).run (3 : Nat) (4 : Nat) = fstOfPair 3 4 := rfl

/-- A `match` on a literal. -/
def onTrue (n : Nat) : Nat := match true with | true => n | false => 0
def onTrueT := #leanscript_to_term onTrue
-- [SKIPPED BY PROFILE_LAKE] example : (onTrueT (Δ := DSig.nil)).run (5 : Nat) = onTrue 5 := rfl

end NoIotaTest

end
