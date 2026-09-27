module

public import LeanScript.Term.TermSubst
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

1. The five kinds of ι-redex do not type-check.
2. Substitution is hereditary: substituting an introduction form for a variable that is taken
   apart reduces the redex on the spot, and still means what the term meant.
3. The notation and the translator reduce the ι-redexes of the source while normalising, and
   share (by a `let`) a value of unknown shape before taking it apart.
-/

namespace NoIotaTest

open LeanScript TermTest

/-! ## 1. The grammar rules ι-redexes out -/

/-- A pair of numbers. -/
abbrev pairT : Ty [0, 0] := .record .nat (.one .nat)

/-- The pair `(1, 2)`. -/
def pair12 {Γ : Ctx [0, 0]} : PExpr Δ Γ pairT := .record_mk (.cons (natT 1) (.cons (natT 2) .nil))

/-- Data unfolding: `data_out b j (data_in b j e)`. -/
example : True := by
  fail_if_success
    have : PExpr Δ [] ((Δ.block listB).unfold 0) := .data_out listB 0 nilT
  fail_if_success
    have : PExpr Δ [] ((Δ.block listB).unfold 0) :=
      .neu (.data_out listB 0 (.data_in listB 0 (.union_mk .two₁ .nil)))
  trivial

/-- Record elimination: `record_casesOn (record_mk args) body`. -/
example : True := by
  fail_if_success
    have : Term Δ [] .nat [] := .record_casesOn pair12 (.ret (.bvar 0))
  fail_if_success
    have : Term Δ [] .nat [] :=
      .record_casesOn (.record_mk (.cons (natT 1) (.cons (natT 2) .nil))) (.ret (.bvar 0))
  trivial

/-- `some 3`. -/
def some3 : PExpr Δ [] (.option .nat) := .union_mk .two₂ (.cons (natT 3) .nil)

/-- Union elimination: `union_casesOn (union_mk ix args) branches`. -/
example : True := by
  fail_if_success
    have : Term Δ [] .nat [] := .union_casesOn some3 (.two (.ret (natT 0)) (.ret (.bvar 0)))
  trivial

/-- Once bound by a `let`, the value is a variable, which may be taken apart. -/
example : Term Δ [] .nat [] :=
  .letE (.share some3) (.union_casesOn (.bvar 0) (.two (.ret (natT 0)) (.ret (.bvar 0))))

/-- Pure and tail conditions on a literal: `cond (lit .bool true) a b`, `ite (lit .bool true) t e`,
    and an enum case analysis of a constructor. -/
example : True := by
  fail_if_success
    have : PExpr Δ [] .nat := .cond (.lit .bool true) (natT 1) (natT 2)
  fail_if_success
    have : PExpr Δ [] .nat := .neu (.cond (.lit .bool true) (natT 1) (natT 2))
  fail_if_success
    have : Term Δ [] .nat [] := .ite (.lit .bool true) (.ret (natT 1)) (.ret (natT 2))
  fail_if_success
    have : Term Δ [] .nat [] := .enum_casesOn (.enum_mk {} 0) (fun _ => .ret (natT 1))
  trivial

/-- The values taken apart above are well-typed pure expressions: only their elimination is
    ruled out. -/
example : PExpr Δ [] .bool := .lit .bool true
example : PExpr Δ [] (.enum {}) := .enum_mk {} 0

/-- The same eliminations of a variable are fine. -/
example : Term Δ [pairT] .nat [] := .record_casesOn (.bvar 0) (.ret (.bvar 1))
example : PExpr Δ [.bool] .nat := .cond (.bvar 0) (natT 1) (natT 2)
example : PExpr Δ [listNat] ((Δ.block listB).unfold 0) := .data_out listB 0 (.bvar 0)

/-! ## 2. Hereditary substitution reduces the redexes it would create -/

/-- The second field of a pair given as a variable. -/
def sndT : Term Δ [pairT] .nat [] := .record_casesOn (.bvar 0) (.ret (.bvar 1))

example : sndT.subst1 pair12 = .ret (natT 2) := rfl

/-- The head of a list given as a variable, or `0`: one layer out, then a union case. -/
def headOr0T : Term Δ [listNat] .nat [] :=
  .union_casesOn (.data_out listB 0 (.bvar 0)) (.two (.ret (natT 0)) (.ret (.bvar 0)))

example : headOr0T.subst1 (consT (natT 7) nilT) = .ret (natT 7) := rfl
example : headOr0T.subst1 nilT = .ret (natT 0) := rfl
/-- Neutral values (here the variables themselves) keep the case analysis. -/
example : headOr0T.subst Subst.id = headOr0T := rfl

/-- A condition given as a variable. -/
def iteT : Term Δ [.bool] .nat [] := .ite (.bvar 0) (.ret (natT 1)) (.ret (natT 2))

example : iteT.subst1 (.lit .bool false) = .ret (natT 2) := rfl
example : (PExpr.cond (.bvar 0) (natT 1) (natT 2) : PExpr Δ [.bool] .nat).subst1
    (.lit .bool true) = natT 1 := rfl

/-- An enum given as a variable. -/
def enumT : Term Δ [.enum {}] .nat [] := .enum_casesOn (.bvar 0) (fun i => .ret (natT i.val))

example : enumT.subst1 (.enum_mk {} 2) = .ret (natT 2) := rfl

/-- The reductions mean what the eliminations meant (`Term.eval_subst1`), for any argument. -/
example (a : PExpr Δ [] listNat) :
    (headOr0T.subst1 a).run = headOr0T.eval (Tuple.cons (a.run) PUnit.unit) PUnit.unit :=
  Term.eval_subst1 _ _ _ _

/-! ## 3. The notation reduces the ι-redexes of the source -/

example : ([Term| let (_, _) := (1, 2); #1] : Term Δ [] .nat []) = .ret (natT 2) := rfl
example : ([Term| if true then 1 else 2] : Term Δ [] .nat []) = .ret (natT 1) := rfl
example : ([Term| cond false 1 2] : PExpr Δ [] .nat) = natT 2 := rfl
example : ([Term| match enum_mk 2 with | 0 => 10 | 1 => 11 | _ => 12] : Term Δ [] .nat []) =
    .ret (natT 12) := rfl
example : ([Term| match union_mk 1 7 #0 with | · => 0 | (_, _) => #0] :
    Term Δ [listNat] .nat []) = .ret (natT 7) := rfl
example : ([Term| data_out ‹listB› 0 (data_in ‹listB› 0 #0)] :
    PExpr Δ [(Δ.block listB).unfold 0] ((Δ.block listB).unfold 0)) = .bvar 0 := rfl

/-- A value of unknown shape (a Lean term) is shared by a `let` before it is taken apart. -/
example : ([Term| let (_, _) := ‹pair12›; #1] : Term Δ [] .nat []) =
    .letE (.share pair12) (.record_casesOn (.bvar 0) (.ret (.bvar 1))) := rfl

/-! ## The translator -/

/-- A `match` on a pair just built. -/
def fstOfPair (a b : Nat) : Nat := match (a, b) with | (x, _) => x
def fstOfPairT := #leanscript_to_term fstOfPair
example : (fstOfPairT (Δ := DSig.nil)).run (3 : Nat) (4 : Nat) = fstOfPair 3 4 := rfl

/-- A `match` on a literal. -/
def onTrue (n : Nat) : Nat := match true with | true => n | false => 0
def onTrueT := #leanscript_to_term onTrue
example : (onTrueT (Δ := DSig.nil)).run (5 : Nat) = onTrue 5 := rfl
/-- The branch is selected while normalising: no case analysis remains. -/
example {ks : List Nat} {Δ : DSig ks} : onTrueT (Δ := Δ) = .ofComp (.lam (.ret (.bvar 0))) := rfl

end NoIotaTest

end
