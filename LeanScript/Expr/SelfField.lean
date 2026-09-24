module
public import LeanScript.Ty.TyWfIn
public import LeanScript.Ty.Wf

@[expose] public section

set_option autoImplicit false

/-!
# Pointers at the fields a deeper look descends into

`SelfField`, `FamilyMemberField` and `FamilyMemberAt`: the indices the depth-`k` folds of
`LeanScript.Term` (in `LeanScript.Expr.Term`) use to name a subvalue, or a member of a
family, to look further down into.
-/

namespace LeanScript

/-- A pointer at a field of a constructor that **is** an occurrence of the type being
    folded over: the field a deeper look descends into.

    A constructor's payload is a list of trees written in the scope the binder opens, and
    a field that is literally `Ty.self` is a value of the type again.  `here` names such
    a field — carrying the proof that it is one, which is `rfl` — and `there` steps past
    a field to the ones after it, so `.here rfl`, `.there (.here rfl)`, … name the
    payload's occurrences in declaration order.

    It is what says that a depth-`k` fold (`LeanScript.Term.recTaggedUnion_rec`) looks
    further down only into a **subvalue**, never into a value it was handed. -/
inductive SelfField : List (TyWfIn 1) → Type
  /-- The first field is an occurrence of the type. -/
  | here : ∀ {a : TyWfIn 1} {fs : List (TyWfIn 1)}, a.toTy = Ty.self → SelfField (a :: fs)
  /-- An occurrence among the fields after the first. -/
  | there : ∀ {a : TyWfIn 1} {fs : List (TyWfIn 1)}, SelfField fs → SelfField (a :: fs)
  deriving DecidableEq, Repr

/-- A pointer at a field of a constructor of a **member of a mutual family** that **is**
    an occurrence of member `i` of that family: the field a deeper look descends into.

    It is `LeanScript.SelfField` in the scope of a family: a member's payload is a list
    of trees written in the scope of the whole family, and a field that is literally
    `Ty.familyMember i` is a value of member `i` again.  `here` names such a field —
    carrying the proof that it is one, which is `rfl` — and `there` steps past a field to
    the ones after it, so `.here rfl`, `.there (.here rfl)`, … name the payload's
    occurrences of member `i` in declaration order.

    It is what says that a depth-`k` fold of a mutual family
    (`LeanScript.Term.mutualRecursiveFamily_rec`) looks further down only into a
    **subvalue**, never into a value it was handed. -/
inductive FamilyMemberField {n : Nat} : Nat → List (TyWfIn (n + 2)) → Type
  /-- The first field is an occurrence of member `i`. -/
  | here : ∀ {i : Nat} {a : TyWfIn (n + 2)} {fs : List (TyWfIn (n + 2))},
      a.toTy = Ty.familyMember i → FamilyMemberField i (a :: fs)
  /-- An occurrence of member `i` among the fields after the first. -/
  | there : ∀ {i : Nat} {a : TyWfIn (n + 2)} {fs : List (TyWfIn (n + 2))},
      FamilyMemberField i fs → FamilyMemberField i (a :: fs)
  deriving DecidableEq, Repr

/-- **Which member of a family a member number is**: the proof that member `i` of the
    family `ms` is the member `m`, as a position in the list of members rather than as a
    number with a bound.

    A deeper look (`LeanScript.FamilyFoldKBranch.deep`) descends into a field that is an
    occurrence of member `i` and then dispatches on that member's *shape*, so it needs the
    shape and not only the number: `.here`, `.there .here`, … name the members in
    declaration order, and a number the family does not have is unwritable. -/
inductive FamilyMemberAt {n : Nat} :
    List (LeanFamMemberSchema (TyWfIn (n + 2))) → Nat →
    LeanFamMemberSchema (TyWfIn (n + 2)) → Type
  /-- The first member of the list is member `0`. -/
  | here : ∀ {m : LeanFamMemberSchema (TyWfIn (n + 2))}
      {ms : List (LeanFamMemberSchema (TyWfIn (n + 2)))}, FamilyMemberAt (m :: ms) 0 m
  /-- Member `i` of the members after the first is member `i + 1`. -/
  | there : ∀ {i : Nat} {m' m : LeanFamMemberSchema (TyWfIn (n + 2))}
      {ms : List (LeanFamMemberSchema (TyWfIn (n + 2)))},
      FamilyMemberAt ms i m → FamilyMemberAt (m' :: ms) (i + 1) m
  deriving DecidableEq, Repr

end LeanScript

end
