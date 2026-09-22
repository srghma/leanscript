module

public import LeanScript.Den

@[expose] public section

set_option autoImplicit false
set_option linter.defProp false
set_option warn.classDefReducibility false

/-!
# The orders a recursion descends in

`Term.fixAcc` takes an arbitrary order and a proof that the subject of every argument
tuple is accessible for it.  Almost every recursion a front end transcribes descends in
`<` on `Nat` — a structural recursion is exactly that, at the structural measure of the
argument it recurses on — so the accessibility proof for that one order is given here,
written so that it **reduces**: it is a `def`, built out of `Acc.intro` by recursion on a
`Nat`, rather than a `theorem` produced by `WellFounded.apply`.

## Passing the proof so that the term still computes

Lean hoists a closed proof that appears inside the body of a definition into an auxiliary
`theorem`, and the elaborator does not unfold a `theorem`.  A term whose `hacc` field was
written inline is therefore still a perfectly good term — the evaluator runs it, and the
kernel reduces it — but `by rfl` and `by decide` will not see through it.

So bind the proof to a **top-level `def` of its own** and pass that constant:

```
def haccArg0 : ∀ as : Env (Ty.prim .nat :: ps), Acc NatLt (subject as) := fun as => accNatLt _
def myFn : Term Sg [] [] _ := .fixAcc ... haccArg0 ...
```

`accNatLtArg0` below is that constant for the commonest case: the recursion descends in
`<` on its **first** argument, which is a `Nat`.
-/

namespace LeanScript

/-- The order a structural recursion descends in: `<` on `Nat`. -/
abbrev NatLt : Nat → Nat → Prop := fun a b => a < b

/-- `<` on `Nat` is decidable, which is what lets `Term.fixAcc` re-enter a recursion
    exactly at the calls that descend. -/
def NatLt.dec : DecidableRel NatLt := fun a b => Nat.decLt a b

/-- Everything below `n` is accessible for `<`. -/
def accNatLtAux : (n : Nat) → (m : Nat) → m < n → Acc NatLt m
  | 0, m, h => absurd h (Nat.not_lt_zero m)
  | n + 1, m, h => Acc.intro m fun y hy => accNatLtAux n y (by omega)

/-- Every natural number is accessible for `<`.  This is a `def`, and it reduces. -/
def accNatLt (n : Nat) : Acc NatLt n := Acc.intro n fun y hy => accNatLtAux n y hy

/-- The accessibility field of a recursion that descends in `<` on its **first**
    argument, which is a `Nat`.  Pass this constant itself — see the note above. -/
def accNatLtArg0 {ps : List Ty} :
    ∀ as : Env (Ty.prim .nat :: ps), Acc NatLt (Prod.fst as) :=
  fun as => accNatLt as.1

/-- The subject of a recursion that descends in `<` on its first argument. -/
def subjectArg0 {ps : List Ty} : Env (Ty.prim .nat :: ps) → Nat := fun as => as.1

/-! ## The lexicographic order on a pair of `Nat`s

A recursion that descends at two numbers at once — Ackermann's function, the diagonal
enumeration, the hyperoperation tower — has no `Nat` measure, so `Term.fixAcc` is handed
the lexicographic order on `Nat × Nat` instead.  Everything below is written so that it
**reduces**: the order is the truth of a `Bool`-valued function, so deciding it is
computing with numbers rather than taking a proof apart, and the accessibility proof is
a structural recursion on a bound, exactly as `accNatLtAux` is. -/

/-- The lexicographic order on a pair of numbers, as a `Bool`. -/
def natLexB (p q : Nat × Nat) : Bool :=
  Nat.blt p.1 q.1 || (Nat.beq p.1 q.1 && Nat.blt p.2 q.2)

/-- The lexicographic order on `Nat × Nat`: the first components descend, or they are
    equal and the second ones do. -/
abbrev NatLex : Nat × Nat → Nat × Nat → Prop := fun p q => natLexB p q = true

/-- The lexicographic order is decidable, by computing with numbers. -/
def NatLex.dec : DecidableRel NatLex := fun p q => Bool.decEq (natLexB p q) true

theorem natLexB_iff {p q : Nat × Nat} :
    natLexB p q = true ↔ (p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)) := by
  simp [natLexB, Nat.blt_eq, Nat.beq_eq]

/-- Every pair whose second component is below `n` and whose first component is `a` is
    accessible, given that every pair with a smaller first component is.  The pair is a
    parameter rather than a pair of numbers, so that the answer is about the pair the
    recursion was handed and no cast stands in the way of reduction. -/
def accLexInner (a : Nat) (ih : ∀ q : Nat × Nat, q.1 < a → Acc NatLex q) :
    (n : Nat) → (p : Nat × Nat) → p.1 = a → p.2 < n → Acc NatLex p
  | 0, p, _, h => absurd h (Nat.not_lt_zero p.2)
  | n + 1, p, hp, hn => Acc.intro p fun r hr =>
      if h1 : r.1 < a then ih r h1
      else
        accLexInner a ih n r
          (by have := natLexB_iff.mp hr; omega)
          (by have := natLexB_iff.mp hr; omega)

/-- Every pair whose first component is below `n` is accessible. -/
def accLexOuter : (n : Nat) → (p : Nat × Nat) → p.1 < n → Acc NatLex p
  | 0, p, h => absurd h (Nat.not_lt_zero p.1)
  | n + 1, p, hp =>
      accLexInner p.1 (fun q hq => accLexOuter n q (by omega)) (p.2 + 1) p rfl
        (Nat.lt_succ_self p.2)

/-- Every pair of numbers is accessible for the lexicographic order.  This is a `def`,
    and it reduces. -/
def accNatLex (p : Nat × Nat) : Acc NatLex p :=
  accLexOuter (p.1 + 1) p (Nat.lt_succ_self p.1)

end LeanScript

end
