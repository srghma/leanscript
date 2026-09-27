/-
Refining the *type* instead of carrying a `Prop`.

`ExamplesValidData.ForestPair` states its precondition as a `Prop` (`Valid1`), which the
compiler erases, so nothing about it survives into the compiled world.  Part of such a
precondition is, however, a statement about the *shape* of the data — "the list has even
length", "every node's flag is `2`" — and a shape can be made a type.

`MForest` below is the type of marked forests of even length: it stores nodes two at a
time and has no room for a flag, so a value of it cannot fail either condition.  The
erasure `MForest.erase : MForest → Forest` lands in the forests that satisfy exactly
those two conjuncts, and that is proved here rather than assumed.

The trade-off: a function written
against `MForest` needs no precondition at all, so its translation rejects bad input at
the type level — but its argument is a *different runtime type*, so callers holding an
ordinary `Forest` must convert, and the conversion is the run-time check again.
-/

import ExamplesValidData.ForestPair

namespace ExamplesValidData

mutual

/-- A node without a flag field: the flag is fixed to `2`, so it carries no information. -/
inductive MNode where
  | node (label : Nat) (kids : MForest) : MNode
  deriving Repr

/-- A forest of marked nodes, stored two at a time: its length is even by construction. -/
inductive MForest where
  | nil : MForest
  | cons2 (a b : MNode) (rest : MForest) : MForest
  deriving Repr

end

mutual

/-- Forget the refinement, filling in the flag that the type made implicit. -/
def MNode.erase : MNode → Node
  | .node l ks => .node l 2 ks.erase

/-- Forget the refinement. -/
def MForest.erase : MForest → Forest
  | .nil => .nil
  | .cons2 a b r => .cons a.erase (.cons b.erase r.erase)

end

/-- Even length, by construction. -/
theorem MForest.len_erase_even : ∀ xs : MForest, (MForest.erase xs).len % 2 = 0
  | .nil => by simp [MForest.erase, Forest.len]
  | .cons2 a b r => by
      have ih := MForest.len_erase_even r
      simp [MForest.erase, Forest.len]
      omega

/-- Every node marked, by construction. -/
theorem MForest.marked_erase : ∀ xs : MForest, (MForest.erase xs).marked
  | .nil => by simp [MForest.erase, Forest.marked]
  | .cons2 a b r => by
      have ih := MForest.marked_erase r
      cases a with
      | node _ _ =>
        cases b with
        | node _ _ => exact ⟨rfl, rfl, ih⟩

/-- So the data half of `Valid1` — the part that is a statement about the shape of the
    argument — needs no proof argument when the argument has the refined type. -/
theorem MForest.valid1_of_len {xs : MForest} (h : (MForest.erase xs).len ≥ 1)
    (h3 : (MForest.erase xs).len % 3 = 0 ∨ (MForest.erase xs).len % 3 = 1) :
    Valid1 (MForest.erase xs) :=
  ⟨h, h3, MForest.marked_erase xs⟩

end ExamplesValidData
