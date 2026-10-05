module

@[expose] public section

set_option autoImplicit false

/-!
# Equality of characters, as the translator reads it

`Char` is a leaf of the language: its values are literals, and the instance
`instDecidableEqChar` (which decides `a = b` by `decEq a.val b.val`, a projection of the leaf)
has no translation.  `#leanscript_to_term` (`trDecide`, `LeanScript/TermElab/ToTerm/Expr/Calls.lean`)
translates `decide (a = b)` on `Char` as `decide ("".push a = "".push b)` instead: the
comparison of two one-character strings, with the externs `String.push` and `String.decEq`
(in JavaScript, where a `Char` is a one-character string, `"".push c` is `c` itself and the
comparison is `a === b`).  This file proves the two decisions equal.
-/

namespace LeanScript.Gen

/-- Two one-character strings are equal exactly when their characters are. -/
theorem char_push_eq_iff (a b : Char) : ("".push a = "".push b) ↔ a = b := by
  constructor
  · intro h
    simpa using congrArg String.toList h
  · intro h
    rw [h]

/-- The translation of `a = b` on `Char` decides the same as the original. -/
theorem decide_char_eq_push (a b : Char) :
    decide (a = b) = decide ("".push a = "".push b) := by
  simp

/-- The same, for `==` (the `BEq` of `DecidableEq Char`). -/
theorem char_beq_eq_push (a b : Char) :
    (a == b) = decide ("".push a = "".push b) := by
  rw [← decide_char_eq_push]
  rfl

/-! ## Order

`a < b` on `Char` is decided by `Char.instDecidableLt` (`a.val.decLt b.val`) and `a ≤ b` by
`Char.instDecidableLe`, projections of the leaf again.  `trDecide` translates `decide (a < b)`
as `decide ("".push a < "".push b)` (the extern `String.decidableLT`, `<` in JavaScript) and
`decide (a ≤ b)` as `!decide ("".push b < "".push a)` (the way `String.decLE` decides `≤`). -/

/-- One one-character string is below another exactly when its character is. -/
theorem char_push_lt_iff (a b : Char) : ("".push a < "".push b) ↔ a < b := by
  show ("".push a).toList < ("".push b).toList ↔ a < b
  simp only [String.toList_push, String.toList_empty, List.nil_append]
  constructor
  · intro h
    cases h with
    | rel h => exact h
    | cons h => exact absurd h (by simp)
  · intro h
    exact List.Lex.rel h

/-- `Char` is totally ordered: `a ≤ b` exactly when not `b < a`. -/
theorem char_le_iff_not_lt (a b : Char) : a ≤ b ↔ ¬ b < a := by
  show a.val.toNat ≤ b.val.toNat ↔ ¬ b.val.toNat < a.val.toNat
  omega

/-- The translation of `a < b` on `Char` decides the same as the original. -/
theorem decide_char_lt_push (a b : Char) :
    decide (a < b) = decide ("".push a < "".push b) :=
  decide_eq_decide.mpr (char_push_lt_iff a b).symm

/-- The translation of `a ≤ b` on `Char` decides the same as the original. -/
theorem decide_char_le_push (a b : Char) :
    decide (a ≤ b) = !decide ("".push b < "".push a) := by
  rw [← decide_not]
  exact decide_eq_decide.mpr
    ((char_le_iff_not_lt a b).trans (not_congr (char_push_lt_iff b a).symm))

end LeanScript.Gen

end
