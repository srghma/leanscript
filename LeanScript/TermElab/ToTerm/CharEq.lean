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

end LeanScript.Gen

end
