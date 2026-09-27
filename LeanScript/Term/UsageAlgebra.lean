module

public import LeanScript.Term.Usage
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Order.Defs.LinearOrder

@[expose] public section

set_option autoImplicit false

/-!
# The algebra of usages, from Mathlib

`Usage01ω.add` makes `Usage01ω` a commutative monoid with unit `zero`, and `Usage01ω.max` is
the maximum of the linear order `zero ≤ one ≤ many`.  With these instances Mathlib's lemmas
about commutative monoids and linear orders (`add_comm`, `add_assoc`, `max_comm`, `max_assoc`,
`max_self`, …) hold for usages, instead of being proved again by hand; the computation is
still the pattern matching of `add` and `max`.

This module is kept out of the imports of the rest of the project: importing Mathlib there
would change how every test prints (`ℕ` for `Nat`, …) and switch on Mathlib's linters.
-/

namespace LeanScript

namespace Usage01ω

instance : Zero Usage01ω := ⟨.zero⟩

instance : AddCommMonoid Usage01ω where
  add_assoc u v w := by cases u <;> cases v <;> cases w <;> rfl
  zero_add u := by cases u <;> rfl
  add_zero u := by cases u <;> rfl
  add_comm u v := by cases u <;> cases v <;> rfl
  nsmul := nsmulRec

/-- The rank of a usage in `zero ≤ one ≤ many`. -/
def rank : Usage01ω → Nat
  | .zero => 0
  | .one => 1
  | .many => 2

instance : LinearOrder Usage01ω where
  le u v := u.rank ≤ v.rank
  lt u v := u.rank < v.rank
  le_refl _ := Nat.le_refl _
  le_trans _ _ _ := Nat.le_trans
  le_antisymm u v h₁ h₂ := by
    cases u <;> cases v <;> first | rfl | exact absurd (Nat.le_antisymm h₁ h₂) (by decide)
  lt_iff_le_not_ge _ _ := Nat.lt_iff_le_and_not_ge
  le_total _ _ := Nat.le_total _ _
  toDecidableLE u v := inferInstanceAs (Decidable (u.rank ≤ v.rank))
  toDecidableEq := inferInstance
  max := Usage01ω.max
  max_def u v := by cases u <;> cases v <;> rfl
  compare_eq_compareOfLessAndEq u v := by cases u <;> cases v <;> rfl

/-- `+` and `max` of the instances are `Usage01ω.add` and `Usage01ω.max`. -/
example (u v : Usage01ω) : u + v = u.add v := rfl
example (u v : Usage01ω) : Max.max u v = Usage01ω.max u v := rfl

/-- The laws, from Mathlib. -/
theorem add_comm (u v : Usage01ω) : u + v = v + u := _root_.add_comm u v
theorem add_assoc (u v w : Usage01ω) : u + v + w = u + (v + w) := _root_.add_assoc u v w
theorem max_comm (u v : Usage01ω) : Usage01ω.max u v = Usage01ω.max v u := _root_.max_comm u v
theorem max_assoc (u v w : Usage01ω) :
    Usage01ω.max (Usage01ω.max u v) w = Usage01ω.max u (Usage01ω.max v w) :=
  _root_.max_assoc u v w
theorem max_self (u : Usage01ω) : Usage01ω.max u u = u := _root_.max_self u

end Usage01ω

end LeanScript

end
