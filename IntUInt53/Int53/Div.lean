import IntUInt53.Int53.Mul

/-!
# Division and remainder on `Int53`

The division operations of `BoundedInt64`, specialised to `Int53`.

Division truncates towards zero, so `(-7) / 2 = -3` and `(-7) % 2 = -1`.

Because the range of `Int53` is symmetric — `MIN = -MAX` — neither the
quotient nor the remainder can ever leave it: both are bounded in absolute
value by the dividend.  The only failure is therefore a zero divisor, and this
is proved below (`Int53.divFails_iff`, `Int53.modFails_iff`).
-/

set_option autoImplicit false

open BoundedInt64

namespace Int53

/-! ### Division on `Int53` fails only on a zero divisor -/

theorem lo_toInt_eq_neg_hi_toInt :
    (-(2 ^ 53 - 1) : Int64).toInt = -((2 ^ 53 - 1 : Int64).toInt) := by decide

/-- On `Int53` division fails exactly on a zero divisor. -/
theorem divFails_iff {a b : Int53} : divFails a b ↔ b.toInt = 0 :=
  BoundedInt64.divFails_iff_of_symm lo_toInt_eq_neg_hi_toInt a b

/-- On `Int53` the remainder fails exactly on a zero divisor. -/
theorem modFails_iff {a b : Int53} : modFails a b ↔ b.toInt = 0 :=
  BoundedInt64.modFails_iff_of_symm lo_toInt_eq_neg_hi_toInt a b

/-- The quotient of two `Int53` values is always representable. -/
theorem inRange_exactDiv {a b : Int53} (h : b.toInt ≠ 0) :
    BoundedInt64.InRange (-(2 ^ 53 - 1)) (2 ^ 53 - 1) (exactDiv a b) :=
  Decidable.of_not_not (fun hc => h (divFails_iff.mp (Or.inr hc)))

/-- The remainder of two `Int53` values is always representable. -/
theorem inRange_exactMod {a b : Int53} (h : b.toInt ≠ 0) :
    BoundedInt64.InRange (-(2 ^ 53 - 1)) (2 ^ 53 - 1) (exactMod a b) :=
  Decidable.of_not_not (fun hc => h (modFails_iff.mp (Or.inr hc)))

/-! ### The checked variants -/

theorem checked_div_eq_none_iff {a b : Int53} : checked_div a b = none ↔ b.toInt = 0 := by
  rw [BoundedInt64.checked_div_eq_none_iff, divFails_iff]

theorem checked_mod_eq_none_iff {a b : Int53} : checked_mod a b = none ↔ b.toInt = 0 := by
  rw [BoundedInt64.checked_mod_eq_none_iff, modFails_iff]

/-- Exactness: whenever checked division succeeds, it returns the exact quotient. -/
theorem toInt_of_checked_div {a b c : Int53} (h : checked_div a b = some c) :
    c.toInt = a.toInt.tdiv b.toInt := BoundedInt64.toInt_of_checked_div h

/-- Exactness: whenever the checked remainder succeeds, it is exact. -/
theorem toInt_of_checked_mod {a b c : Int53} (h : checked_mod a b = some c) :
    c.toInt = a.toInt.tmod b.toInt := BoundedInt64.toInt_of_checked_mod h

/-- Checked division succeeds, with the exact quotient, on every nonzero divisor. -/
theorem checked_div_exact {a b : Int53} (h : b.toInt ≠ 0) :
    ∃ c, checked_div a b = some c ∧ c.toInt = a.toInt.tdiv b.toInt :=
  BoundedInt64.checked_div_of_not_fails (fun hc => h (divFails_iff.mp hc))

/-- The checked remainder succeeds, exactly, on every nonzero divisor. -/
theorem checked_mod_exact {a b : Int53} (h : b.toInt ≠ 0) :
    ∃ c, checked_mod a b = some c ∧ c.toInt = a.toInt.tmod b.toInt :=
  BoundedInt64.checked_mod_of_not_fails (fun hc => h (modFails_iff.mp hc))

/-! ### All four variants -/

/-- On a nonzero divisor all four variants of division on `Int53` return the
exact quotient, and the flag is `false`. -/
theorem div_variants_exact {a b : Int53} (h : b.toInt ≠ 0) :
    (∃ c, checked_div a b = some c ∧ c.toInt = a.toInt.tdiv b.toInt) ∧
      (wrapping_div a b).toInt = a.toInt.tdiv b.toInt ∧
      (overflowing_div a b).1.toInt = a.toInt.tdiv b.toInt ∧
      (overflowing_div a b).2 = false ∧
      (saturating_div a b).toInt = a.toInt.tdiv b.toInt :=
  BoundedInt64.div_variants_agree (fun hc => h (divFails_iff.mp hc))

/-- On a nonzero divisor all four variants of the remainder on `Int53` return
the exact remainder, and the flag is `false`. -/
theorem mod_variants_exact {a b : Int53} (h : b.toInt ≠ 0) :
    (∃ c, checked_mod a b = some c ∧ c.toInt = a.toInt.tmod b.toInt) ∧
      (wrapping_mod a b).toInt = a.toInt.tmod b.toInt ∧
      (overflowing_mod a b).1.toInt = a.toInt.tmod b.toInt ∧
      (overflowing_mod a b).2 = false ∧
      (saturating_mod a b).toInt = a.toInt.tmod b.toInt :=
  BoundedInt64.mod_variants_agree (fun hc => h (modFails_iff.mp hc))

/-- The defining property of division with remainder on `Int53`. -/
theorem mul_div_add_mod (a b : Int53) :
    b.toInt * exactDiv a b + exactMod a b = a.toInt :=
  BoundedInt64.mul_exactDiv_add_exactMod a b

/-! ### Exact arithmetic, concretely -/

/-- `12 / 4 = 3`, exactly. -/
theorem twelve_div_four : checked_div (ofInt 12) (ofInt 4) = some (ofInt 3) := by decide

/-- Division truncates towards zero: `(-7) / 2 = -3`. -/
theorem neg_seven_div_two :
    checked_div (ofInt (-7)) (ofInt 2) = some (ofInt (-3)) := by decide

/-- The remainder takes the sign of the dividend: `(-7) % 2 = -1`. -/
theorem neg_seven_mod_two :
    checked_mod (ofInt (-7)) (ofInt 2) = some (ofInt (-1)) := by decide

/-- Division by zero is reported, not silently answered. -/
theorem checked_div_zero : checked_div (ofInt 12) zero = none := by decide

/-- The remainder by zero is reported as well. -/
theorem checked_mod_zero : checked_mod (ofInt 12) zero = none := by decide

/-- Negating by division is exact at the bottom of the range: `MIN / (-1) = MAX`. -/
theorem min_div_neg_one : checked_div minVal (ofInt (-1)) = some maxVal := by decide

end Int53
