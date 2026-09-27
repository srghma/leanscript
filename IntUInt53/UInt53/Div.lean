import IntUInt53.UInt53.Mul

/-!
# Division and remainder on `UInt53`

The division operations of `TopBoundedUInt64`, specialised to `UInt53`.

On `UInt53` division can never overflow: `a / b ≤ a ≤ MAX` and `a % b ≤ a ≤ MAX`.
The only failure is a zero divisor, which the checked variant reports with
`none` and the overflowing variant with the flag `true`.
-/

set_option autoImplicit false

open TopBoundedUInt64

namespace UInt53

/-! ### Exactness of the total operations -/

@[simp] theorem toNat_div' (a b : UInt53) : (div a b).toNat = a.toNat / b.toNat :=
  TopBoundedUInt64.toNat_div a b

@[simp] theorem toNat_mod' (a b : UInt53) : (mod a b).toNat = a.toNat % b.toNat :=
  TopBoundedUInt64.toNat_mod a b

/-- The defining property of division with remainder on `UInt53`. -/
theorem div_add_mod (a b : UInt53) :
    b.toNat * (div a b).toNat + (mod a b).toNat = a.toNat :=
  TopBoundedUInt64.div_add_mod a b

/-- The remainder is smaller than a nonzero divisor. -/
theorem toNat_mod_lt {a b : UInt53} (h : b.toNat ≠ 0) : (mod a b).toNat < b.toNat :=
  TopBoundedUInt64.toNat_mod_lt h

/-! ### The checked variants -/

theorem checked_div_eq_none_iff {a b : UInt53} : checked_div a b = none ↔ b.toNat = 0 :=
  TopBoundedUInt64.checked_div_eq_none_iff

theorem checked_mod_eq_none_iff {a b : UInt53} : checked_mod a b = none ↔ b.toNat = 0 :=
  TopBoundedUInt64.checked_mod_eq_none_iff

/-- Exactness: whenever checked division succeeds, it returns the exact quotient. -/
theorem toNat_of_checked_div {a b c : UInt53} (h : checked_div a b = some c) :
    c.toNat = a.toNat / b.toNat := TopBoundedUInt64.toNat_of_checked_div h

/-- Exactness: whenever the checked remainder succeeds, it is exact. -/
theorem toNat_of_checked_mod {a b c : UInt53} (h : checked_mod a b = some c) :
    c.toNat = a.toNat % b.toNat := TopBoundedUInt64.toNat_of_checked_mod h

/-- Checked division succeeds, with the exact quotient, on every nonzero divisor. -/
theorem checked_div_exact {a b : UInt53} (h : b.toNat ≠ 0) :
    ∃ c, checked_div a b = some c ∧ c.toNat = a.toNat / b.toNat :=
  ⟨div a b, TopBoundedUInt64.checked_div_of_ne_zero h, TopBoundedUInt64.toNat_div a b⟩

/-- The checked remainder succeeds, exactly, on every nonzero divisor. -/
theorem checked_mod_exact {a b : UInt53} (h : b.toNat ≠ 0) :
    ∃ c, checked_mod a b = some c ∧ c.toNat = a.toNat % b.toNat :=
  ⟨mod a b, TopBoundedUInt64.checked_mod_of_ne_zero h, TopBoundedUInt64.toNat_mod a b⟩

/-! ### All four variants -/

/-- On a nonzero divisor all four variants of division on `UInt53` return the
exact quotient, and the overflow flag is `false`. -/
theorem div_variants_exact {a b : UInt53} (h : b.toNat ≠ 0) :
    (∃ c, checked_div a b = some c ∧ c.toNat = a.toNat / b.toNat) ∧
      (wrapping_div a b).toNat = a.toNat / b.toNat ∧
      (overflowing_div a b).1.toNat = a.toNat / b.toNat ∧
      (overflowing_div a b).2 = false ∧
      (saturating_div a b).toNat = a.toNat / b.toNat :=
  TopBoundedUInt64.div_variants_agree h

/-- On a nonzero divisor all four variants of the remainder on `UInt53` return
the exact remainder, and the overflow flag is `false`. -/
theorem mod_variants_exact {a b : UInt53} (h : b.toNat ≠ 0) :
    (∃ c, checked_mod a b = some c ∧ c.toNat = a.toNat % b.toNat) ∧
      (wrapping_mod a b).toNat = a.toNat % b.toNat ∧
      (overflowing_mod a b).1.toNat = a.toNat % b.toNat ∧
      (overflowing_mod a b).2 = false ∧
      (saturating_mod a b).toNat = a.toNat % b.toNat :=
  TopBoundedUInt64.mod_variants_agree h

/-! ### Exact arithmetic, concretely -/

/-- `12 / 4 = 3`, exactly. -/
theorem twelve_div_four : checked_div (ofNat 12) (ofNat 4) = some (ofNat 3) := by decide

/-- `13 % 4 = 1`, exactly. -/
theorem thirteen_mod_four : checked_mod (ofNat 13) (ofNat 4) = some (ofNat 1) := by decide

/-- Division by zero is reported, not silently answered. -/
theorem checked_div_zero : checked_div (ofNat 12) (ofNat 0) = none := by decide

/-- The remainder by zero is reported as well. -/
theorem checked_mod_zero : checked_mod (ofNat 12) (ofNat 0) = none := by decide

/-- Dividing the largest value by one is exact. -/
theorem checked_div_max_one : checked_div maxVal (ofNat 1) = some maxVal := by decide

end UInt53
