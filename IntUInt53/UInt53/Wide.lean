import IntUInt53.UInt53.Mul
import IntUInt53.TopBoundedUInt64.Wide

/-!
# Widening and carrying arithmetic on `UInt53`

The widening operations of `TopBoundedUInt64`, specialised to `UInt53`.

`mulWide a b` returns the exact product of two `UInt53` values as a pair
`(high, low)` of `UInt53` values with `high * 2 ^ 53 + low = a * b`.  Since the
product of two numbers below `2 ^ 53` is below `2 ^ 106`, this is exactly the
53-bit two-limb representation of the product: no information is lost, and no
overflow needs to be reported.

`carryingAdd a b c` is the corresponding primitive for addition.
-/

set_option autoImplicit false

open TopBoundedUInt64

namespace UInt53

@[simp] theorem toNat_mulHigh' (a b : UInt53) :
    (mulHigh a b).toNat = a.toNat * b.toNat / SIZE := by
  rw [TopBoundedUInt64.toNat_mulHigh, period_eq]

@[simp] theorem toNat_mulLow' (a b : UInt53) :
    (mulLow a b).toNat = a.toNat * b.toNat % SIZE := by
  rw [TopBoundedUInt64.toNat_mulLow, period_eq]

/-- **Exactness of the widening product**: the two 53-bit limbs recover the
exact product of two `UInt53` values. -/
theorem mulWide_exact (a b : UInt53) :
    (mulWide a b).1.toNat * SIZE + (mulWide a b).2.toNat = a.toNat * b.toNat := by
  have h := TopBoundedUInt64.mulWide_spec a b
  rwa [period_eq] at h

/-- The high limb is zero exactly when the product is representable in one `UInt53`. -/
theorem mulHigh_eq_zero_iff' {a b : UInt53} :
    (mulHigh a b).toNat = 0 ↔ a.toNat * b.toNat ≤ MAX :=
  TopBoundedUInt64.mulHigh_eq_zero_iff

/-- **Exactness of carrying addition**: the value and the carry recover the
exact sum `a + b + c`. -/
theorem carryingAdd_exact (a b : UInt53) (c : Bool) :
    (carryingAdd a b c).1.toNat + (if (carryingAdd a b c).2 then SIZE else 0)
      = a.toNat + b.toNat + (if c then 1 else 0) := by
  have h := TopBoundedUInt64.carryingAdd_spec a b c
  rwa [period_eq] at h

/-! ### Exact arithmetic, concretely -/

/-- The product `MAX * MAX` is not representable in a single `UInt53`, yet the
widening product returns it exactly:
`9007199254740990 * 2 ^ 53 + 1 = 9007199254740991 ^ 2`. -/
theorem mulWide_max_max :
    (mulWide maxVal maxVal).1.toNat = 9007199254740990 ∧
      (mulWide maxVal maxVal).2.toNat = 1 := by
  constructor <;> decide

/-- `3 * 4 = 12` has no high limb. -/
theorem mulWide_three_four :
    mulWide (ofNat 3) (ofNat 4) = (ofNat 0, ofNat 12) := by decide

/-- Adding `MAX + MAX + 1` carries: the sum is `SIZE + MAX`, so the value is
`MAX` and the carry is set. -/
theorem carryingAdd_max_max :
    carryingAdd maxVal maxVal true = (maxVal, true) := by decide

end UInt53
