import IntUInt53.TopBoundedUInt64.Fast
import IntUInt53.TopBoundedUInt64.Mul
import IntUInt53.TopBoundedUInt64.Add

/-!
# Widening and carrying arithmetic on `TopBoundedUInt64`

The variants of the previous modules all answer in one value, so a product
that does not fit has to be reported as an overflow.  The operations here
instead return *two* values and lose nothing:

* `mulWide a b = (high, low)` with `high * period + low = a * b`, the exact
  product written in base `period hi`;
* `carryingAdd a b c = (sum, carry)` with `sum + carry * period = a + b + c`,
  the primitive used to chain additions.

Both are exact by construction: the specifications below are equations between
natural numbers with no truncation anywhere.
-/

set_option autoImplicit false

namespace TopBoundedUInt64

variable {hi : UInt64}

/-! ### Widening multiplication -/

/-- The high part of the exact product, i.e. `(a * b) / period hi`. -/
def mulHigh (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi :=
  ofNatLe hi (a.toNat * b.toNat / period hi) (by
    have ha := toNat_le a
    have hb := toNat_le b
    have hp : period hi = hi.toNat + 1 := rfl
    have hmul : a.toNat * b.toNat ≤ hi.toNat * hi.toNat := Nat.mul_le_mul ha hb
    have hsucc : (hi.toNat + 1) * (hi.toNat + 1)
        = hi.toNat * hi.toNat + hi.toNat + hi.toNat + 1 := Nat.succ_mul_succ _ _
    have hlt : a.toNat * b.toNat < period hi * period hi := by rw [hp]; omega
    have := Nat.div_lt_of_lt_mul (m := a.toNat * b.toNat) (n := period hi) (k := period hi) hlt
    omega)

/-- The low part of the exact product, i.e. `(a * b) % period hi`. -/
def mulLow (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi := wrapping_mul a b

/-- Widening multiplication: the exact product in base `period hi`, as the pair
of its high and low parts. -/
def mulWide (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi × TopBoundedUInt64 hi :=
  (mulHigh a b, mulLow a b)

@[simp] theorem toNat_mulHigh (a b : TopBoundedUInt64 hi) :
    (mulHigh a b).toNat = a.toNat * b.toNat / period hi := by
  unfold mulHigh; rw [toNat_ofNatLe]

@[simp] theorem toNat_mulLow (a b : TopBoundedUInt64 hi) :
    (mulLow a b).toNat = a.toNat * b.toNat % period hi := toNat_wrapping_mul a b

/-- **Nothing is lost**: the two halves recover the exact product. -/
theorem mulWide_spec (a b : TopBoundedUInt64 hi) :
    (mulWide a b).1.toNat * period hi + (mulWide a b).2.toNat = a.toNat * b.toNat := by
  show (mulHigh a b).toNat * period hi + (mulLow a b).toNat = a.toNat * b.toNat
  rw [toNat_mulHigh, toNat_mulLow]
  exact Nat.div_add_mod' _ _

/-- The high part vanishes exactly when the product is representable. -/
theorem mulHigh_eq_zero_iff {a b : TopBoundedUInt64 hi} :
    (mulHigh a b).toNat = 0 ↔ a.toNat * b.toNat ≤ hi.toNat := by
  rw [toNat_mulHigh]
  have hp : period hi = hi.toNat + 1 := rfl
  constructor
  · intro h
    have := Nat.lt_of_div_eq_zero (by omega) h
    omega
  · intro h
    exact Nat.div_eq_of_lt (by omega)

/-- When the product fits, the low part is the exact product. -/
theorem toNat_mulLow_of_le {a b : TopBoundedUInt64 hi} (h : a.toNat * b.toNat ≤ hi.toNat) :
    (mulLow a b).toNat = a.toNat * b.toNat := by
  rw [toNat_mulLow]
  exact Nat.mod_eq_of_lt (by have hp : period hi = hi.toNat + 1 := rfl; omega)

/-! ### Carrying addition -/

/-- Carrying addition: `a + b + c` split as a value of the type and a carry bit. -/
def carryingAdd (a b : TopBoundedUInt64 hi) (c : Bool) :
    TopBoundedUInt64 hi × Bool :=
  let s := a.toNat + b.toNat + (if c then 1 else 0)
  (ofNatWrap hi s, decide (hi.toNat < s))

/-- The key fact: on a sum that is less than two periods, wrapping plus a
carry bit recovers the sum exactly. -/
theorem toNat_ofNatWrap_add_carry {s : Nat} (hs : s < 2 * period hi) :
    (ofNatWrap hi s).toNat + (if hi.toNat < s then period hi else 0) = s := by
  have hp : period hi = hi.toNat + 1 := rfl
  rw [toNat_ofNatWrap]
  by_cases hlt : hi.toNat < s
  · have hmod : s % period hi = s - period hi := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [ite_eq_left hlt, hmod]
    omega
  · rw [ite_eq_right hlt, Nat.mod_eq_of_lt (by omega), Nat.add_zero]

/-- **Nothing is lost**: the value and the carry recover the exact sum. -/
theorem carryingAdd_spec (a b : TopBoundedUInt64 hi) (c : Bool) :
    (carryingAdd a b c).1.toNat
        + (if (carryingAdd a b c).2 then period hi else 0)
      = a.toNat + b.toNat + (if c then 1 else 0) := by
  have ha := toNat_le a
  have hb := toNat_le b
  have hp : period hi = hi.toNat + 1 := rfl
  have hs : a.toNat + b.toNat + (if c then 1 else 0) < 2 * period hi := by
    cases c <;> simp <;> omega
  have key := toNat_ofNatWrap_add_carry (hi := hi) hs
  unfold carryingAdd
  simpa using key

/-- The carry is set exactly when the exact sum leaves the range. -/
theorem carryingAdd_snd_iff {a b : TopBoundedUInt64 hi} {c : Bool} :
    (carryingAdd a b c).2 = true ↔ hi.toNat < a.toNat + b.toNat + (if c then 1 else 0) := by
  unfold carryingAdd; simp

/-- Without a carry in, carrying addition is the overflowing addition. -/
theorem carryingAdd_false (a b : TopBoundedUInt64 hi) :
    carryingAdd a b false = overflowing_add a b := by
  unfold carryingAdd overflowing_add wrapping_add exactAdd
  simp

end TopBoundedUInt64
