import IntUInt53.TopBoundedUInt64.Fast
import IntUInt53.TopBoundedUInt64.Mul
import IntUInt53.TopBoundedUInt64.Add
import IntUInt53.TopBoundedUInt64.Sub

/-!
# The wrapping operations are modular arithmetic

This module makes the informal statement "wrapping arithmetic is arithmetic
modulo `period hi`" precise, by showing that the reduction map

```
ofNatWrap hi : Nat → TopBoundedUInt64 hi
```

is a surjection that turns `+` and `*` on `Nat` into `wrapping_add` and
`wrapping_mul`, that identifies two natural numbers exactly when they are
congruent modulo the period, and that is inverted by `toNat` on the
representatives.  In other words `TopBoundedUInt64 hi` with its wrapping
operations *is* `Nat` modulo `period hi`, with `{0, …, hi}` as the canonical
representatives.
-/

set_option autoImplicit false

namespace TopBoundedUInt64

variable {hi : UInt64}

/-! ### The reduction map -/

/-- Reduction is a left inverse of the inclusion of representatives. -/
@[simp] theorem ofNatWrap_toNat (a : TopBoundedUInt64 hi) : ofNatWrap hi a.toNat = a :=
  ext (by rw [toNat_ofNatWrap, Nat.mod_eq_of_lt (toNat_lt_period a)])

/-- Reduction is surjective. -/
theorem ofNatWrap_surjective (a : TopBoundedUInt64 hi) : ∃ n, ofNatWrap hi n = a :=
  ⟨a.toNat, ofNatWrap_toNat a⟩

/-- Reduction identifies exactly the numbers congruent modulo the period. -/
theorem ofNatWrap_eq_ofNatWrap_iff {m n : Nat} :
    ofNatWrap hi m = ofNatWrap hi n ↔ m % period hi = n % period hi := by
  rw [ext_iff, toNat_ofNatWrap, toNat_ofNatWrap]

/-- Reduction is invariant under adding a multiple of the period. -/
@[simp] theorem ofNatWrap_add_mul_period (n k : Nat) :
    ofNatWrap hi (n + k * period hi) = ofNatWrap hi n :=
  ext (by rw [toNat_ofNatWrap, toNat_ofNatWrap, Nat.add_mul_mod_self_right])

/-! ### Reduction is a homomorphism -/

/-- Reduction turns addition of natural numbers into wrapping addition. -/
theorem ofNatWrap_add (m n : Nat) :
    ofNatWrap hi (m + n) = wrapping_add (ofNatWrap hi m) (ofNatWrap hi n) :=
  ext (by
    rw [toNat_wrapping_add, toNat_ofNatWrap, toNat_ofNatWrap, toNat_ofNatWrap,
      Nat.add_mod_mod, Nat.mod_add_mod])

/-- Reduction turns multiplication of natural numbers into wrapping multiplication. -/
theorem ofNatWrap_mul (m n : Nat) :
    ofNatWrap hi (m * n) = wrapping_mul (ofNatWrap hi m) (ofNatWrap hi n) :=
  ext (by
    rw [toNat_wrapping_mul, toNat_ofNatWrap, toNat_ofNatWrap, toNat_ofNatWrap]
    simp [Nat.mul_mod])

/-- Reduction sends `0` to the least value. -/
@[simp] theorem ofNatWrap_zero : ofNatWrap hi 0 = minVal hi :=
  ext (by rw [toNat_ofNatWrap, toNat_minVal, Nat.zero_mod])

/-! ### Consequences: the wrapping operations satisfy the ring laws -/

/-- Wrapping multiplication distributes over wrapping addition. -/
theorem wrapping_mul_wrapping_add (a b c : TopBoundedUInt64 hi) :
    wrapping_mul a (wrapping_add b c)
      = wrapping_add (wrapping_mul a b) (wrapping_mul a c) := by
  rw [← ofNatWrap_toNat a, ← ofNatWrap_toNat b, ← ofNatWrap_toNat c,
    ← ofNatWrap_add, ← ofNatWrap_mul, ← ofNatWrap_mul, ← ofNatWrap_mul, ← ofNatWrap_add,
    Nat.mul_add]

/-- Wrapping subtraction is the inverse of wrapping addition. -/
theorem wrapping_add_wrapping_sub (a b : TopBoundedUInt64 hi) :
    wrapping_add (wrapping_sub a b) b = a := by
  apply ext
  rw [toNat_wrapping_add, toNat_wrapping_sub, Nat.mod_add_mod]
  have hb := toNat_le b
  have ha := toNat_le a
  have hp : period hi = hi.toNat + 1 := rfl
  have heq : a.toNat + period hi - b.toNat + b.toNat = a.toNat + period hi := by omega
  rw [heq, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (toNat_lt_period a)

end TopBoundedUInt64
