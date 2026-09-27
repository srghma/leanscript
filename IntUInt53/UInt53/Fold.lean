import IntUInt53.UInt53.Add
import IntUInt53.TopBoundedUInt64.Fold

/-!
# Whole computations on `UInt53`

The overflow-freedom results of `TopBoundedUInt64.Fold`, specialised to
`UInt53`: a chain of checked additions is exact, it fails exactly when the
exact total exceeds `MAX`, and a simple count-times-bound criterion guarantees
that it cannot fail.
-/

set_option autoImplicit false

open TopBoundedUInt64

namespace UInt53

/-- A chain of checked additions on `UInt53` is exact. -/
theorem checked_sum_exact {l : List UInt53} {c : UInt53} :
    checked_sum l = some c ↔ c.toNat = sumNat l :=
  TopBoundedUInt64.checked_sum_eq_some_iff

/-- **Overflow freedom on `UInt53`**: the chain succeeds exactly when the exact
total is at most `MAX`. -/
theorem checked_sum_isSome_iff' {l : List UInt53} :
    (checked_sum l).isSome ↔ sumNat l ≤ MAX :=
  TopBoundedUInt64.checked_sum_isSome_iff

/-- A million summands, each at most a billion, cannot overflow a `UInt53`:
`10 ^ 6 * 10 ^ 9 = 10 ^ 15 ≤ 9007199254740991`. -/
theorem checked_sum_million_billions {l : List UInt53}
    (hbound : ∀ a ∈ l, a.toNat ≤ 10 ^ 9) (hlen : l.length ≤ 10 ^ 6) :
    ∃ c, checked_sum l = some c ∧ c.toNat = sumNat l := by
  refine TopBoundedUInt64.checked_sum_of_le (k := 10 ^ 9) hbound ?_
  rw [hi_toNat]
  have : l.length * 10 ^ 9 ≤ 10 ^ 6 * 10 ^ 9 := Nat.mul_le_mul_right _ hlen
  unfold MAX
  omega

/-- The checked dot product of two `UInt53` lists is exact. -/
theorem checked_dot_exact {xs ys : List UInt53} {c : UInt53} :
    checked_dot xs ys = some c ↔ c.toNat = dotNat xs ys :=
  TopBoundedUInt64.checked_dot_eq_some_iff

/-- `1 + 2 + 3 = 6`, as a chain of checked additions. -/
theorem checked_sum_one_two_three :
    checked_sum [ofNat 1, ofNat 2, ofNat 3] = some (ofNat 6) := by decide

/-- The dot product `[2, 3] · [4, 5] = 23`. -/
theorem checked_dot_example :
    checked_dot [ofNat 2, ofNat 3] [ofNat 4, ofNat 5] = some (ofNat 23) := by decide

/-- A chain that overflows is reported, not silently wrapped. -/
theorem checked_sum_overflow : checked_sum [maxVal, ofNat 1] = none := by decide

end UInt53
