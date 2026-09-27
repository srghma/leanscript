import IntUInt53.UInt53AndInt53Common.Convert
import IntUInt53.UInt53
import IntUInt53.Int53

/-!
# Summary: the exactness guarantee, in one place

This module collects the headline results of the development.  For both types
and for each of addition, subtraction and multiplication it states, in a single
theorem, that *all four variants return the exact mathematical result whenever
that result is representable*:

* `checked_*` returns `some` of it;
* `wrapping_*` returns it (no wrapping occurs);
* `overflowing_*` returns it together with the flag `false`;
* `saturating_*` returns it (no clamping occurs).

There is no rounding, no approximation and no fractional drift anywhere: the
values denote natural numbers (`UInt53.toNat`) and integers (`Int53.toInt`),
and the specifications are equations between those exact numbers.
-/

set_option autoImplicit false

namespace Exact53

open TopBoundedUInt64 BoundedInt64

/-! ### `UInt53` -/

/-- Addition on `UInt53` is exact whenever the sum is representable. -/
theorem uint53_add {a b : UInt53} (h : a.toNat + b.toNat ≤ UInt53.MAX) :
    (∃ c, checked_add a b = some c ∧ c.toNat = a.toNat + b.toNat) ∧
      (wrapping_add a b).toNat = a.toNat + b.toNat ∧
      (overflowing_add a b).1.toNat = a.toNat + b.toNat ∧
      (overflowing_add a b).2 = false ∧
      (saturating_add a b).toNat = a.toNat + b.toNat := by
  refine ⟨UInt53.checked_add_exact h, UInt53.toNat_wrapping_add_exact h,
    UInt53.toNat_overflowing_add_exact h, ?_, UInt53.toNat_saturating_add_exact h⟩
  cases hb : (overflowing_add a b).2 with
  | false => rfl
  | true =>
    have := UInt53.overflowing_add_snd_iff.mp hb
    omega

/-- Subtraction on `UInt53` is exact whenever the difference is representable. -/
theorem uint53_sub {a b : UInt53} (h : b.toNat ≤ a.toNat) :
    (∃ c, checked_sub a b = some c ∧ c.toNat = a.toNat - b.toNat) ∧
      (wrapping_sub a b).toNat = a.toNat - b.toNat ∧
      (overflowing_sub a b).1.toNat = a.toNat - b.toNat ∧
      (overflowing_sub a b).2 = false ∧
      (saturating_sub a b).toNat = a.toNat - b.toNat := by
  refine ⟨UInt53.checked_sub_exact h, UInt53.toNat_wrapping_sub_exact h,
    UInt53.toNat_overflowing_sub_exact h, ?_, UInt53.toNat_saturating_sub a b⟩
  cases hb : (overflowing_sub a b).2 with
  | false => rfl
  | true =>
    have := UInt53.overflowing_sub_snd_iff.mp hb
    omega

/-- Multiplication on `UInt53` is exact whenever the product is representable. -/
theorem uint53_mul {a b : UInt53} (h : a.toNat * b.toNat ≤ UInt53.MAX) :
    (∃ c, checked_mul a b = some c ∧ c.toNat = a.toNat * b.toNat) ∧
      (wrapping_mul a b).toNat = a.toNat * b.toNat ∧
      (overflowing_mul a b).1.toNat = a.toNat * b.toNat ∧
      (overflowing_mul a b).2 = false ∧
      (saturating_mul a b).toNat = a.toNat * b.toNat := by
  refine ⟨UInt53.checked_mul_exact h, UInt53.toNat_wrapping_mul_exact h,
    UInt53.toNat_overflowing_mul_exact h, ?_, UInt53.toNat_saturating_mul_exact h⟩
  cases hb : (overflowing_mul a b).2 with
  | false => rfl
  | true =>
    have := UInt53.overflowing_mul_snd_iff.mp hb
    omega

/-! ### `Int53` -/

/-- Addition on `Int53` is exact whenever the sum is representable. -/
theorem int53_add {a b : Int53} (h₁ : Int53.MIN ≤ a.toInt + b.toInt)
    (h₂ : a.toInt + b.toInt ≤ Int53.MAX) :
    (∃ c, checked_add a b = some c ∧ c.toInt = a.toInt + b.toInt) ∧
      (wrapping_add a b).toInt = a.toInt + b.toInt ∧
      (overflowing_add a b).1.toInt = a.toInt + b.toInt ∧
      (overflowing_add a b).2 = false ∧
      (saturating_add a b).toInt = a.toInt + b.toInt := by
  refine ⟨Int53.checked_add_exact h₁ h₂, Int53.toInt_wrapping_add_exact h₁ h₂,
    Int53.toInt_overflowing_add_exact h₁ h₂, ?_, Int53.toInt_saturating_add_exact h₁ h₂⟩
  cases hb : (overflowing_add a b).2 with
  | false => rfl
  | true =>
    have := Int53.overflowing_add_snd_iff.mp hb
    omega

/-- Subtraction on `Int53` is exact whenever the difference is representable. -/
theorem int53_sub {a b : Int53} (h₁ : Int53.MIN ≤ a.toInt - b.toInt)
    (h₂ : a.toInt - b.toInt ≤ Int53.MAX) :
    (∃ c, checked_sub a b = some c ∧ c.toInt = a.toInt - b.toInt) ∧
      (wrapping_sub a b).toInt = a.toInt - b.toInt ∧
      (overflowing_sub a b).1.toInt = a.toInt - b.toInt ∧
      (overflowing_sub a b).2 = false ∧
      (saturating_sub a b).toInt = a.toInt - b.toInt := by
  refine ⟨Int53.checked_sub_exact h₁ h₂, Int53.toInt_wrapping_sub_exact h₁ h₂,
    Int53.toInt_overflowing_sub_exact h₁ h₂, ?_, Int53.toInt_saturating_sub_exact h₁ h₂⟩
  cases hb : (overflowing_sub a b).2 with
  | false => rfl
  | true =>
    have := Int53.overflowing_sub_snd_iff.mp hb
    omega

/-- Multiplication on `Int53` is exact whenever the product is representable. -/
theorem int53_mul {a b : Int53} (h₁ : Int53.MIN ≤ a.toInt * b.toInt)
    (h₂ : a.toInt * b.toInt ≤ Int53.MAX) :
    (∃ c, checked_mul a b = some c ∧ c.toInt = a.toInt * b.toInt) ∧
      (wrapping_mul a b).toInt = a.toInt * b.toInt ∧
      (overflowing_mul a b).1.toInt = a.toInt * b.toInt ∧
      (overflowing_mul a b).2 = false ∧
      (saturating_mul a b).toInt = a.toInt * b.toInt := by
  refine ⟨Int53.checked_mul_exact h₁ h₂, Int53.toInt_wrapping_mul_exact h₁ h₂,
    Int53.toInt_overflowing_mul_exact h₁ h₂, ?_, Int53.toInt_saturating_mul_exact h₁ h₂⟩
  cases hb : (overflowing_mul a b).2 with
  | false => rfl
  | true =>
    have := Int53.overflowing_mul_snd_iff.mp hb
    omega

/-! ### `1 + 2 = 3`, in both types -/

theorem uint53_one_add_two :
    checked_add (UInt53.ofNat 1) (UInt53.ofNat 2) = some (UInt53.ofNat 3) :=
  UInt53.one_add_two

theorem int53_one_add_two :
    checked_add (Int53.ofInt 1) (Int53.ofInt 2) = some (Int53.ofInt 3) :=
  Int53.one_add_two

/-! ### Division -/

/-- Division on `UInt53` is exact for every nonzero divisor: all four variants
return the exact quotient, and the only failure is a zero divisor. -/
theorem uint53_div {a b : UInt53} (h : b.toNat ≠ 0) :
    (∃ c, checked_div a b = some c ∧ c.toNat = a.toNat / b.toNat) ∧
      (wrapping_div a b).toNat = a.toNat / b.toNat ∧
      (overflowing_div a b).1.toNat = a.toNat / b.toNat ∧
      (overflowing_div a b).2 = false ∧
      (saturating_div a b).toNat = a.toNat / b.toNat :=
  UInt53.div_variants_exact h

/-- Division on `Int53` (truncating towards zero) is exact for every nonzero
divisor; because the range is symmetric, no quotient can leave it. -/
theorem int53_div {a b : Int53} (h : b.toInt ≠ 0) :
    (∃ c, checked_div a b = some c ∧ c.toInt = a.toInt.tdiv b.toInt) ∧
      (wrapping_div a b).toInt = a.toInt.tdiv b.toInt ∧
      (overflowing_div a b).1.toInt = a.toInt.tdiv b.toInt ∧
      (overflowing_div a b).2 = false ∧
      (saturating_div a b).toInt = a.toInt.tdiv b.toInt :=
  Int53.div_variants_exact h

/-! ### Negation on `Int53` is total -/

/-- Negation on `Int53` never overflows, and all four variants return `-a`. -/
theorem int53_neg (a : Int53) :
    (∃ c, checked_neg a = some c ∧ c.toInt = -a.toInt) ∧
      (wrapping_neg a).toInt = -a.toInt ∧
      (overflowing_neg a).1.toInt = -a.toInt ∧
      (overflowing_neg a).2 = false ∧
      (saturating_neg a).toInt = -a.toInt :=
  Int53.neg_variants_exact a

/-! ### Losing nothing at all -/

/-- The widening product of two `UInt53` values loses nothing: its two 53-bit
limbs recover the exact product, which need not be representable itself. -/
theorem uint53_mul_wide (a b : UInt53) :
    (mulWide a b).1.toNat * UInt53.SIZE + (mulWide a b).2.toNat = a.toNat * b.toNat :=
  UInt53.mulWide_exact a b

/-- A whole chain of checked additions on `UInt53` succeeds exactly when the
exact total is representable: no intermediate step can fail on its own. -/
theorem uint53_sum_overflow_free {l : List UInt53} :
    (checked_sum l).isSome ↔ sumNat l ≤ UInt53.MAX :=
  UInt53.checked_sum_isSome_iff'

/-- Serialising a `UInt53` to bytes and reading it back is the identity. -/
theorem uint53_bytes_round_trip (a : UInt53) : UInt53.ofBytes? (UInt53.toBytes a) = some a :=
  UInt53.ofBytes?_toBytes a

/-- Serialising an `Int53` to a sign and bytes and reading it back is the identity. -/
theorem int53_bytes_round_trip (a : Int53) :
    Int53.ofBytes? (Int53.toBytes a).1 (Int53.toBytes a).2 = some a :=
  Int53.ofBytes?_toBytes a

/-! ### The compiled implementation is the specification -/

/-- The bound of `UInt53` satisfies both side conditions of the machine-word
implementation, so compiled code takes the fast path for every operation. -/
theorem uint53_machine_side_conditions :
    TopBoundedUInt64.smallBound (2 ^ 53 - 1) = true ∧
      TopBoundedUInt64.pow2Period (2 ^ 53 - 1) = true := by
  constructor <;> decide

/-- The bounds of `Int53` satisfy the side condition of the machine-word
implementation. -/
theorem int53_machine_side_condition :
    BoundedInt64.moderate (-(2 ^ 53 - 1)) (2 ^ 53 - 1) = true := by decide

/-- On `UInt53`, the machine-word implementation that compiled code runs *is* the
specification: the two functions are equal, so no trust is placed in the fast path. -/
theorem uint53_machine_implementation :
    (TopBoundedUInt64.checked_add (hi := 2 ^ 53 - 1)) = TopBoundedUInt64.checked_add_fast ∧
      (TopBoundedUInt64.wrapping_add (hi := 2 ^ 53 - 1)) = TopBoundedUInt64.wrapping_add_fast ∧
      (TopBoundedUInt64.checked_mul (hi := 2 ^ 53 - 1)) = TopBoundedUInt64.checked_mul_fast ∧
      (TopBoundedUInt64.wrapping_mul (hi := 2 ^ 53 - 1)) = TopBoundedUInt64.wrapping_mul_fast :=
  ⟨congrFun TopBoundedUInt64.checked_add_eq_fast _,
    congrFun TopBoundedUInt64.wrapping_add_eq_fast _,
    congrFun TopBoundedUInt64.checked_mul_eq_fast _,
    congrFun TopBoundedUInt64.wrapping_mul_eq_fast _⟩

/-- The same on `Int53`. -/
theorem int53_machine_implementation :
    (BoundedInt64.checked_add (lo := -(2 ^ 53 - 1)) (hi := 2 ^ 53 - 1))
        = BoundedInt64.checked_add_fast ∧
      (BoundedInt64.wrapping_add (lo := -(2 ^ 53 - 1)) (hi := 2 ^ 53 - 1))
        = BoundedInt64.wrapping_add_fast ∧
      (BoundedInt64.checked_mul (lo := -(2 ^ 53 - 1)) (hi := 2 ^ 53 - 1))
        = BoundedInt64.checked_mul_fast ∧
      (BoundedInt64.wrapping_mul (lo := -(2 ^ 53 - 1)) (hi := 2 ^ 53 - 1))
        = BoundedInt64.wrapping_mul_fast :=
  ⟨congrFun (congrFun BoundedInt64.checked_add_eq_fast _) _,
    congrFun (congrFun BoundedInt64.wrapping_add_eq_fast _) _,
    congrFun (congrFun BoundedInt64.checked_mul_eq_fast _) _,
    congrFun (congrFun BoundedInt64.wrapping_mul_eq_fast _) _⟩

end Exact53
