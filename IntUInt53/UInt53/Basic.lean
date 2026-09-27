import IntUInt53.TopBoundedUInt64
import Aesop

/-!
# `UInt53` : exact unsigned 53-bit integers

`UInt53` is the type of natural numbers in the range `[0, 9007199254740991]`,
i.e. `[0, 2 ^ 53 - 1]`.  It is the instance

```
abbrev UInt53 := TopBoundedUInt64 (2 ^ 53 - 1)
```

of the generic bounded type, so a value is *literally* a `UInt64` machine word
together with a proof that it is at most `2 ^ 53 - 1`.  No floating point
representation is involved anywhere, hence there is no rounding, no
approximation and no fractional drift: `1 + 2 = 3` holds on the nose, and more
generally every operation whose mathematical result fits in the range is
computed exactly.

This file fixes the constants (`MAX`, `MIN`, `SIZE`), relates them to the
generic bound, and provides the constructors.  The four variants of each
operation are inherited from `TopBoundedUInt64` and specialised in
`IntUInt53.UInt53.Add`, `.Sub` and `.Mul`.
-/

set_option autoImplicit false

/-- Unsigned 53-bit integers: the numbers `0, 1, …, 9007199254740991`. -/
abbrev UInt53 := TopBoundedUInt64 (2 ^ 53 - 1)

namespace UInt53

/-- The largest value of `UInt53`, namely `9007199254740991 = 2 ^ 53 - 1`. -/
def MAX : Nat := 9007199254740991

/-- The smallest value of `UInt53`, namely `0`. -/
def MIN : Nat := 0

/-- The number of distinct values of `UInt53`, namely `2 ^ 53`. -/
def SIZE : Nat := 2 ^ 53

theorem SIZE_eq : SIZE = 9007199254740992 := by decide

theorem MAX_add_one : MAX + 1 = SIZE := by decide

/-- The generic upper bound of `UInt53` denotes `MAX`. -/
@[simp] theorem hi_toNat : (2 ^ 53 - 1 : UInt64).toNat = MAX := rfl

/-- The period of the wrapping operations on `UInt53` is `SIZE = 2 ^ 53`. -/
@[simp] theorem period_eq : TopBoundedUInt64.period (2 ^ 53 - 1) = SIZE := rfl

/-! ### Range -/

/-- Every `UInt53` lies in the range `[0, 9007199254740991]`. -/
theorem le_MAX (a : UInt53) : a.toNat ≤ MAX := a.toNat_le

theorem MIN_le (a : UInt53) : MIN ≤ a.toNat := Nat.zero_le _

theorem toNat_lt_SIZE (a : UInt53) : a.toNat < SIZE := a.toNat_lt_period

/-- A natural number is representable as a `UInt53` exactly when it is at most `MAX`. -/
theorem inRange_iff {n : Nat} : TopBoundedUInt64.InRange (2 ^ 53 - 1) n ↔ n ≤ MAX := Iff.rfl

/-! ### Constructors -/

/-- Build a `UInt53` from a literal that is in range.  The side condition is
discharged by `decide`, so an out-of-range literal such as `UInt53.ofNat 9007199254740992`
is rejected at compile time instead of silently wrapping. -/
def ofNat (n : Nat) (h : n ≤ MAX := by decide) : UInt53 :=
  TopBoundedUInt64.ofNatLe _ n h

@[simp] theorem toNat_ofNat (n : Nat) (h : n ≤ MAX) : (ofNat n h).toNat = n := by
  have h' : n ≤ (2 ^ 53 - 1 : UInt64).toNat := by rw [hi_toNat]; exact h
  exact TopBoundedUInt64.toNat_ofNatLe n h'

/-- The checked constructor: `none` when the number exceeds `MAX`. -/
def ofNat? (n : Nat) : Option UInt53 := TopBoundedUInt64.ofNat? _ n

theorem ofNat?_eq_some_iff {n : Nat} {a : UInt53} : ofNat? n = some a ↔ a.toNat = n :=
  TopBoundedUInt64.ofNat?_eq_some_iff

theorem ofNat?_eq_none_iff {n : Nat} : ofNat? n = none ↔ MAX < n := by
  unfold ofNat?
  rw [TopBoundedUInt64.ofNat?_eq_none_iff]
  unfold TopBoundedUInt64.InRange
  rw [hi_toNat]
  omega

/-- The wrapping constructor: reduce modulo `SIZE = 2 ^ 53`. -/
def ofNatWrap (n : Nat) : UInt53 := TopBoundedUInt64.ofNatWrap _ n

@[simp] theorem toNat_ofNatWrap (n : Nat) : (ofNatWrap n).toNat = n % SIZE := by
  unfold ofNatWrap; rw [TopBoundedUInt64.toNat_ofNatWrap, period_eq]

/-- The saturating constructor: clamp to `MAX`. -/
def ofNatSat (n : Nat) : UInt53 := TopBoundedUInt64.ofNatSat _ n

@[simp] theorem toNat_ofNatSat (n : Nat) : (ofNatSat n).toNat = min n MAX := by
  unfold ofNatSat; rw [TopBoundedUInt64.toNat_ofNatSat, hi_toNat]

/-! ### Distinguished values -/

/-- The largest `UInt53`, namely `9007199254740991`. -/
def maxVal : UInt53 := TopBoundedUInt64.maxVal _

/-- The smallest `UInt53`, namely `0`. -/
def minVal : UInt53 := TopBoundedUInt64.minVal _

@[simp] theorem toNat_maxVal : maxVal.toNat = MAX := rfl

@[simp] theorem toNat_minVal : minVal.toNat = MIN := by
  show (TopBoundedUInt64.minVal _).toNat = MIN
  rw [TopBoundedUInt64.toNat_minVal]
  rfl

theorem le_maxVal (a : UInt53) : a.toNat ≤ maxVal.toNat := le_MAX a

theorem minVal_le (a : UInt53) : minVal.toNat ≤ a.toNat := by
  rw [toNat_minVal]; exact Nat.zero_le _

end UInt53
