import IntUInt53.BoundedInt64

/-!
# `Int53` : exact signed 53-bit integers

`Int53` is the type of integers in the range
`[-9007199254740991, 9007199254740991]`, i.e. `[-(2 ^ 53 - 1), 2 ^ 53 - 1]`.
It is the instance

```
abbrev Int53 := BoundedInt64 (-(2 ^ 53 - 1)) (2 ^ 53 - 1)
```

of the generic bounded type, so a value is *literally* an `Int64` machine word
together with proofs that it lies between the two bounds.  The range is
symmetric, exactly like the set of integers that IEEE-754 binary64 represents
exactly; no floating point representation is used, so arithmetic here is exact:
no rounding, no approximation, no fractional drift.

This file fixes the constants (`MAX`, `MIN`, `SIZE`), relates them to the
generic bounds, and provides the constructors.  The four variants of each
operation are inherited from `BoundedInt64` and specialised in
`IntUInt53.Int53.Add`, `.Sub` and `.Mul`.
-/

set_option autoImplicit false

/-- Signed 53-bit integers: the numbers `-9007199254740991, …, 9007199254740991`. -/
abbrev Int53 := BoundedInt64 (-(2 ^ 53 - 1)) (2 ^ 53 - 1)

namespace Int53

/-- The largest value of `Int53`, namely `9007199254740991 = 2 ^ 53 - 1`. -/
def MAX : Int := 9007199254740991

/-- The smallest value of `Int53`, namely `-9007199254740991`. -/
def MIN : Int := -9007199254740991

/-- The number of distinct values of `Int53`, namely `2 ^ 54 - 1`. -/
def SIZE : Int := 18014398509481983

theorem MIN_eq_neg_MAX : MIN = -MAX := by decide

theorem SIZE_eq : SIZE = MAX - MIN + 1 := by decide

/-- The generic upper bound of `Int53` denotes `MAX`. -/
@[simp] theorem hi_toInt : (2 ^ 53 - 1 : Int64).toInt = MAX := rfl

/-- The generic lower bound of `Int53` denotes `MIN`. -/
@[simp] theorem lo_toInt : (-(2 ^ 53 - 1) : Int64).toInt = MIN := rfl

/-- The range of `Int53` is nonempty. -/
theorem lo_le_hi : (-(2 ^ 53 - 1) : Int64) ≤ (2 ^ 53 - 1 : Int64) := by decide

/-- The period of the wrapping operations on `Int53` is `SIZE = 2 ^ 54 - 1`. -/
@[simp] theorem period_eq :
    BoundedInt64.period (-(2 ^ 53 - 1)) (2 ^ 53 - 1) = SIZE := by decide

/-! ### Range -/

theorem le_MAX (a : Int53) : a.toInt ≤ MAX := a.toInt_le_hi

theorem MIN_le (a : Int53) : MIN ≤ a.toInt := a.lo_le_toInt

/-- An integer is representable as an `Int53` exactly when it lies in `[MIN, MAX]`. -/
theorem inRange_iff {n : Int} :
    BoundedInt64.InRange (-(2 ^ 53 - 1)) (2 ^ 53 - 1) n ↔ (MIN ≤ n ∧ n ≤ MAX) := Iff.rfl

/-! ### Constructors -/

/-- Build an `Int53` from a literal that is in range.  The side conditions are
discharged by `decide`, so an out-of-range literal such as `Int53.ofInt 9007199254740992`
is rejected at compile time instead of silently wrapping. -/
def ofInt (n : Int) (h₁ : MIN ≤ n := by decide) (h₂ : n ≤ MAX := by decide) : Int53 :=
  BoundedInt64.ofIntMem _ _ n h₁ h₂

@[simp] theorem toInt_ofInt (n : Int) (h₁ : MIN ≤ n) (h₂ : n ≤ MAX) :
    (ofInt n h₁ h₂).toInt = n := by
  unfold ofInt; exact BoundedInt64.toInt_ofIntMem n _ _

/-- The checked constructor: `none` when the integer is out of range. -/
def ofInt? (n : Int) : Option Int53 := BoundedInt64.ofInt? _ _ n

theorem ofInt?_eq_some_iff {n : Int} {a : Int53} : ofInt? n = some a ↔ a.toInt = n :=
  BoundedInt64.ofInt?_eq_some_iff

theorem ofInt?_eq_none_iff {n : Int} : ofInt? n = none ↔ (n < MIN ∨ MAX < n) := by
  unfold ofInt?
  rw [BoundedInt64.ofInt?_eq_none_iff]
  unfold BoundedInt64.InRange
  rw [hi_toInt, lo_toInt]
  omega

/-- The wrapping constructor: reduce modulo `SIZE = 2 ^ 54 - 1` into `[MIN, MAX]`. -/
def ofIntWrap (n : Int) : Int53 := BoundedInt64.ofIntWrap lo_le_hi n

@[simp] theorem toInt_ofIntWrap (n : Int) :
    (ofIntWrap n).toInt = MIN + (n - MIN) % SIZE := by
  unfold ofIntWrap
  rw [BoundedInt64.toInt_ofIntWrap, lo_toInt, period_eq]

/-- The saturating constructor: clamp to `[MIN, MAX]`. -/
def ofIntSat (n : Int) : Int53 := BoundedInt64.ofIntSat lo_le_hi n

@[simp] theorem toInt_ofIntSat (n : Int) :
    (ofIntSat n).toInt = max MIN (min n MAX) := by
  unfold ofIntSat
  rw [BoundedInt64.toInt_ofIntSat, hi_toInt, lo_toInt]

/-! ### Distinguished values -/

/-- The largest `Int53`, namely `9007199254740991`. -/
def maxVal : Int53 := BoundedInt64.maxVal lo_le_hi

/-- The smallest `Int53`, namely `-9007199254740991`. -/
def minVal : Int53 := BoundedInt64.minVal lo_le_hi

/-- Zero. -/
def zero : Int53 := ofInt 0

@[simp] theorem toInt_maxVal : maxVal.toInt = MAX := rfl

@[simp] theorem toInt_minVal : minVal.toInt = MIN := rfl

@[simp] theorem toInt_zero : zero.toInt = 0 := by
  unfold zero; rw [toInt_ofInt]

theorem le_maxVal (a : Int53) : a.toInt ≤ maxVal.toInt := le_MAX a

theorem minVal_le (a : Int53) : minVal.toInt ≤ a.toInt := MIN_le a

end Int53
