import IntUInt53.TopBoundedUInt64AndBoundedInt64Common.WordAux

/-!
# `BoundedInt64` : signed machine words with proved lower and upper bounds

`BoundedInt64 lo hi` is the type of `Int64` values `val` with `lo ≤ val ≤ hi`.
An element is *literally* a machine word together with proofs that it is in
range, so the set of representable values is exactly the integer interval
`[lo, hi]`.

No proof argument appears in the type: if `hi < lo` then the type is simply
empty, and every operation below derives `lo ≤ hi` from the elements it is
given.

This file contains the type, the map `toInt` into the integers, the
constructors (`ofIntMem`, `ofInt?`, `ofIntWrap`, `ofIntSat`) and the order
instances.  The arithmetic operations live in
`IntUInt53.BoundedInt64.Add`, `.Sub` and `.Mul`.

Only the Lean core library is used.
-/

set_option autoImplicit false

open BoundedWordAux

/-- `BoundedInt64 lo hi` is the type of `Int64` values `val` with `lo ≤ val ≤ hi`. -/
structure BoundedInt64 (lo hi : Int64) where
  /-- The underlying machine word. -/
  val   : Int64
  /-- The proof that the word is at least the lower bound. -/
  lo_le : lo ≤ val
  /-- The proof that the word is at most the upper bound. -/
  le_hi : val ≤ hi
deriving DecidableEq, Repr

namespace BoundedInt64

variable {lo hi : Int64}

/-! ### The integer denoted by a value -/

/-- The integer denoted by a bounded word. -/
def toInt (a : BoundedInt64 lo hi) : Int := a.val.toInt

@[simp] theorem toInt_mk (v : Int64) (h₁ : lo ≤ v) (h₂ : v ≤ hi) :
    (BoundedInt64.mk v h₁ h₂).toInt = v.toInt := rfl

theorem lo_le_toInt (a : BoundedInt64 lo hi) : lo.toInt ≤ a.toInt := int64_le_iff.mp a.lo_le

theorem toInt_le_hi (a : BoundedInt64 lo hi) : a.toInt ≤ hi.toInt := int64_le_iff.mp a.le_hi

/-- The existence of an element shows that the range is nonempty. -/
theorem lo_le_hi (a : BoundedInt64 lo hi) : lo ≤ hi :=
  int64_le_iff.mpr (Int.le_trans (lo_le_toInt a) (toInt_le_hi a))

theorem lo_toInt_le_hi_toInt (a : BoundedInt64 lo hi) : lo.toInt ≤ hi.toInt :=
  Int.le_trans (lo_le_toInt a) (toInt_le_hi a)

/-- Two bounded words are equal exactly when they denote the same integer. -/
theorem ext_iff {a b : BoundedInt64 lo hi} : a = b ↔ a.toInt = b.toInt := by
  constructor
  · intro h; rw [h]
  · intro h
    cases a; cases b
    simpa using int64_eq_of_toInt_eq h

theorem ext {a b : BoundedInt64 lo hi} (h : a.toInt = b.toInt) : a = b := ext_iff.mpr h

/-! ### The range and its size -/

/-- The number of distinct values of `BoundedInt64 lo hi`, namely `hi - lo + 1`.
This is the period of the wrapping operations. -/
def period (lo hi : Int64) : Int := hi.toInt - lo.toInt + 1

theorem period_pos (h : lo ≤ hi) : 0 < period lo hi := by
  have := int64_le_iff.mp h
  unfold period; omega

theorem period_ne_zero (h : lo ≤ hi) : period lo hi ≠ 0 := Int.ne_of_gt (period_pos h)

/-- An integer is representable exactly when it lies between the bounds. -/
def InRange (lo hi : Int64) (n : Int) : Prop := lo.toInt ≤ n ∧ n ≤ hi.toInt

instance (lo hi : Int64) (n : Int) : Decidable (InRange lo hi n) := by
  unfold InRange; infer_instance

theorem inRange_toInt (a : BoundedInt64 lo hi) : InRange lo hi a.toInt :=
  ⟨lo_le_toInt a, toInt_le_hi a⟩

theorem inRange_iff_sub_lt_period {n : Int} :
    InRange lo hi n ↔ (lo.toInt ≤ n ∧ n - lo.toInt < period lo hi) := by
  unfold InRange period; omega

/-! ### Constructors -/

/-- Build a value from an integer known to be in range. -/
def ofIntMem (lo hi : Int64) (n : Int) (h₁ : lo.toInt ≤ n) (h₂ : n ≤ hi.toInt) :
    BoundedInt64 lo hi :=
  have hlo : -2 ^ 63 ≤ n := Int.le_trans (neg_two_pow_63_le_toInt lo) h₁
  have hhi : n < 2 ^ 63 := Int.lt_of_le_of_lt h₂ (toInt_lt_two_pow_63 hi)
  ⟨Int64.ofInt n,
    int64_le_iff.mpr (by rw [toInt_ofInt_of_mem hlo hhi]; exact h₁),
    int64_le_iff.mpr (by rw [toInt_ofInt_of_mem hlo hhi]; exact h₂)⟩

@[simp] theorem toInt_ofIntMem (n : Int) (h₁ : lo.toInt ≤ n) (h₂ : n ≤ hi.toInt) :
    (ofIntMem lo hi n h₁ h₂).toInt = n :=
  toInt_ofInt_of_mem (Int.le_trans (neg_two_pow_63_le_toInt lo) h₁)
    (Int.lt_of_le_of_lt h₂ (toInt_lt_two_pow_63 hi))

/-- The checked constructor: `none` when the integer is out of range. -/
def ofInt? (lo hi : Int64) (n : Int) : Option (BoundedInt64 lo hi) :=
  if h : lo.toInt ≤ n ∧ n ≤ hi.toInt then some (ofIntMem lo hi n h.1 h.2) else none

theorem ofInt?_eq_some_iff {n : Int} {a : BoundedInt64 lo hi} :
    ofInt? lo hi n = some a ↔ a.toInt = n := by
  unfold ofInt?
  split
  · next h =>
    constructor
    · intro hs; rw [← Option.some.inj hs, toInt_ofIntMem]
    · intro hv; exact congrArg some (ext (by rw [toInt_ofIntMem, hv]))
  · next h =>
    constructor
    · intro hs; exact absurd hs (by simp)
    · intro hv; exact absurd ⟨hv ▸ lo_le_toInt a, hv ▸ toInt_le_hi a⟩ h

theorem ofInt?_eq_none_iff {n : Int} : ofInt? lo hi n = none ↔ ¬ InRange lo hi n := by
  unfold ofInt? InRange
  split <;> simp_all

theorem ofInt?_of_inRange {n : Int} (h : InRange lo hi n) :
    ofInt? lo hi n = some (ofIntMem lo hi n h.1 h.2) := dite_eq_left h

/-- The wrapping constructor: reduce modulo the period `hi - lo + 1`, keeping the
representative in `[lo, hi]`. -/
def ofIntWrap (h : lo ≤ hi) (n : Int) : BoundedInt64 lo hi :=
  have hp : 0 < period lo hi := period_pos h
  have h₁ : (0 : Int) ≤ (n - lo.toInt) % period lo hi :=
    Int.emod_nonneg _ (Int.ne_of_gt hp)
  have h₂ : (n - lo.toInt) % period lo hi < period lo hi := Int.emod_lt_of_pos _ hp
  ofIntMem lo hi (lo.toInt + (n - lo.toInt) % period lo hi) (by omega)
    (by unfold period at h₂ ⊢; omega)

@[simp] theorem toInt_ofIntWrap (h : lo ≤ hi) (n : Int) :
    (ofIntWrap h n).toInt = lo.toInt + (n - lo.toInt) % period lo hi := by
  unfold ofIntWrap; rw [toInt_ofIntMem]

theorem ofIntWrap_of_inRange (h : lo ≤ hi) {n : Int} (hr : InRange lo hi n) :
    (ofIntWrap h n).toInt = n := by
  rw [toInt_ofIntWrap]
  have h₁ : (0 : Int) ≤ n - lo.toInt := by unfold InRange at hr; omega
  have h₂ : n - lo.toInt < period lo hi := (inRange_iff_sub_lt_period.mp hr).2
  rw [Int.emod_eq_of_lt h₁ h₂]
  omega

/-- Wrapping is invariant under adding a multiple of the period. -/
theorem toInt_ofIntWrap_add_mul_period (h : lo ≤ hi) {m k : Int} (hr : InRange lo hi m) :
    (ofIntWrap h (m + k * period lo hi)).toInt = m := by
  rw [toInt_ofIntWrap]
  have h₁ : (0 : Int) ≤ m - lo.toInt := by unfold InRange at hr; omega
  have h₂ : m - lo.toInt < period lo hi := (inRange_iff_sub_lt_period.mp hr).2
  have hrw : m + k * period lo hi - lo.toInt = (m - lo.toInt) + k * period lo hi := by
    generalize k * period lo hi = t
    omega
  rw [hrw, Int.add_mul_emod_self_right, Int.emod_eq_of_lt h₁ h₂]
  omega

/-- Above the upper bound, wrapping subtracts exactly one period. -/
theorem toInt_ofIntWrap_sub_period (h : lo ≤ hi) {n : Int} (h₁ : hi.toInt < n)
    (h₂ : n - period lo hi ≤ hi.toInt) :
    (ofIntWrap h n).toInt = n - period lo hi := by
  have hr : InRange lo hi (n - period lo hi) := by
    unfold InRange period at *; omega
  have key := toInt_ofIntWrap_add_mul_period (k := 1) h hr
  rw [Int.one_mul] at key
  have hn : n - period lo hi + period lo hi = n := by omega
  rwa [hn] at key

/-- Below the lower bound, wrapping adds exactly one period. -/
theorem toInt_ofIntWrap_add_period (h : lo ≤ hi) {n : Int} (h₁ : n < lo.toInt)
    (h₂ : lo.toInt ≤ n + period lo hi) :
    (ofIntWrap h n).toInt = n + period lo hi := by
  have hr : InRange lo hi (n + period lo hi) := by
    unfold InRange period at *; omega
  have key := toInt_ofIntWrap_add_mul_period (k := -1) h hr
  rw [Int.neg_one_mul] at key
  have hn : n + period lo hi + -period lo hi = n := by omega
  rwa [hn] at key

/-- The saturating constructor: clamp to `[lo, hi]`. -/
def ofIntSat (h : lo ≤ hi) (n : Int) : BoundedInt64 lo hi :=
  have hle : lo.toInt ≤ hi.toInt := int64_le_iff.mp h
  ofIntMem lo hi (max lo.toInt (min n hi.toInt)) (by omega) (by omega)

@[simp] theorem toInt_ofIntSat (h : lo ≤ hi) (n : Int) :
    (ofIntSat h n).toInt = max lo.toInt (min n hi.toInt) := by
  unfold ofIntSat; rw [toInt_ofIntMem]

theorem ofIntSat_of_inRange (h : lo ≤ hi) {n : Int} (hr : InRange lo hi n) :
    (ofIntSat h n).toInt = n := by
  rw [toInt_ofIntSat]
  unfold InRange at hr
  omega

/-! ### Distinguished values -/

/-- The largest value, `hi` itself. -/
def maxVal (h : lo ≤ hi) : BoundedInt64 lo hi := ⟨hi, h, int64_le_iff.mpr (Int.le_refl _)⟩

/-- The smallest value, `lo` itself. -/
def minVal (h : lo ≤ hi) : BoundedInt64 lo hi := ⟨lo, int64_le_iff.mpr (Int.le_refl _), h⟩

@[simp] theorem toInt_maxVal (h : lo ≤ hi) : (maxVal h).toInt = hi.toInt := rfl

@[simp] theorem toInt_minVal (h : lo ≤ hi) : (minVal h).toInt = lo.toInt := rfl

theorem le_maxVal (a : BoundedInt64 lo hi) : a.toInt ≤ (maxVal (lo_le_hi a)).toInt :=
  toInt_le_hi a

theorem minVal_le (a : BoundedInt64 lo hi) : (minVal (lo_le_hi a)).toInt ≤ a.toInt :=
  lo_le_toInt a

/-! ### Order -/

instance : LE (BoundedInt64 lo hi) := ⟨fun a b => a.toInt ≤ b.toInt⟩
instance : LT (BoundedInt64 lo hi) := ⟨fun a b => a.toInt < b.toInt⟩

theorem le_def {a b : BoundedInt64 lo hi} : a ≤ b ↔ a.toInt ≤ b.toInt := Iff.rfl
theorem lt_def {a b : BoundedInt64 lo hi} : a < b ↔ a.toInt < b.toInt := Iff.rfl

instance (a b : BoundedInt64 lo hi) : Decidable (a ≤ b) := decidable_of_iff _ le_def.symm
instance (a b : BoundedInt64 lo hi) : Decidable (a < b) := decidable_of_iff _ lt_def.symm

theorem le_refl' (a : BoundedInt64 lo hi) : a ≤ a := Int.le_refl _

theorem le_trans' {a b c : BoundedInt64 lo hi} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  Int.le_trans h₁ h₂

theorem le_antisymm' {a b : BoundedInt64 lo hi} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b :=
  ext (Int.le_antisymm h₁ h₂)

theorem le_total' (a b : BoundedInt64 lo hi) : a ≤ b ∨ b ≤ a := by
  rcases Int.le_total a.toInt b.toInt with h | h
  · exact Or.inl h
  · exact Or.inr h

end BoundedInt64
