import IntUInt53.TopBoundedUInt64AndBoundedInt64Common.WordAux

/-!
# `TopBoundedUInt64` : unsigned machine words with a proved upper bound

`TopBoundedUInt64 hi` is the type of `UInt64` values that are at most `hi`.  An
element is *literally* a machine word together with a proof that it is in
range, so the set of values a `TopBoundedUInt64 hi` can take is exactly
`{0, 1, …, hi}` — nothing else is representable.

Only an upper bound is needed: `0 ≤ a` holds for every `UInt64`, so an unsigned
bounded type carries a top bound only.  No proof argument appears in the type
itself; if one wants `hi` to be the maximum of a nonempty range that is
automatic, since `0 ≤ hi` always.

This file contains the type, the map `toNat` into the natural numbers, the
three constructors used throughout (`ofNatLe`, `ofNatWrap`, `ofNatSat`), the
partial constructor `ofNat?`, and the order instances.  The arithmetic
operations live in `IntUInt53.TopBoundedUInt64.Add`, `.Sub` and `.Mul`.

The development uses the Lean core library only; there is no Mathlib
dependency, and no floating point representation is involved anywhere.
-/

set_option autoImplicit false

open BoundedWordAux

/-- `TopBoundedUInt64 hi` is the type of `UInt64` values `val` with `val ≤ hi`. -/
structure TopBoundedUInt64 (hi : UInt64) where
  /-- The underlying machine word. -/
  val  : UInt64
  /-- The proof that the word is within the bound. -/
  isLe : val ≤ hi
deriving DecidableEq, Repr

namespace TopBoundedUInt64

variable {hi : UInt64}

/-! ### The natural number denoted by a value -/

/-- The natural number denoted by a bounded word. -/
def toNat (a : TopBoundedUInt64 hi) : Nat := a.val.toNat

@[simp] theorem toNat_mk (v : UInt64) (h : v ≤ hi) :
    (TopBoundedUInt64.mk v h).toNat = v.toNat := rfl

/-- Every value is at most the bound. -/
theorem toNat_le (a : TopBoundedUInt64 hi) : a.toNat ≤ hi.toNat :=
  uint64_le_iff.mp a.isLe

theorem toNat_lt_two_pow_64 (a : TopBoundedUInt64 hi) : a.toNat < 2 ^ 64 := toNat_lt a.val

/-- Two bounded words are equal exactly when they denote the same number. -/
theorem ext_iff {a b : TopBoundedUInt64 hi} : a = b ↔ a.toNat = b.toNat := by
  constructor
  · intro h; rw [h]
  · intro h
    cases a; cases b
    simpa using uint64_eq_of_toNat_eq h

theorem ext {a b : TopBoundedUInt64 hi} (h : a.toNat = b.toNat) : a = b := ext_iff.mpr h

/-! ### The range and its size -/

/-- The number of distinct values of `TopBoundedUInt64 hi`, namely `hi + 1`.
This is the period of the wrapping operations. -/
def period (hi : UInt64) : Nat := hi.toNat + 1

theorem period_pos (hi : UInt64) : 0 < period hi := Nat.succ_pos _

theorem toNat_lt_period (a : TopBoundedUInt64 hi) : a.toNat < period hi :=
  Nat.lt_succ_of_le (toNat_le a)

/-- A natural number is representable exactly when it is at most `hi`. -/
def InRange (hi : UInt64) (n : Nat) : Prop := n ≤ hi.toNat

instance (hi : UInt64) (n : Nat) : Decidable (InRange hi n) := by
  unfold InRange; infer_instance

theorem inRange_iff_lt_period {n : Nat} : InRange hi n ↔ n < period hi := by
  unfold InRange period; omega

theorem inRange_toNat (a : TopBoundedUInt64 hi) : InRange hi a.toNat := toNat_le a

/-! ### Constructors -/

/-- Build a value from a natural number known to be in range. -/
def ofNatLe (hi : UInt64) (n : Nat) (h : n ≤ hi.toNat) : TopBoundedUInt64 hi :=
  ⟨UInt64.ofNat n, by
    rw [uint64_le_iff, toNat_ofNat_of_lt (Nat.lt_of_le_of_lt h (toNat_lt hi))]
    exact h⟩

@[simp] theorem toNat_ofNatLe (n : Nat) (h : n ≤ hi.toNat) : (ofNatLe hi n h).toNat = n :=
  toNat_ofNat_of_lt (Nat.lt_of_le_of_lt h (toNat_lt hi))

/-- The checked constructor: `none` when the number does not fit. -/
def ofNat? (hi : UInt64) (n : Nat) : Option (TopBoundedUInt64 hi) :=
  if h : n ≤ hi.toNat then some (ofNatLe hi n h) else none

theorem ofNat?_eq_some_iff {n : Nat} {a : TopBoundedUInt64 hi} :
    ofNat? hi n = some a ↔ a.toNat = n := by
  unfold ofNat?
  split
  · next h =>
    constructor
    · intro hs; rw [← Option.some.inj hs, toNat_ofNatLe]
    · intro hv; exact congrArg some (ext (by rw [toNat_ofNatLe, hv]))
  · next h =>
    constructor
    · intro hs; exact absurd hs (by simp)
    · intro hv; exact absurd (hv ▸ toNat_le a) h

theorem ofNat?_eq_none_iff {n : Nat} : ofNat? hi n = none ↔ ¬ InRange hi n := by
  unfold ofNat? InRange
  split <;> simp_all

theorem ofNat?_of_inRange {n : Nat} (h : InRange hi n) :
    ofNat? hi n = some (ofNatLe hi n (show n ≤ hi.toNat from h)) := dite_eq_left h

theorem toNat_of_ofNat?_eq_some {n : Nat} {a : TopBoundedUInt64 hi}
    (h : ofNat? hi n = some a) : a.toNat = n := ofNat?_eq_some_iff.mp h

/-- The wrapping constructor: reduce modulo the period `hi + 1`. -/
def ofNatWrap (hi : UInt64) (n : Nat) : TopBoundedUInt64 hi :=
  ofNatLe hi (n % period hi) (by
    have h := Nat.mod_lt n (period_pos hi)
    have hp : period hi = hi.toNat + 1 := rfl
    omega)

@[simp] theorem toNat_ofNatWrap (n : Nat) : (ofNatWrap hi n).toNat = n % period hi := by
  unfold ofNatWrap; rw [toNat_ofNatLe]

theorem ofNatWrap_of_inRange {n : Nat} (h : InRange hi n) : (ofNatWrap hi n).toNat = n := by
  rw [toNat_ofNatWrap]
  exact Nat.mod_eq_of_lt (inRange_iff_lt_period.mp h)

/-- The saturating constructor: clamp to `hi`. -/
def ofNatSat (hi : UInt64) (n : Nat) : TopBoundedUInt64 hi :=
  ofNatLe hi (min n hi.toNat) (Nat.min_le_right _ _)

@[simp] theorem toNat_ofNatSat (n : Nat) : (ofNatSat hi n).toNat = min n hi.toNat := by
  unfold ofNatSat; rw [toNat_ofNatLe]

theorem ofNatSat_of_inRange {n : Nat} (h : InRange hi n) : (ofNatSat hi n).toNat = n := by
  rw [toNat_ofNatSat]; exact Nat.min_eq_left h

/-! ### Distinguished values -/

/-- The largest value, `hi` itself. -/
def maxVal (hi : UInt64) : TopBoundedUInt64 hi := ⟨hi, uint64_le_iff.mpr (Nat.le_refl _)⟩

/-- The smallest value, `0`. -/
def minVal (hi : UInt64) : TopBoundedUInt64 hi :=
  ⟨0, by rw [uint64_le_iff]; simp⟩

@[simp] theorem toNat_maxVal : (maxVal hi).toNat = hi.toNat := rfl

@[simp] theorem toNat_minVal : (minVal hi).toNat = 0 := by
  show (0 : UInt64).toNat = 0
  simp

instance : Inhabited (TopBoundedUInt64 hi) := ⟨minVal hi⟩

theorem le_maxVal (a : TopBoundedUInt64 hi) : a.toNat ≤ (maxVal hi).toNat := toNat_le a

theorem minVal_le (a : TopBoundedUInt64 hi) : (minVal hi).toNat ≤ a.toNat := by
  rw [toNat_minVal]; exact Nat.zero_le _

/-! ### Order -/

instance : LE (TopBoundedUInt64 hi) := ⟨fun a b => a.toNat ≤ b.toNat⟩
instance : LT (TopBoundedUInt64 hi) := ⟨fun a b => a.toNat < b.toNat⟩

theorem le_def {a b : TopBoundedUInt64 hi} : a ≤ b ↔ a.toNat ≤ b.toNat := Iff.rfl
theorem lt_def {a b : TopBoundedUInt64 hi} : a < b ↔ a.toNat < b.toNat := Iff.rfl

instance (a b : TopBoundedUInt64 hi) : Decidable (a ≤ b) :=
  decidable_of_iff _ le_def.symm

instance (a b : TopBoundedUInt64 hi) : Decidable (a < b) :=
  decidable_of_iff _ lt_def.symm

theorem le_refl' (a : TopBoundedUInt64 hi) : a ≤ a := Nat.le_refl _

theorem le_trans' {a b c : TopBoundedUInt64 hi} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  Nat.le_trans h₁ h₂

theorem le_antisymm' {a b : TopBoundedUInt64 hi} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b :=
  ext (Nat.le_antisymm h₁ h₂)

theorem le_total' (a b : TopBoundedUInt64 hi) : a ≤ b ∨ b ≤ a := Nat.le_total _ _

end TopBoundedUInt64
