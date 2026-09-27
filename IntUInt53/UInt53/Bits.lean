import IntUInt53.UInt53.Div
import IntUInt53.UInt53.Mul
import Aesop

/-!
# Shifts and bitwise operations on `UInt53`

`UInt53` denotes exactly the natural numbers below `2 ^ 53`, so the bitwise
operations of `Nat` restrict to it:

* `land`, `lor`, `lxor` are **total** — the result of a bitwise operation on
  two numbers below `2 ^ 53` is again below `2 ^ 53`;
* `shiftRight a k = a / 2 ^ k` is total as well;
* `shiftLeft a k = a * 2 ^ k` can leave the range, so it comes in the usual
  four variants;
* `testBit`, `setBit` and `clearBit` inspect and change one bit.

Each operation is specified by the natural number it denotes, so everything
below is exact arithmetic on `Nat`.
-/

set_option autoImplicit false

open TopBoundedUInt64

namespace UInt53

theorem lt_two_pow_53 (a : UInt53) : a.toNat < 2 ^ 53 := by
  have := le_MAX a
  unfold MAX at this
  omega

theorem le_MAX_of_lt_two_pow_53 {n : Nat} (h : n < 2 ^ 53) : n ≤ MAX := by
  unfold MAX; omega

/-! ### Bitwise operations -/

/-- Bitwise and.  Total: the result is at most either argument. -/
def land (a b : UInt53) : UInt53 :=
  TopBoundedUInt64.ofNatLe _ (a.toNat &&& b.toNat)
    (le_MAX_of_lt_two_pow_53 (Nat.and_lt_two_pow _ (lt_two_pow_53 b)))

/-- Bitwise or.  Total: both arguments are below `2 ^ 53`, hence so is the result. -/
def lor (a b : UInt53) : UInt53 :=
  TopBoundedUInt64.ofNatLe _ (a.toNat ||| b.toNat)
    (le_MAX_of_lt_two_pow_53 (Nat.or_lt_two_pow (lt_two_pow_53 a) (lt_two_pow_53 b)))

/-- Bitwise exclusive or.  Total for the same reason. -/
def lxor (a b : UInt53) : UInt53 :=
  TopBoundedUInt64.ofNatLe _ (a.toNat ^^^ b.toNat)
    (le_MAX_of_lt_two_pow_53 (Nat.xor_lt_two_pow (lt_two_pow_53 a) (lt_two_pow_53 b)))

@[simp] theorem toNat_land (a b : UInt53) : (land a b).toNat = a.toNat &&& b.toNat := by
  unfold land; exact toNat_ofNatLe (toNat a &&& toNat b) (land._proof_1 _ b)

@[simp] theorem toNat_lor (a b : UInt53) : (lor a b).toNat = a.toNat ||| b.toNat := by
  unfold lor; exact toNat_ofNatLe (toNat a ||| toNat b) (lor._proof_1 _ b)

@[simp] theorem toNat_lxor (a b : UInt53) : (lxor a b).toNat = a.toNat ^^^ b.toNat := by
  unfold lxor; exact toNat_ofNatLe (toNat a ^^^ toNat b) (lxor._proof_1 _ b)

theorem land_comm (a b : UInt53) : land a b = land b a :=
  TopBoundedUInt64.ext (by rw [toNat_land, toNat_land, Nat.and_comm])

theorem lor_comm (a b : UInt53) : lor a b = lor b a :=
  TopBoundedUInt64.ext (by rw [toNat_lor, toNat_lor, Nat.or_comm])

theorem lxor_comm (a b : UInt53) : lxor a b = lxor b a :=
  TopBoundedUInt64.ext (by rw [toNat_lxor, toNat_lxor, Nat.xor_comm])

theorem lxor_self (a : UInt53) : lxor a a = minVal :=
  TopBoundedUInt64.ext (by rw [toNat_lxor, toNat_minVal, Nat.xor_self]; rfl)

theorem land_self (a : UInt53) : land a a = a :=
  TopBoundedUInt64.ext (by rw [toNat_land, Nat.and_self])

theorem lor_self (a : UInt53) : lor a a = a :=
  TopBoundedUInt64.ext (by rw [toNat_lor, Nat.or_self])

theorem toNat_land_le_left (a b : UInt53) : (land a b).toNat ≤ a.toNat := by
  rw [toNat_land]; exact Nat.and_le_left

/-! ### The right shift -/

/-- The right shift `a >>> k`, i.e. division by `2 ^ k`.  Total: the result is
at most `a`. -/
def shiftRight (a : UInt53) (k : Nat) : UInt53 :=
  TopBoundedUInt64.ofNatLe _ (a.toNat >>> k) (by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.le_trans (Nat.div_le_self _ _) (le_MAX a))

@[simp] theorem toNat_shiftRight (a : UInt53) (k : Nat) :
    (shiftRight a k).toNat = a.toNat / 2 ^ k := by
  unfold shiftRight
  rw [TopBoundedUInt64.toNat_ofNatLe, Nat.shiftRight_eq_div_pow]

/-! ### The left shift, in four variants -/

/-- The exact value of the left shift `a <<< k`, namely `a * 2 ^ k`. -/
def exactShiftLeft (a : UInt53) (k : Nat) : Nat := a.toNat * 2 ^ k

/-- The left shift overflows when `a * 2 ^ k` exceeds `MAX`. -/
def shiftLeftOverflows (a : UInt53) (k : Nat) : Prop := MAX < exactShiftLeft a k

instance (a : UInt53) (k : Nat) : Decidable (shiftLeftOverflows a k) := by
  unfold shiftLeftOverflows; infer_instance

/-- Checked left shift: `none` when the exact value does not fit. -/
def checked_shiftLeft (a : UInt53) (k : Nat) : Option UInt53 :=
  ofNat? (exactShiftLeft a k)

/-- Wrapping left shift: the exact value reduced modulo `SIZE`. -/
def wrapping_shiftLeft (a : UInt53) (k : Nat) : UInt53 :=
  ofNatWrap (exactShiftLeft a k)

/-- Overflowing left shift: the wrapped value together with a flag. -/
def overflowing_shiftLeft (a : UInt53) (k : Nat) : UInt53 × Bool :=
  (wrapping_shiftLeft a k, decide (MAX < exactShiftLeft a k))

/-- Saturating left shift: the exact value, clamped at `MAX`. -/
def saturating_shiftLeft (a : UInt53) (k : Nat) : UInt53 :=
  ofNatSat (exactShiftLeft a k)

theorem checked_shiftLeft_eq_some_iff {a : UInt53} {k : Nat} {c : UInt53} :
    checked_shiftLeft a k = some c ↔ c.toNat = a.toNat * 2 ^ k :=
  ofNat?_eq_some_iff

theorem checked_shiftLeft_eq_none_iff {a : UInt53} {k : Nat} :
    checked_shiftLeft a k = none ↔ MAX < a.toNat * 2 ^ k := ofNat?_eq_none_iff

@[simp] theorem toNat_wrapping_shiftLeft (a : UInt53) (k : Nat) :
    (wrapping_shiftLeft a k).toNat = (a.toNat * 2 ^ k) % SIZE := by
  unfold wrapping_shiftLeft exactShiftLeft; rw [toNat_ofNatWrap]

@[simp] theorem toNat_saturating_shiftLeft (a : UInt53) (k : Nat) :
    (saturating_shiftLeft a k).toNat = min (a.toNat * 2 ^ k) MAX := by
  unfold saturating_shiftLeft exactShiftLeft; rw [toNat_ofNatSat]

theorem overflowing_shiftLeft_snd_iff {a : UInt53} {k : Nat} :
    (overflowing_shiftLeft a k).2 = true ↔ MAX < a.toNat * 2 ^ k := by
  unfold overflowing_shiftLeft exactShiftLeft; simp

/-- **All four variants of the left shift are exact** whenever `a * 2 ^ k` is
representable. -/
theorem shiftLeft_variants_exact {a : UInt53} {k : Nat} (h : a.toNat * 2 ^ k ≤ MAX) :
    (∃ c, checked_shiftLeft a k = some c ∧ c.toNat = a.toNat * 2 ^ k) ∧
      (wrapping_shiftLeft a k).toNat = a.toNat * 2 ^ k ∧
      (overflowing_shiftLeft a k).1.toNat = a.toNat * 2 ^ k ∧
      (overflowing_shiftLeft a k).2 = false ∧
      (saturating_shiftLeft a k).toNat = a.toNat * 2 ^ k := by
  have hwrap : (wrapping_shiftLeft a k).toNat = a.toNat * 2 ^ k := by
    rw [toNat_wrapping_shiftLeft]
    exact Nat.mod_eq_of_lt (by unfold MAX at h; rw [SIZE_eq]; omega)
  refine ⟨⟨ofNat (a.toNat * 2 ^ k) h, ?_, by rw [toNat_ofNat]⟩, hwrap, hwrap, ?_, ?_⟩
  · exact ofNat?_eq_some_iff.mpr (by rw [toNat_ofNat]; rfl)
  · cases hb : (overflowing_shiftLeft a k).2 with
    | false => rfl
    | true =>
      have := overflowing_shiftLeft_snd_iff.mp hb
      omega
  · rw [toNat_saturating_shiftLeft]
    exact Nat.min_eq_left h

/-- Shifting left and back right recovers the value when nothing overflowed. -/
theorem shiftRight_wrapping_shiftLeft {a : UInt53} {k : Nat} (h : a.toNat * 2 ^ k ≤ MAX) :
    shiftRight (wrapping_shiftLeft a k) k = a := by
  apply TopBoundedUInt64.ext
  rw [toNat_shiftRight, (shiftLeft_variants_exact h).2.1,
    Nat.mul_div_cancel _ (Nat.two_pow_pos k)]

/-! ### Individual bits -/

/-- The `i`-th bit of the value. -/
def testBit (a : UInt53) (i : Nat) : Bool := a.toNat.testBit i

/-- Set the `i`-th bit; for `i < 53` the result is still in range. -/
def setBit (a : UInt53) (i : Nat) (h : i < 53 := by decide) : UInt53 :=
  lor a (ofNat (2 ^ i) (by
    have : (2 : Nat) ^ i < 2 ^ 53 := Nat.pow_lt_pow_right (by decide) h
    exact le_MAX_of_lt_two_pow_53 this))

@[simp] theorem toNat_setBit (a : UInt53) (i : Nat) (h : i < 53) :
    (setBit a i h).toNat = a.toNat ||| 2 ^ i := by
  unfold setBit
  rw [toNat_lor, toNat_ofNat]

/-- Setting a bit makes it set. -/
theorem testBit_setBit (a : UInt53) (i : Nat) (h : i < 53) :
    testBit (setBit a i h) i = true := by
  unfold testBit
  rw [toNat_setBit]
  simp [Nat.testBit_or, Nat.testBit_two_pow_self]

/-! ### Exact arithmetic, concretely -/

/-- `1 <<< 52` is exactly `4503599627370496`. -/
theorem checked_shiftLeft_one_52 :
    checked_shiftLeft (ofNat 1) 52 = some (ofNat 4503599627370496) := by decide

/-- `1 <<< 53` does not fit in a `UInt53` and is reported. -/
theorem checked_shiftLeft_one_53 : checked_shiftLeft (ofNat 1) 53 = none := by decide

/-- `12 >>> 2 = 3`. -/
theorem shiftRight_twelve_two : shiftRight (ofNat 12) 2 = ofNat 3 := by decide

/-- `12 &&& 10 = 8`. -/
theorem land_twelve_ten : land (ofNat 12) (ofNat 10) = ofNat 8 := by decide

/-- `12 ||| 10 = 14`. -/
theorem lor_twelve_ten : lor (ofNat 12) (ofNat 10) = ofNat 14 := by decide

/-- `12 ^^^ 10 = 6`. -/
theorem lxor_twelve_ten : lxor (ofNat 12) (ofNat 10) = ofNat 6 := by decide

end UInt53
