import IntUInt53.UInt53
import IntUInt53.Int53

/-!
# Converting between `UInt53` and `Int53`

`UInt53` denotes `[0, 9007199254740991]` and `Int53` denotes
`[-9007199254740991, 9007199254740991]`, so every `UInt53` is an `Int53` and an
`Int53` is a `UInt53` exactly when it is nonnegative.  Both conversions are
proved to preserve the denoted number, and the round trip is the identity.
-/

set_option autoImplicit false

namespace UInt53

/-- Every `UInt53` is an `Int53`. -/
def toInt53 (a : UInt53) : Int53 :=
  Int53.ofInt (a.toNat : Int)
    (by have := le_MAX a; unfold MAX at this; unfold Int53.MIN; omega)
    (by have := le_MAX a; unfold MAX at this; unfold Int53.MAX; omega)

/-- The conversion preserves the denoted number. -/
@[simp] theorem toInt_toInt53 (a : UInt53) : (toInt53 a).toInt = (a.toNat : Int) := by
  unfold toInt53; rw [Int53.toInt_ofInt]

end UInt53

namespace Int53

/-- An `Int53` is a `UInt53` exactly when it is nonnegative. -/
def toUInt53? (a : Int53) : Option UInt53 :=
  if h : 0 ≤ a.toInt then
    some (UInt53.ofNat a.toInt.toNat
      (by have := le_MAX a; unfold MAX at this; unfold UInt53.MAX; omega))
  else none

theorem toUInt53?_eq_none_iff {a : Int53} : toUInt53? a = none ↔ a.toInt < 0 := by
  unfold toUInt53?
  split <;> simp_all

/-- The conversion preserves the denoted number. -/
theorem toNat_of_toUInt53? {a : Int53} {b : UInt53} (h : toUInt53? a = some b) :
    (b.toNat : Int) = a.toInt := by
  unfold toUInt53? at h
  split at h
  · next hnn =>
    rw [← Option.some.inj h, UInt53.toNat_ofNat]
    omega
  · exact absurd h (by simp)

end Int53

namespace UInt53

/-- The round trip `UInt53 → Int53 → UInt53` is the identity. -/
theorem toUInt53?_toInt53 (a : UInt53) : Int53.toUInt53? (toInt53 a) = some a := by
  unfold Int53.toUInt53?
  rw [dite_eq_left (by rw [toInt_toInt53]; omega)]
  apply congrArg some
  apply TopBoundedUInt64.ext
  rw [UInt53.toNat_ofNat, toInt_toInt53]
  omega

end UInt53
