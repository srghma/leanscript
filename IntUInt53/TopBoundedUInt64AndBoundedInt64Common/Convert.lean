import IntUInt53.TopBoundedUInt64
import IntUInt53.BoundedInt64

/-!
# Converting between `TopBoundedUInt64` and `BoundedInt64`

An unsigned bounded value denotes a natural number and a signed one denotes an
integer, so whenever the two ranges match up the conversions in both directions
exist and preserve the denoted number.  That is the content of this file:

* `TopBoundedUInt64.toBoundedInt64` embeds `TopBoundedUInt64 hi` into
  `BoundedInt64 0 hiI` for a signed bound `hiI` denoting the same number;
* `BoundedInt64.toTopBoundedUInt64?` goes back, returning `none` exactly on the
  negative values.

Both are proved value preserving, which is what makes them safe to use: nothing
is rounded or truncated on the way.
-/

set_option autoImplicit false

open BoundedWordAux

namespace TopBoundedUInt64

variable {hi : UInt64} {hiI : Int64}

/-- Embed an unsigned bounded word into the signed bounded words of the same range. -/
def toBoundedInt64 (h : (hi.toNat : Int) = hiI.toInt) (a : TopBoundedUInt64 hi) :
    BoundedInt64 0 hiI :=
  BoundedInt64.ofIntMem 0 hiI (a.toNat : Int)
    (by
      have : ((0 : Int64)).toInt = 0 := rfl
      rw [this]
      exact Int.natCast_nonneg _)
    (by
      have := toNat_le a
      omega)

/-- The embedding preserves the denoted number. -/
@[simp] theorem toInt_toBoundedInt64 (h : (hi.toNat : Int) = hiI.toInt)
    (a : TopBoundedUInt64 hi) : (toBoundedInt64 h a).toInt = (a.toNat : Int) := by
  unfold toBoundedInt64; rw [BoundedInt64.toInt_ofIntMem]

end TopBoundedUInt64

namespace BoundedInt64

variable {lo hi : Int64} {hiU : UInt64}

/-- Convert a signed bounded word to an unsigned one, if it is nonnegative. -/
def toTopBoundedUInt64? (h : hi.toInt = (hiU.toNat : Int)) (a : BoundedInt64 lo hi) :
    Option (TopBoundedUInt64 hiU) :=
  if hnn : 0 ≤ a.toInt then
    some (TopBoundedUInt64.ofNatLe hiU a.toInt.toNat (by
      have h₂ := toInt_le_hi a
      omega))
  else none

/-- The conversion preserves the denoted number. -/
theorem toNat_of_toTopBoundedUInt64? (h : hi.toInt = (hiU.toNat : Int))
    {a : BoundedInt64 lo hi} {b : TopBoundedUInt64 hiU}
    (hb : toTopBoundedUInt64? h a = some b) : (b.toNat : Int) = a.toInt := by
  unfold toTopBoundedUInt64? at hb
  split at hb
  · next hnn =>
    rw [← Option.some.inj hb, TopBoundedUInt64.toNat_ofNatLe]
    omega
  · exact absurd hb (by simp)

/-- The conversion succeeds exactly on the nonnegative values. -/
theorem toTopBoundedUInt64?_eq_none_iff (h : hi.toInt = (hiU.toNat : Int))
    {a : BoundedInt64 lo hi} : toTopBoundedUInt64? h a = none ↔ a.toInt < 0 := by
  unfold toTopBoundedUInt64?
  split <;> simp_all

end BoundedInt64
