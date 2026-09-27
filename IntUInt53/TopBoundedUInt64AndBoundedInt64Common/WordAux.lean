/-!
# Auxiliary facts about the machine words `UInt64` and `Int64`

`TopBoundedUInt64` stores its value in a `UInt64` and `BoundedInt64` stores its
value in an `Int64`.  Both developments therefore need the same small set of
facts saying that the round trip `Nat → UInt64 → Nat` (respectively
`Int → Int64 → Int`) is the identity on values that fit in the machine word.
Those facts are collected here so that they are stated and proved once.

Only the Lean core library is used; there is no Mathlib dependency.
-/

set_option autoImplicit false

namespace BoundedWordAux

/-- Converting a `UInt64` to a `Nat` yields a number below `2 ^ 64`. -/
theorem toNat_lt (a : UInt64) : a.toNat < 2 ^ 64 := UInt64.toNat_lt a

/-- The round trip `Nat → UInt64 → Nat` is the identity below `2 ^ 64`. -/
theorem toNat_ofNat_of_lt {n : Nat} (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n := by
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

/-- Comparison of `UInt64`s is comparison of the natural numbers they denote. -/
theorem uint64_le_iff {a b : UInt64} : a ≤ b ↔ a.toNat ≤ b.toNat := UInt64.le_iff_toNat_le

/-- `UInt64`s that denote the same natural number are equal. -/
theorem uint64_eq_of_toNat_eq {a b : UInt64} (h : a.toNat = b.toNat) : a = b :=
  UInt64.toNat_inj.mp h

/-- Every `Int64` denotes an integer in `[-2 ^ 63, 2 ^ 63)`. -/
theorem neg_two_pow_63_le_toInt (a : Int64) : -2 ^ 63 ≤ a.toInt := Int64.le_toInt a

theorem toInt_lt_two_pow_63 (a : Int64) : a.toInt < 2 ^ 63 := Int64.toInt_lt a

/-- The round trip `Int → Int64 → Int` is the identity on `[-2 ^ 63, 2 ^ 63)`. -/
theorem toInt_ofInt_of_mem {n : Int} (h₁ : -2 ^ 63 ≤ n) (h₂ : n < 2 ^ 63) :
    (Int64.ofInt n).toInt = n := by
  rw [Int64.toInt_ofInt]
  have hsize : Int64.size = 2 ^ 64 := rfl
  rw [hsize]
  exact Int.bmod_eq_of_le h₁ h₂

/-- Comparison of `Int64`s is comparison of the integers they denote. -/
theorem int64_le_iff {a b : Int64} : a ≤ b ↔ a.toInt ≤ b.toInt := Int64.le_iff_toInt_le

theorem int64_lt_iff {a b : Int64} : a < b ↔ a.toInt < b.toInt := Int64.lt_iff_toInt_lt

/-- `Int64`s that denote the same integer are equal. -/
theorem int64_eq_of_toInt_eq {a b : Int64} (h : a.toInt = b.toInt) : a = b :=
  Int64.toInt_inj.mp h

end BoundedWordAux
