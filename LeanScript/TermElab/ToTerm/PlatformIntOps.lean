module

@[expose] public section

set_option autoImplicit false

/-!
# The operations of `USize` and `ISize`, as the translator reads them

`USize` is a structure around a `BitVec System.Platform.numBits`, and `ISize` one around a
`USize`.  The width `System.Platform.numBits` is not a numeral (it is `32` or `64`, whichever
platform runs the program), so the definitions of their operations (`USize.add a b` is
`⟨a.toBitVec + b.toBitVec⟩`) have no translation.

The translation (`platformIntOpCall?`, `platformIntDecide?`,
`LeanScript/TermElab/ToTerm/Expr/Calls.lean`) assumes a **64-bit platform**
(`System.Platform.numBits = 64`), as the compiled Lean that the checks compare against does on
this machine, and as the JavaScript of purescript-backend-optimizer does: a `USize` is
represented as a `UInt64` (the leaf `uint64`), an `ISize` as an `Int64` (`int64`), and the
conversions between them (`USize.toUInt64`, `UInt64.toUSize`, `ISize.toInt64`,
`Int64.toISize`) are the identity.  This is the only place where the platform is assumed.

Every operation is then read as the operation of the 64-bit type between those conversions,
and **each reading is proved equal to the original here, on every platform** (no assumption on
`numBits`): `USize.add a b` is `(a.toUInt64 + b.toUInt64).toUSize` (`usize_add`), and so on.
On a 64-bit platform the conversions are bijections inverse to each other, so the translated
term computes what the program does.
-/

namespace LeanScript.Gen

section
variable (a b : USize)

theorem usize_add : USize.add a b = (a.toUInt64 + b.toUInt64).toUSize := by
  rw [UInt64.toUSize_add, USize.toUSize_toUInt64, USize.toUSize_toUInt64]; rfl
theorem usize_sub : USize.sub a b = (a.toUInt64 - b.toUInt64).toUSize := by
  rw [UInt64.toUSize_sub, USize.toUSize_toUInt64, USize.toUSize_toUInt64]; rfl
theorem usize_mul : USize.mul a b = (a.toUInt64 * b.toUInt64).toUSize := by
  rw [UInt64.toUSize_mul, USize.toUSize_toUInt64, USize.toUSize_toUInt64]; rfl
theorem usize_div : USize.div a b = (a.toUInt64 / b.toUInt64).toUSize := by
  rw [← USize.toUInt64_div, USize.toUSize_toUInt64]; rfl
theorem usize_mod : USize.mod a b = (a.toUInt64 % b.toUInt64).toUSize := by
  rw [← USize.toUInt64_mod, USize.toUSize_toUInt64]; rfl
theorem usize_neg : USize.neg a = (-a.toUInt64).toUSize := by
  rw [UInt64.toUSize_neg, USize.toUSize_toUInt64]; rfl
theorem usize_land : USize.land a b = (a.toUInt64 &&& b.toUInt64).toUSize := by
  rw [← USize.toUInt64_and, USize.toUSize_toUInt64]; rfl
theorem usize_lor : USize.lor a b = (a.toUInt64 ||| b.toUInt64).toUSize := by
  rw [← USize.toUInt64_or, USize.toUSize_toUInt64]; rfl
theorem usize_xor : USize.xor a b = (a.toUInt64 ^^^ b.toUInt64).toUSize := by
  rw [← USize.toUInt64_xor, USize.toUSize_toUInt64]; rfl
theorem usize_complement : USize.complement a = (~~~a.toUInt64).toUSize := by
  apply USize.toNat_inj.1
  have h1 : (~~~a).toNat = 2 ^ System.Platform.numBits - 1 - a.toNat := USize.toNat_not a
  have h2 : (~~~a.toUInt64).toNat = 2 ^ 64 - 1 - a.toNat := by
    rw [UInt64.toNat_not, USize.toNat_toUInt64]
  have h3 := USize.toNat_lt_two_pow_numBits a
  have h4 : 2 ^ System.Platform.numBits ∣ 2 ^ 64 :=
    Nat.pow_dvd_pow 2 System.Platform.numBits_le
  have h5 : 0 < 2 ^ System.Platform.numBits := Nat.two_pow_pos _
  show (~~~a).toNat = _
  rw [h1, UInt64.toNat_toUSize, h2]
  obtain ⟨k, hk⟩ := h4
  rw [hk]
  have hk1 : 1 ≤ k := by
    rcases k with _ | k
    · simp at hk
    · omega
  have : 2 ^ System.Platform.numBits * k - 1 - a.toNat =
      (2 ^ System.Platform.numBits - 1 - a.toNat) + 2 ^ System.Platform.numBits * (k - 1) := by
    rw [Nat.mul_sub, Nat.mul_one]
    have : 2 ^ System.Platform.numBits ≤ 2 ^ System.Platform.numBits * k :=
      Nat.le_mul_of_pos_right _ hk1
    omega
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
theorem usize_ofNat (n : Nat) : USize.ofNat n = (UInt64.ofNat n).toUSize := by simp
theorem usize_toNat : USize.toNat a = a.toUInt64.toNat := by simp
theorem usize_toUInt8 : USize.toUInt8 a = a.toUInt64.toUInt8 := by simp
theorem usize_toUInt16 : USize.toUInt16 a = a.toUInt64.toUInt16 := by simp
theorem usize_toUInt32 : USize.toUInt32 a = a.toUInt64.toUInt32 := by simp
theorem uint8_toUSize (x : UInt8) : x.toUSize = x.toUInt64.toUSize := by
  apply USize.toNat_inj.1; simp
theorem uint16_toUSize (x : UInt16) : x.toUSize = x.toUInt64.toUSize := by
  apply USize.toNat_inj.1; simp
theorem uint32_toUSize (x : UInt32) : x.toUSize = x.toUInt64.toUSize := by
  apply USize.toNat_inj.1; simp
theorem usize_eq : decide (a = b) = decide (a.toUInt64 = b.toUInt64) := by
  simp [USize.toUInt64_inj]
theorem usize_lt : decide (a < b) = decide (a.toUInt64 < b.toUInt64) := by
  simp [USize.toUInt64_lt]
theorem usize_le : decide (a ≤ b) = decide (a.toUInt64 ≤ b.toUInt64) := by
  simp [USize.toUInt64_le]
end

section
variable (a b : ISize)

theorem isize_toInt64_inj {a b : ISize} : a.toInt64 = b.toInt64 ↔ a = b :=
  ⟨fun h => by rw [← ISize.toISize_toInt64 a, h, ISize.toISize_toInt64], fun h => h ▸ rfl⟩

/-- `2 ^ numBits` divides `2 ^ 64`: reducing modulo `2 ^ 64` first does not change a
    reduction modulo `2 ^ numBits`. -/
theorem two_pow_numBits_dvd : 2 ^ System.Platform.numBits ∣ 2 ^ 64 :=
  Nat.pow_dvd_pow 2 System.Platform.numBits_le

theorem isize_add : ISize.add a b = (a.toInt64 + b.toInt64).toISize := by
  rw [Int64.toISize_add, ISize.toISize_toInt64, ISize.toISize_toInt64]; rfl
theorem isize_sub : ISize.sub a b = (a.toInt64 - b.toInt64).toISize := by
  rw [Int64.toISize_sub, ISize.toISize_toInt64, ISize.toISize_toInt64]; rfl
theorem isize_mul : ISize.mul a b = (a.toInt64 * b.toInt64).toISize := by
  rw [Int64.toISize_mul, ISize.toISize_toInt64, ISize.toISize_toInt64]; rfl
theorem isize_neg : ISize.neg a = (-a.toInt64).toISize := by
  rw [Int64.toISize_neg, ISize.toISize_toInt64]; rfl
theorem isize_land : ISize.land a b = (a.toInt64 &&& b.toInt64).toISize := by
  rw [Int64.toISize_and, ISize.toISize_toInt64, ISize.toISize_toInt64]; rfl
theorem isize_lor : ISize.lor a b = (a.toInt64 ||| b.toInt64).toISize := by
  rw [Int64.toISize_or, ISize.toISize_toInt64, ISize.toISize_toInt64]; rfl
theorem isize_xor : ISize.xor a b = (a.toInt64 ^^^ b.toInt64).toISize := by
  rw [Int64.toISize_xor, ISize.toISize_toInt64, ISize.toISize_toInt64]; rfl
theorem isize_complement : ISize.complement a = (~~~a.toInt64).toISize := by
  rw [Int64.toISize_not, ISize.toISize_toInt64]; rfl
theorem isize_div : ISize.div a b = (a.toInt64 / b.toInt64).toISize := by
  apply ISize.toInt_inj.1
  show (a / b).toInt = _
  rw [ISize.toInt_div, Int64.toInt_toISize, Int64.toInt_div, ISize.toInt_toInt64,
    ISize.toInt_toInt64, Int.bmod_bmod_of_dvd two_pow_numBits_dvd]
theorem isize_mod : ISize.mod a b = (a.toInt64 % b.toInt64).toISize := by
  rw [← ISize.toInt64_mod, ISize.toISize_toInt64]; rfl
theorem isize_ofInt (i : Int) : ISize.ofInt i = (Int64.ofInt i).toISize := by simp
theorem isize_ofNat (n : Nat) : ISize.ofNat n = (Int64.ofNat n).toISize := by
  apply ISize.toInt_inj.1; simp
theorem isize_toInt : ISize.toInt a = a.toInt64.toInt := by simp
theorem isize_eq : decide (a = b) = decide (a.toInt64 = b.toInt64) := by
  simp [isize_toInt64_inj]
theorem isize_lt : decide (a < b) = decide (a.toInt64 < b.toInt64) := by
  simp [ISize.toInt64_lt]
theorem isize_le : decide (a ≤ b) = decide (a.toInt64 ≤ b.toInt64) := by
  simp [ISize.toInt64_le]
end

end LeanScript.Gen
