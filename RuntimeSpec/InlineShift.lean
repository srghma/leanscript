module

public import RuntimeSpec.Model

@[expose] public section

set_option autoImplicit false

/-!
# The 32-bit shifts written inline

`runtime.js` computes `UInt32.shiftRight` as `a >>> (b % 32)`, `Int32.shiftRight` as
`a >> (((b % 32) + 32) % 32)` and `Int32.shiftLeft` as `(a << (((b % 32) + 32) % 32)) | 0`.  The
backend writes them inline instead (`scripts/js_ops_inline.json`), as the bare operators
`a >>> b`, `a >> b` and `a << b`: JavaScript already takes the shift count as `ToUint32(b) & 31`,
which is Lean's count (`b % 32` for `UInt32`, `b.toBitVec.smod 32` for `Int32`), and `<<` already
answers a signed 32-bit integer.  These theorems prove it in the model of `RuntimeSpec.Model`
(`ushr`, `sar`, `shl` are `>>>`, `>>`, `<<`) on every argument of the representation (a `uint32`
is a `UInt32`'s `toNat`, an `int32` an `Int32`'s `toInt`).

`UInt32.shiftLeft` is written `(a << b) >>> 0` (`uint32_shift_left_inline`); the shifts of
`UInt64` are below.  The other widths keep their functions: an 8- or 16-bit shift count is taken
modulo 8 or 16, which JavaScript's mask by 31 does not do.
-/

namespace RuntimeSpec

private theorem toI32_natCast' (n : Nat) : toI32 n = BitVec.ofNat 32 n := BitVec.ofInt_natCast 32 n

/-- `a >>> b` is `UInt32.shiftRight`. -/
theorem uint32_shift_right_inline (a b : UInt32) :
    ushr a.toNat b.toNat = ((a >>> b).toNat : Int) := by
  simp [ushr, shiftCount, toI32_natCast', UInt32.toNat_shiftRight]

private theorem smod32_toNat (b : Int32) :
    (b.toBitVec.smod 32).toNat = b.toBitVec.toNat % 32 := by
  have h1 : (b.toBitVec.smod 32).toInt = b.toInt % 32 := by
    rw [BitVec.toInt_smod, Int.fmod_eq_emod_of_nonneg _ (by decide), Int32.toInt_toBitVec]
    rfl
  have h2 := BitVec.toInt_eq_toNat_cond (b.toBitVec.smod 32)
  have h3 := (b.toBitVec.smod 32).isLt
  have h4 := BitVec.toInt_eq_toNat_cond b.toBitVec
  rw [Int32.toInt_toBitVec] at h4
  rw [h1] at h2
  split at h2 <;> split at h4 <;> omega

private theorem shiftCount_int32 (b : Int32) : shiftCount b.toInt = b.toBitVec.toNat % 32 := by
  simp only [shiftCount, toI32, ← Int32.toInt_toBitVec, BitVec.ofInt_toInt]

private theorem toI32_int32 (a : Int32) : toI32 a.toInt = a.toBitVec := by
  simp only [toI32, ← Int32.toInt_toBitVec, BitVec.ofInt_toInt]

/-- `a >> b` is `Int32.shiftRight`. -/
theorem int32_shift_right_inline (a b : Int32) :
    sar a.toInt b.toInt = (a >>> b).toInt := by
  rw [sar, toI32_int32, shiftCount_int32, ← Int32.toInt_toBitVec, Int32.toBitVec_shiftRight,
    BitVec.sshiftRight_eq', smod32_toNat]

/-- `a << b` is `Int32.shiftLeft`. -/
theorem int32_shift_left_inline (a b : Int32) :
    shl a.toInt b.toInt = (a <<< b).toInt := by
  rw [shl, toI32_int32, shiftCount_int32, ← Int32.toInt_toBitVec, Int32.toBitVec_shiftLeft,
    BitVec.shiftLeft_eq', smod32_toNat]

/-! ## The left shift of `UInt32`, and the shifts of `UInt64`

`(a << b) >>> 0` is `UInt32.shiftLeft`: `<<` takes the count modulo 32 (Lean's), and `>>> 0`
reads the 32 bits back unsigned.  At the `BigInt` representation the shifts of `UInt64` are
`BigInt.asUintN(64, a << (b & 63n))` and `a >> (b & 63n)` (`b & 63n` is `b % 64`), `UInt64.ofNat`
is `BigInt.asUintN(64, a)`, and the right shift of `Nat` at the `number` representation is
`Math.floor(a / 2 ** b)`.  A `BigInt` is modelled by its value: `<<`, `>>` and `&` on
non-negative `BigInt`s are those of `Nat`.

`JsTerm.Lower.Shift` drops the mask of the count under the test `b < 64` (the reading of a shift
of `BitVec 64`, `LeanScript.Gen.bitvec64_shiftLeft`), and drops the test of a right shift
altogether (`uint64_shift_right_guarded`), and does the same for a literal count below `64`
(`uint64_shift_right_lit`, `uint64_shift_left_lit`).
-/

private theorem toI32_uint32' (a : UInt32) : toI32 (a.toNat : Int) = a.toBitVec := by
  rw [toI32, BitVec.ofInt_natCast]; simp

/-- `(a << b) >>> 0` is `UInt32.shiftLeft`. -/
theorem uint32_shift_left_inline (a b : UInt32) :
    ushr (shl a.toNat b.toNat) 0 = ((a <<< b).toNat : Int) := by
  have hc : shiftCount (b.toNat : Int) = b.toNat % 32 := by
    simp [shiftCount, toI32_uint32']
  simp only [ushr, shl, hc, BitVec.ofInt_toInt, toI32, shiftCount]
  rw [← toI32, toI32_uint32']
  simp [UInt32.toNat_shiftLeft, BitVec.toNat_shiftLeft]

private theorem and63 (n : Nat) : n &&& 63 = n % 64 := by
  have := Nat.and_two_pow_sub_one_eq_mod n 6; simpa using this

/-- `BigInt.asUintN(64, a << (b & 63n))` is `UInt64.shiftLeft`. -/
theorem uint64_shift_left_inline (a b : UInt64) :
    asUintN 64 ((a.toNat <<< (b.toNat &&& 63) : Nat) : Int) = ((a <<< b).toNat : Int) := by
  rw [asUintN, and63, UInt64.toNat_shiftLeft]; simp

/-- `a >> (b & 63n)` is `UInt64.shiftRight`. -/
theorem uint64_shift_right_inline (a b : UInt64) :
    a.toNat >>> (b.toNat &&& 63) = (a >>> b).toNat := by
  rw [and63, UInt64.toNat_shiftRight]

/-- `BigInt.asUintN(64, a)` is `UInt64.ofNat`. -/
theorem uint64_of_nat_inline (n : Nat) : asUintN 64 (n : Int) = ((UInt64.ofNat n).toNat : Int) := by
  rw [asUintN]; simp [UInt64.toNat_ofNat']

/-- `Math.floor(a / 2 ** b)` (modelled by the floored quotient) is `Nat.shiftRight`. -/
theorem uint53_nat_shiftr_inline (a b : Nat) : (a : Int).fdiv (2 ^ b : Nat) = ((a >>> b : Nat) : Int) := by
  rw [Nat.shiftRight_eq_div_pow, Int.fdiv_eq_ediv_of_nonneg _ (Int.natCast_nonneg _)]; simp

/-- `b < 64 ? a >>> b : 0` (the shift of `UInt64`, count modulo 64) is `a >> b`: a right shift
    of a value below `2 ^ 64` by `64` or more is `0`. -/
theorem uint64_shift_right_guarded (a b : UInt64) :
    (if b < 64 then (a >>> b).toNat else 0) = a.toNat >>> b.toNat := by
  split
  · rename_i h
    have h' : b.toNat < 64 := by simpa [UInt64.lt_iff_toNat_lt] using h
    rw [UInt64.toNat_shiftRight]; simp [Nat.mod_eq_of_lt h']
  · rename_i h
    have h' : 64 ≤ b.toNat := by simp [UInt64.lt_iff_toNat_lt] at h; omega
    have ha := a.toNat_lt
    rw [Nat.shiftRight_eq_div_pow]
    symm; apply Nat.div_eq_of_lt
    exact Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) h')

/-- Under `b < 64`, the shift of `UInt64` is `BigInt.asUintN(64, a << b)`, without the mask. -/
theorem uint64_shift_left_guarded (a b : UInt64) (h : b < 64) :
    ((a <<< b).toNat : Int) = asUintN 64 ((a.toNat <<< b.toNat : Nat) : Int) := by
  have h' : b.toNat < 64 := by simpa [UInt64.lt_iff_toNat_lt] using h
  rw [asUintN, UInt64.toNat_shiftLeft]; simp [Nat.mod_eq_of_lt h']

/-- A right shift of `UInt64` by a literal count `k < 64` is `a >> k`. -/
theorem uint64_shift_right_lit (a : UInt64) (k : Nat) (h : k < 64) :
    (a >>> UInt64.ofNat k).toNat = a.toNat >>> k := by
  have hk : (UInt64.ofNat k).toNat = k := by simp [UInt64.toNat_ofNat']; omega
  rw [UInt64.toNat_shiftRight, hk, Nat.mod_eq_of_lt h]

/-- A left shift of `UInt64` by a literal count `k < 64` is `BigInt.asUintN(64, a << k)`. -/
theorem uint64_shift_left_lit (a : UInt64) (k : Nat) (h : k < 64) :
    ((a <<< UInt64.ofNat k).toNat : Int) = asUintN 64 ((a.toNat <<< k : Nat) : Int) := by
  have hk : (UInt64.ofNat k).toNat = k := by simp [UInt64.toNat_ofNat']; omega
  rw [asUintN, UInt64.toNat_shiftLeft, hk, Nat.mod_eq_of_lt h]; simp

end RuntimeSpec
