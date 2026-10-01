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

The other widths keep their functions: an 8- or 16-bit shift count is taken modulo 8 or 16,
which JavaScript's mask by 31 does not do.
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

end RuntimeSpec
