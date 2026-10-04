module

@[expose] public section

set_option autoImplicit false

/-!
# The operations of `BitVec w`, as the translator reads them

`BitVec w` is a leaf of the language: its values are literals, and the definitions of its
operations (`BitVec.add x y` is `.ofNat w (x.toNat + y.toNat)`, a projection of the leaf) have
no translation.  At the widths of the fixed-width unsigned integers (`8`, `16`, `32`, `64`) a
bit vector *is* that integer (`UInt32` is a structure around a `BitVec 32`, and the externs
`UInt32.ofBitVec`/`UInt32.toBitVec` are the identity in JavaScript), so `#leanscript_to_term`
(`trBitVecOp?`, `LeanScript/TermElab/ToTerm/Expr/Calls.lean`) translates

* an operation `f x y` of `BitVec w` (`+`, `-`, `*`, `/`, `%`, `-x`, `&&&`, `|||`, `^^^`, `~~~`)
  as `(g (UIntW.ofBitVec x) (UIntW.ofBitVec y)).toBitVec`, with `g` the operation of `UIntW`
  (an extern: `lean_uint32_add`, …), and
* a decision `x = y`, `x < y`, `x ≤ y` of `BitVec w` as the one of
  `UIntW.ofBitVec x` and `UIntW.ofBitVec y` (`lean_uint32_dec_eq`, …).

and (`bitvecShiftCall?`, `bitvecToNatCall?`)

* `x.toNat` as `(UIntW.ofBitVec x).toNat`;
* a shift `x <<< y`, `x >>> y` by a bit vector of the same width (`x <<< y.toNat`) as
  `if UIntW.ofBitVec y < w then (UIntW.ofBitVec x <<< UIntW.ofBitVec y).toBitVec else 0`: the
  shift of `UIntW` takes its count modulo `w`, the one of `BitVec w` answers `0` from `w` on;
* a shift by a natural number `n` as `if n < w then (UIntW.ofBitVec x <<< .ofNat n).toBitVec
  else 0`, and by a literal `k` as `(UIntW.ofBitVec x <<< k).toBitVec` when `k < w`, as `0`
  otherwise.

This file proves each of these readings equal to the original, at each width.
-/

namespace LeanScript.Gen

section
variable (x y : BitVec 8)
theorem bitvec8_add : x + y = (UInt8.ofBitVec x + UInt8.ofBitVec y).toBitVec := rfl
theorem bitvec8_sub : x - y = (UInt8.ofBitVec x - UInt8.ofBitVec y).toBitVec := rfl
theorem bitvec8_mul : x * y = (UInt8.ofBitVec x * UInt8.ofBitVec y).toBitVec := rfl
theorem bitvec8_div : x / y = (UInt8.ofBitVec x / UInt8.ofBitVec y).toBitVec := rfl
theorem bitvec8_mod : x % y = (UInt8.ofBitVec x % UInt8.ofBitVec y).toBitVec := rfl
theorem bitvec8_neg : -x = (-UInt8.ofBitVec x).toBitVec := rfl
theorem bitvec8_and : (x &&& y) = (UInt8.ofBitVec x &&& UInt8.ofBitVec y).toBitVec := rfl
theorem bitvec8_or : (x ||| y) = (UInt8.ofBitVec x ||| UInt8.ofBitVec y).toBitVec := rfl
theorem bitvec8_xor : (x ^^^ y) = (UInt8.ofBitVec x ^^^ UInt8.ofBitVec y).toBitVec := rfl
theorem bitvec8_not : (~~~x) = (~~~UInt8.ofBitVec x).toBitVec := rfl
theorem bitvec8_lt : decide (x < y) = decide (UInt8.ofBitVec x < UInt8.ofBitVec y) := rfl
theorem bitvec8_le : decide (x ≤ y) = decide (UInt8.ofBitVec x ≤ UInt8.ofBitVec y) := rfl
theorem bitvec8_eq : decide (x = y) = decide (UInt8.ofBitVec x = UInt8.ofBitVec y) := by
  congr 1; apply propext; constructor
  · intro h; rw [h]
  · intro h; exact congrArg UInt8.toBitVec h
theorem bitvec8_beq : (x == y) = decide (UInt8.ofBitVec x = UInt8.ofBitVec y) := by
  rw [← bitvec8_eq]; rfl
end

section
variable (x y : BitVec 16)
theorem bitvec16_add : x + y = (UInt16.ofBitVec x + UInt16.ofBitVec y).toBitVec := rfl
theorem bitvec16_sub : x - y = (UInt16.ofBitVec x - UInt16.ofBitVec y).toBitVec := rfl
theorem bitvec16_mul : x * y = (UInt16.ofBitVec x * UInt16.ofBitVec y).toBitVec := rfl
theorem bitvec16_div : x / y = (UInt16.ofBitVec x / UInt16.ofBitVec y).toBitVec := rfl
theorem bitvec16_mod : x % y = (UInt16.ofBitVec x % UInt16.ofBitVec y).toBitVec := rfl
theorem bitvec16_neg : -x = (-UInt16.ofBitVec x).toBitVec := rfl
theorem bitvec16_and : (x &&& y) = (UInt16.ofBitVec x &&& UInt16.ofBitVec y).toBitVec := rfl
theorem bitvec16_or : (x ||| y) = (UInt16.ofBitVec x ||| UInt16.ofBitVec y).toBitVec := rfl
theorem bitvec16_xor : (x ^^^ y) = (UInt16.ofBitVec x ^^^ UInt16.ofBitVec y).toBitVec := rfl
theorem bitvec16_not : (~~~x) = (~~~UInt16.ofBitVec x).toBitVec := rfl
theorem bitvec16_lt : decide (x < y) = decide (UInt16.ofBitVec x < UInt16.ofBitVec y) := rfl
theorem bitvec16_le : decide (x ≤ y) = decide (UInt16.ofBitVec x ≤ UInt16.ofBitVec y) := rfl
theorem bitvec16_eq : decide (x = y) = decide (UInt16.ofBitVec x = UInt16.ofBitVec y) := by
  congr 1; apply propext; constructor
  · intro h; rw [h]
  · intro h; exact congrArg UInt16.toBitVec h
theorem bitvec16_beq : (x == y) = decide (UInt16.ofBitVec x = UInt16.ofBitVec y) := by
  rw [← bitvec16_eq]; rfl
end

section
variable (x y : BitVec 32)
theorem bitvec32_add : x + y = (UInt32.ofBitVec x + UInt32.ofBitVec y).toBitVec := rfl
theorem bitvec32_sub : x - y = (UInt32.ofBitVec x - UInt32.ofBitVec y).toBitVec := rfl
theorem bitvec32_mul : x * y = (UInt32.ofBitVec x * UInt32.ofBitVec y).toBitVec := rfl
theorem bitvec32_div : x / y = (UInt32.ofBitVec x / UInt32.ofBitVec y).toBitVec := rfl
theorem bitvec32_mod : x % y = (UInt32.ofBitVec x % UInt32.ofBitVec y).toBitVec := rfl
theorem bitvec32_neg : -x = (-UInt32.ofBitVec x).toBitVec := rfl
theorem bitvec32_and : (x &&& y) = (UInt32.ofBitVec x &&& UInt32.ofBitVec y).toBitVec := rfl
theorem bitvec32_or : (x ||| y) = (UInt32.ofBitVec x ||| UInt32.ofBitVec y).toBitVec := rfl
theorem bitvec32_xor : (x ^^^ y) = (UInt32.ofBitVec x ^^^ UInt32.ofBitVec y).toBitVec := rfl
theorem bitvec32_not : (~~~x) = (~~~UInt32.ofBitVec x).toBitVec := rfl
theorem bitvec32_lt : decide (x < y) = decide (UInt32.ofBitVec x < UInt32.ofBitVec y) := rfl
theorem bitvec32_le : decide (x ≤ y) = decide (UInt32.ofBitVec x ≤ UInt32.ofBitVec y) := rfl
theorem bitvec32_eq : decide (x = y) = decide (UInt32.ofBitVec x = UInt32.ofBitVec y) := by
  congr 1; apply propext; constructor
  · intro h; rw [h]
  · intro h; exact congrArg UInt32.toBitVec h
theorem bitvec32_beq : (x == y) = decide (UInt32.ofBitVec x = UInt32.ofBitVec y) := by
  rw [← bitvec32_eq]; rfl
end

section
variable (x y : BitVec 64)
theorem bitvec64_add : x + y = (UInt64.ofBitVec x + UInt64.ofBitVec y).toBitVec := rfl
theorem bitvec64_sub : x - y = (UInt64.ofBitVec x - UInt64.ofBitVec y).toBitVec := rfl
theorem bitvec64_mul : x * y = (UInt64.ofBitVec x * UInt64.ofBitVec y).toBitVec := rfl
theorem bitvec64_div : x / y = (UInt64.ofBitVec x / UInt64.ofBitVec y).toBitVec := rfl
theorem bitvec64_mod : x % y = (UInt64.ofBitVec x % UInt64.ofBitVec y).toBitVec := rfl
theorem bitvec64_neg : -x = (-UInt64.ofBitVec x).toBitVec := rfl
theorem bitvec64_and : (x &&& y) = (UInt64.ofBitVec x &&& UInt64.ofBitVec y).toBitVec := rfl
theorem bitvec64_or : (x ||| y) = (UInt64.ofBitVec x ||| UInt64.ofBitVec y).toBitVec := rfl
theorem bitvec64_xor : (x ^^^ y) = (UInt64.ofBitVec x ^^^ UInt64.ofBitVec y).toBitVec := rfl
theorem bitvec64_not : (~~~x) = (~~~UInt64.ofBitVec x).toBitVec := rfl
theorem bitvec64_lt : decide (x < y) = decide (UInt64.ofBitVec x < UInt64.ofBitVec y) := rfl
theorem bitvec64_le : decide (x ≤ y) = decide (UInt64.ofBitVec x ≤ UInt64.ofBitVec y) := rfl
theorem bitvec64_eq : decide (x = y) = decide (UInt64.ofBitVec x = UInt64.ofBitVec y) := by
  congr 1; apply propext; constructor
  · intro h; rw [h]
  · intro h; exact congrArg UInt64.toBitVec h
theorem bitvec64_beq : (x == y) = decide (UInt64.ofBitVec x = UInt64.ofBitVec y) := by
  rw [← bitvec64_eq]; rfl
end

section
variable (x y : BitVec 8) (n : Nat)
theorem bitvec8_toNat : x.toNat = (UInt8.ofBitVec x).toNat := rfl
theorem bitvec8_shiftLeft :
    x <<< y = if UInt8.ofBitVec y < 8 then (UInt8.ofBitVec x <<< UInt8.ofBitVec y).toBitVec else 0 := by
  split
  · rename_i h
    have h' : y.toNat < 8 := h
    show x <<< y.toNat = x <<< (y % 8).toNat
    rw [BitVec.toNat_umod]; simp [Nat.mod_eq_of_lt h']
  · rename_i h
    have h' : ¬ y.toNat < 8 := h
    exact BitVec.shiftLeft_eq_zero (by omega)
theorem bitvec8_shiftRight :
    x >>> y = if UInt8.ofBitVec y < 8 then (UInt8.ofBitVec x >>> UInt8.ofBitVec y).toBitVec else 0 := by
  split
  · rename_i h
    have h' : y.toNat < 8 := h
    show x >>> y.toNat = x >>> (y % 8).toNat
    rw [BitVec.toNat_umod]; simp [Nat.mod_eq_of_lt h']
  · rename_i h
    have h' : ¬ y.toNat < 8 := h
    exact BitVec.ushiftRight_eq_zero (by omega)
theorem bitvec8_shiftLeft_nat :
    x <<< n = if n < 8 then (UInt8.ofBitVec x <<< UInt8.ofNat n).toBitVec else 0 := by
  split
  · rename_i h
    show x <<< n = x <<< ((BitVec.ofNat 8 n) % 8).toNat
    rw [BitVec.toNat_umod]; simp [Nat.mod_eq_of_lt h]
  · exact BitVec.shiftLeft_eq_zero (by omega)
theorem bitvec8_shiftRight_nat :
    x >>> n = if n < 8 then (UInt8.ofBitVec x >>> UInt8.ofNat n).toBitVec else 0 := by
  split
  · rename_i h
    show x >>> n = x >>> ((BitVec.ofNat 8 n) % 8).toNat
    rw [BitVec.toNat_umod]; simp [Nat.mod_eq_of_lt h]
  · exact BitVec.ushiftRight_eq_zero (by omega)
theorem bitvec8_shiftLeft_lit (h : n < 8) : x <<< n = (UInt8.ofBitVec x <<< UInt8.ofNat n).toBitVec := by
  rw [bitvec8_shiftLeft_nat]; simp [h]
theorem bitvec8_shiftRight_lit (h : n < 8) : x >>> n = (UInt8.ofBitVec x >>> UInt8.ofNat n).toBitVec := by
  rw [bitvec8_shiftRight_nat]; simp [h]
theorem bitvec8_shiftLeft_big (h : 8 ≤ n) : x <<< n = 0 := BitVec.shiftLeft_eq_zero h
theorem bitvec8_shiftRight_big (h : 8 ≤ n) : x >>> n = 0 := BitVec.ushiftRight_eq_zero h
end

section
variable (x y : BitVec 16) (n : Nat)
theorem bitvec16_toNat : x.toNat = (UInt16.ofBitVec x).toNat := rfl
theorem bitvec16_shiftLeft :
    x <<< y = if UInt16.ofBitVec y < 16 then (UInt16.ofBitVec x <<< UInt16.ofBitVec y).toBitVec else 0 := by
  split
  · rename_i h
    have h' : y.toNat < 16 := h
    show x <<< y.toNat = x <<< (y % 16).toNat
    rw [BitVec.toNat_umod]; simp [Nat.mod_eq_of_lt h']
  · rename_i h
    have h' : ¬ y.toNat < 16 := h
    exact BitVec.shiftLeft_eq_zero (by omega)
theorem bitvec16_shiftRight :
    x >>> y = if UInt16.ofBitVec y < 16 then (UInt16.ofBitVec x >>> UInt16.ofBitVec y).toBitVec else 0 := by
  split
  · rename_i h
    have h' : y.toNat < 16 := h
    show x >>> y.toNat = x >>> (y % 16).toNat
    rw [BitVec.toNat_umod]; simp [Nat.mod_eq_of_lt h']
  · rename_i h
    have h' : ¬ y.toNat < 16 := h
    exact BitVec.ushiftRight_eq_zero (by omega)
theorem bitvec16_shiftLeft_nat :
    x <<< n = if n < 16 then (UInt16.ofBitVec x <<< UInt16.ofNat n).toBitVec else 0 := by
  split
  · rename_i h
    show x <<< n = x <<< ((BitVec.ofNat 16 n) % 16).toNat
    rw [BitVec.toNat_umod]; simp [Nat.mod_eq_of_lt h]
  · exact BitVec.shiftLeft_eq_zero (by omega)
theorem bitvec16_shiftRight_nat :
    x >>> n = if n < 16 then (UInt16.ofBitVec x >>> UInt16.ofNat n).toBitVec else 0 := by
  split
  · rename_i h
    show x >>> n = x >>> ((BitVec.ofNat 16 n) % 16).toNat
    rw [BitVec.toNat_umod]; simp [Nat.mod_eq_of_lt h]
  · exact BitVec.ushiftRight_eq_zero (by omega)
theorem bitvec16_shiftLeft_lit (h : n < 16) : x <<< n = (UInt16.ofBitVec x <<< UInt16.ofNat n).toBitVec := by
  rw [bitvec16_shiftLeft_nat]; simp [h]
theorem bitvec16_shiftRight_lit (h : n < 16) : x >>> n = (UInt16.ofBitVec x >>> UInt16.ofNat n).toBitVec := by
  rw [bitvec16_shiftRight_nat]; simp [h]
theorem bitvec16_shiftLeft_big (h : 16 ≤ n) : x <<< n = 0 := BitVec.shiftLeft_eq_zero h
theorem bitvec16_shiftRight_big (h : 16 ≤ n) : x >>> n = 0 := BitVec.ushiftRight_eq_zero h
end

section
variable (x y : BitVec 32) (n : Nat)
theorem bitvec32_toNat : x.toNat = (UInt32.ofBitVec x).toNat := rfl
theorem bitvec32_shiftLeft :
    x <<< y = if UInt32.ofBitVec y < 32 then (UInt32.ofBitVec x <<< UInt32.ofBitVec y).toBitVec else 0 := by
  split
  · rename_i h
    have h' : y.toNat < 32 := h
    show x <<< y.toNat = x <<< (y % 32).toNat
    rw [BitVec.toNat_umod]; simp [Nat.mod_eq_of_lt h']
  · rename_i h
    have h' : ¬ y.toNat < 32 := h
    exact BitVec.shiftLeft_eq_zero (by omega)
theorem bitvec32_shiftRight :
    x >>> y = if UInt32.ofBitVec y < 32 then (UInt32.ofBitVec x >>> UInt32.ofBitVec y).toBitVec else 0 := by
  split
  · rename_i h
    have h' : y.toNat < 32 := h
    show x >>> y.toNat = x >>> (y % 32).toNat
    rw [BitVec.toNat_umod]; simp [Nat.mod_eq_of_lt h']
  · rename_i h
    have h' : ¬ y.toNat < 32 := h
    exact BitVec.ushiftRight_eq_zero (by omega)
theorem bitvec32_shiftLeft_nat :
    x <<< n = if n < 32 then (UInt32.ofBitVec x <<< UInt32.ofNat n).toBitVec else 0 := by
  split
  · rename_i h
    show x <<< n = x <<< ((BitVec.ofNat 32 n) % 32).toNat
    rw [BitVec.toNat_umod]; simp [Nat.mod_eq_of_lt h]
  · exact BitVec.shiftLeft_eq_zero (by omega)
theorem bitvec32_shiftRight_nat :
    x >>> n = if n < 32 then (UInt32.ofBitVec x >>> UInt32.ofNat n).toBitVec else 0 := by
  split
  · rename_i h
    show x >>> n = x >>> ((BitVec.ofNat 32 n) % 32).toNat
    rw [BitVec.toNat_umod]; simp [Nat.mod_eq_of_lt h]
  · exact BitVec.ushiftRight_eq_zero (by omega)
theorem bitvec32_shiftLeft_lit (h : n < 32) : x <<< n = (UInt32.ofBitVec x <<< UInt32.ofNat n).toBitVec := by
  rw [bitvec32_shiftLeft_nat]; simp [h]
theorem bitvec32_shiftRight_lit (h : n < 32) : x >>> n = (UInt32.ofBitVec x >>> UInt32.ofNat n).toBitVec := by
  rw [bitvec32_shiftRight_nat]; simp [h]
theorem bitvec32_shiftLeft_big (h : 32 ≤ n) : x <<< n = 0 := BitVec.shiftLeft_eq_zero h
theorem bitvec32_shiftRight_big (h : 32 ≤ n) : x >>> n = 0 := BitVec.ushiftRight_eq_zero h
end

section
variable (x y : BitVec 64) (n : Nat)
theorem bitvec64_toNat : x.toNat = (UInt64.ofBitVec x).toNat := rfl
theorem bitvec64_shiftLeft :
    x <<< y = if UInt64.ofBitVec y < 64 then (UInt64.ofBitVec x <<< UInt64.ofBitVec y).toBitVec else 0 := by
  split
  · rename_i h
    have h' : y.toNat < 64 := h
    show x <<< y.toNat = x <<< (y % 64).toNat
    rw [BitVec.toNat_umod]; simp [Nat.mod_eq_of_lt h']
  · rename_i h
    have h' : ¬ y.toNat < 64 := h
    exact BitVec.shiftLeft_eq_zero (by omega)
theorem bitvec64_shiftRight :
    x >>> y = if UInt64.ofBitVec y < 64 then (UInt64.ofBitVec x >>> UInt64.ofBitVec y).toBitVec else 0 := by
  split
  · rename_i h
    have h' : y.toNat < 64 := h
    show x >>> y.toNat = x >>> (y % 64).toNat
    rw [BitVec.toNat_umod]; simp [Nat.mod_eq_of_lt h']
  · rename_i h
    have h' : ¬ y.toNat < 64 := h
    exact BitVec.ushiftRight_eq_zero (by omega)
theorem bitvec64_shiftLeft_nat :
    x <<< n = if n < 64 then (UInt64.ofBitVec x <<< UInt64.ofNat n).toBitVec else 0 := by
  split
  · rename_i h
    show x <<< n = x <<< ((BitVec.ofNat 64 n) % 64).toNat
    rw [BitVec.toNat_umod]; simp [Nat.mod_eq_of_lt h]
  · exact BitVec.shiftLeft_eq_zero (by omega)
theorem bitvec64_shiftRight_nat :
    x >>> n = if n < 64 then (UInt64.ofBitVec x >>> UInt64.ofNat n).toBitVec else 0 := by
  split
  · rename_i h
    show x >>> n = x >>> ((BitVec.ofNat 64 n) % 64).toNat
    rw [BitVec.toNat_umod]; simp [Nat.mod_eq_of_lt h]
  · exact BitVec.ushiftRight_eq_zero (by omega)
theorem bitvec64_shiftLeft_lit (h : n < 64) : x <<< n = (UInt64.ofBitVec x <<< UInt64.ofNat n).toBitVec := by
  rw [bitvec64_shiftLeft_nat]; simp [h]
theorem bitvec64_shiftRight_lit (h : n < 64) : x >>> n = (UInt64.ofBitVec x >>> UInt64.ofNat n).toBitVec := by
  rw [bitvec64_shiftRight_nat]; simp [h]
theorem bitvec64_shiftLeft_big (h : 64 ≤ n) : x <<< n = 0 := BitVec.shiftLeft_eq_zero h
theorem bitvec64_shiftRight_big (h : 64 ≤ n) : x >>> n = 0 := BitVec.ushiftRight_eq_zero h
end

end LeanScript.Gen

end
