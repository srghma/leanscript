module

public import RuntimeSpec.Runtime
import all Init.Data.UInt.Log2
import all Init.Data.Fin.Log2

@[expose] public section

set_option autoImplicit false

/-!
# The refactored `runtime.js` is correct

For the functions of `runtime.js` whose code the refactoring changed (transcribed in
`RuntimeSpec.Runtime` into the model of `RuntimeSpec.Model`):

* **they compute Lean's operation** on every argument of their representation (a `uint53`
  argument is a `Nat` below `2^53`, an `int53` one an `IsSafe` `Int`, a `BigInt` any integer);
  a function that may throw returns `toNum53` of Lean's result, i.e. it throws exactly when
  Lean's result is not a safe integer;
* **they agree with the old runtime**: on a `BigInt` (resp. a `number`) the new function
  gives what the old one gave on `JsInt.big` (resp. `JsInt.num`), which is why the `typeof`
  tests could go; and every throw that was removed never fired (the old function returned
  `some` of the new result on every argument of the representation).
-/

namespace RuntimeSpec

/-- The `uint53` representation: a `Nat` below `2^53`. -/
abbrev U53 (a : Nat) : Prop := a < 2 ^ 53

private theorem natCast_two_pow_64 : ((2 ^ 64 : Nat) : Int) = 18446744073709551616 := rfl

private theorem toNum53_of_eq {x v : Int} (h : x = v) (hs : -maxSafe ≤ v ∧ v ≤ maxSafe) :
    toNum53 x = some v := by
  subst h; simp [toNum53, hs]

/-! ## Fixed-width conversions -/

private theorem setWidth_toInt (a : Int) (n : Nat) (hn : n = 8 ∨ n = 16) :
    ((BitVec.ofInt 32 a).setWidth n).toInt = a.bmod (2 ^ n) := by
  have : (BitVec.ofInt 32 a).setWidth n = BitVec.ofInt n a := by
    apply BitVec.eq_of_toNat_eq
    rcases hn with rfl | rfl <;> simp [BitVec.toNat_ofInt] <;> omega
  rw [this, BitVec.toInt_ofInt]

theorem uint53__lean_uint16_of_nat_correct (a : Nat) :
    New.uint53__lean_uint16_of_nat a = (UInt16.ofNat a).toNat := by
  simp [New.uint53__lean_uint16_of_nat, band, toI32, BitVec.toInt_and, UInt16.toNat_ofNat']
  rw [show (65535 : Nat) = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Int.bmod_def]
  omega

theorem uint53__lean_uint32_of_nat_correct (a : Nat) :
    New.uint53__lean_uint32_of_nat a = (UInt32.ofNat a).toNat := by
  simp [New.uint53__lean_uint32_of_nat, ushr, shiftCount, toI32, UInt32.toNat_ofNat']

theorem uint53__lean_uint8_of_nat_correct (a : Nat) :
    New.uint53__lean_uint8_of_nat a = (UInt8.ofNat a).toNat := by
  simp [New.uint53__lean_uint8_of_nat, band, toI32, BitVec.toInt_and, UInt8.toNat_ofNat']
  rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Int.bmod_def]
  omega

theorem int53__lean_int16_of_int_correct (a : Int) :
    New.int53__lean_int16_of_int a = (Int16.ofInt a).toInt := by
  have h : ∀ x : BitVec 32, (x <<< 16).sshiftRight 16 = (x.setWidth 16).signExtend 32 := by
    intro x
    ext i hi
    simp only [BitVec.getElem_sshiftRight, BitVec.getElem_signExtend, BitVec.getElem_setWidth,
      BitVec.msb_shiftLeft, BitVec.msb_setWidth, BitVec.getElem_shiftLeft]
    by_cases h : i < 16
    · have h2 : 16 + i < 32 := by omega
      simp [h, h2, BitVec.getLsbD_eq_getElem hi]
    · have h2 : ¬ 16 + i < 32 := by omega
      simp [h, h2, BitVec.getMsbD, BitVec.getLsbD_eq_getElem]
  simp only [New.int53__lean_int16_of_int, sar, shl, shiftCount, toI32, BitVec.ofInt_toInt,
    show (BitVec.ofInt 32 16).toNat % 32 = 16 from rfl, h,
    BitVec.toInt_signExtend_of_le (show 16 ≤ 32 by omega), Int16.toInt_ofInt]
  exact setWidth_toInt a 16 (by simp)

theorem int53__lean_int32_of_int_correct (a : Int) :
    New.int53__lean_int32_of_int a = (Int32.ofInt a).toInt := by
  simp [New.int53__lean_int32_of_int, bor, toI32, Int32.toInt_ofInt, BitVec.toInt_ofInt]

theorem int53__lean_int8_of_int_correct (a : Int) :
    New.int53__lean_int8_of_int a = (Int8.ofInt a).toInt := by
  have h : ∀ x : BitVec 32, (x <<< 24).sshiftRight 24 = (x.setWidth 8).signExtend 32 := by
    intro x
    ext i hi
    simp only [BitVec.getElem_sshiftRight, BitVec.getElem_signExtend, BitVec.getElem_setWidth,
      BitVec.msb_shiftLeft, BitVec.msb_setWidth, BitVec.getElem_shiftLeft]
    by_cases h : i < 8
    · have h2 : 24 + i < 32 := by omega
      simp [h, h2, BitVec.getLsbD_eq_getElem hi]
    · have h2 : ¬ 24 + i < 32 := by omega
      simp [h, h2, BitVec.getMsbD, BitVec.getLsbD_eq_getElem]
  simp only [New.int53__lean_int8_of_int, sar, shl, shiftCount, toI32, BitVec.ofInt_toInt,
    show (BitVec.ofInt 32 24).toNat % 32 = 24 from rfl, h,
    BitVec.toInt_signExtend_of_le (show 8 ≤ 32 by omega), Int8.toInt_ofInt]
  exact setWidth_toInt a 8 (by simp)

theorem bigint_int__lean_int16_of_int_correct (a : Int) :
    New.bigint_int__lean_int16_of_int a = (Int16.ofInt a).toInt := by
  simp [New.bigint_int__lean_int16_of_int, asIntN, Int16.toInt_ofInt, Int16.size]

theorem bigint_nat__lean_uint16_of_nat_correct (a : Nat) :
    New.bigint_nat__lean_uint16_of_nat a = (UInt16.ofNat a).toNat := by
  simp [New.bigint_nat__lean_uint16_of_nat, asUintN, UInt16.toNat_ofNat']

/-! ## The `typeof` tests could go -/

theorem bigint_int__lean_int16_of_int_old (a : Int) :
    Old.bigint_int__lean_int16_of_int (.big a) = New.bigint_int__lean_int16_of_int a ∧
    Old.bigint_int__lean_int16_of_int (.num a) = New.int53__lean_int16_of_int a := by
  exact ⟨rfl, rfl⟩

theorem bigint_nat__lean_uint16_of_nat_old (a : Nat) :
    Old.bigint_nat__lean_uint16_of_nat (.big a) = New.bigint_nat__lean_uint16_of_nat a ∧
    Old.bigint_nat__lean_uint16_of_nat (.num a) = New.uint53__lean_uint16_of_nat a := by
  refine ⟨rfl, ?_⟩
  rw [uint53__lean_uint16_of_nat_correct, UInt16.toNat_ofNat']
  simp only [Old.bigint_nat__lean_uint16_of_nat]
  have h1 : (a : Int).tmod 65536 = a % 65536 := Int.tmod_eq_emod_of_nonneg (by omega)
  rw [h1, Int.tmod_eq_emod_of_nonneg (by omega)]
  omega

theorem bigint_int__uint53__lean_nat_abs_old (a : Int) :
    Old.bigint_int__uint53__lean_nat_abs (.big a) = New.bigint_int__uint53__lean_nat_abs a ∧
    Old.bigint_int__uint53__lean_nat_abs (.num a) = some (New.int53__uint53__lean_nat_abs a) := by
  refine ⟨rfl, ?_⟩
  simp only [Old.bigint_int__uint53__lean_nat_abs, New.int53__uint53__lean_nat_abs]
  split <;> (congr 1; omega)

theorem bigint_nat__int53__lean_int_neg_succ_of_nat_old (a : Nat) :
    Old.bigint_nat__int53__lean_int_neg_succ_of_nat (.big a) =
      New.bigint_nat__int53__lean_int_neg_succ_of_nat a ∧
    Old.bigint_nat__int53__lean_int_neg_succ_of_nat (.num a) =
      some (New.uint53__int53__lean_int_neg_succ_of_nat a) := by
  exact ⟨rfl, rfl⟩

private theorem getD_ge {α : Type} (d : α) (a : List α) (k : Nat) (h : a.length ≤ k) :
    a.getD k d = d := by
  simp [List.getD, List.getElem?_eq_none h]

/-- `Array.get!` on a `BigInt` index: the new `Number(i)` (for any conversion `num` that is
monotone and exact on safe integers, as `Number` of a `BigInt` is) replaces the old `$idx`,
and both compute Lean's `a[i]!` with default `d` (a JavaScript array is shorter than `2^32`). -/
theorem bigint_nat__lean_array_get_correct {α : Type} (num : Int → Int)
    (hmono : ∀ x y, x ≤ y → num x ≤ num y) (hexact : ∀ x, IsSafe x → num x = x)
    (d : α) (a : List α) (ha : a.length < 2 ^ 32) (i : Nat) :
    New.bigint_nat__lean_array_get num d a i = a.getD i d ∧
    Old.bigint_nat__lean_array_get num d a (.big i) = a.getD i d := by
  have hsafe : ∀ n : Nat, n < 2 ^ 32 → IsSafe n := fun n hn => by
    unfold IsSafe maxSafe; omega
  by_cases hi : i < a.length
  · have := hexact i (hsafe i (by omega))
    have h2 : ¬ ((i : Int) > maxSafe) := by unfold maxSafe; omega
    simp [New.bigint_nat__lean_array_get, Old.bigint_nat__lean_array_get, Old.idx, this, hi, h2]
  · have hge : (a.length : Int) ≤ num i := by
      have := hmono a.length i (by omega)
      rwa [hexact _ (hsafe _ ha)] at this
    have hd := getD_ge d a i (by omega)
    refine ⟨?_, ?_⟩
    · simp only [New.bigint_nat__lean_array_get]
      rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega)), hd]
    · by_cases hbig : (i : Int) > maxSafe
      · simp only [Old.bigint_nat__lean_array_get, Old.idx, hbig, ↓reduceIte]
        exact hd.symm
      · have : ¬ num i < a.length := by omega
        simp only [Old.bigint_nat__lean_array_get, Old.idx, hbig, this, ↓reduceIte]
        exact hd.symm

theorem uint53__lean_array_get_correct {α : Type} (d : α) (a : List α) (i : Nat) :
    New.uint53__lean_array_get d a i = a.getD i d := by
  simp only [New.uint53__lean_array_get]
  split
  · simp
  · rw [getD_ge d a i (by omega)]

/-! ## Bitwise operations below `2^53` -/

private theorem toI32_natCast (n : Nat) : toI32 n = BitVec.ofNat 32 n := BitVec.ofInt_natCast 32 n

private theorem bmod32_small (n : Nat) (h : n < 2 ^ 31) : ((n : Int)).bmod (2 ^ 32) = n := by
  rw [Int.bmod_def]; split <;> omega

private theorem bor_zero_small (n : Nat) (h : n < 2 ^ 31) : bor n 0 = n := by
  simp only [bor, BitVec.toInt_or, toI32_natCast, BitVec.toNat_ofNat]
  rw [show (toI32 0).toNat = 0 from rfl, Nat.or_zero,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 32)]
  exact bmod32_small n h

private theorem tdiv32 (a : Nat) : (a : Int).tdiv (2 ^ 32) = ((a / 2 ^ 32 : Nat) : Int) := by
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega), Int.natCast_ediv]; rfl

private theorem band_small (m n : Nat) (hm : m < 2 ^ 31) (hn : n < 2 ^ 31) :
    band m n = ((m &&& n : Nat) : Int) := by
  simp only [band, BitVec.toInt_and, toI32_natCast, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : m < 2 ^ 32), Nat.mod_eq_of_lt (by omega : n < 2 ^ 32)]
  exact bmod32_small _ (Nat.and_lt_two_pow _ hn)

private theorem ushr_band (m n : Nat) : ushr (band m n) 0 = (((m &&& n) % 2 ^ 32 : Nat) : Int) := by
  simp only [ushr, band, toI32, BitVec.ofInt_toInt, shiftCount,
    show (BitVec.ofInt 32 0).toNat % 32 = 0 from rfl, BitVec.ushiftRight_zero,
    BitVec.toNat_and, BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.and_mod_two_pow]

private theorem bor_small (m n : Nat) (hm : m < 2 ^ 31) (hn : n < 2 ^ 31) :
    bor m n = ((m ||| n : Nat) : Int) := by
  simp only [bor, BitVec.toInt_or, toI32_natCast, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : m < 2 ^ 32), Nat.mod_eq_of_lt (by omega : n < 2 ^ 32)]
  exact bmod32_small _ (Nat.or_lt_two_pow hm hn)

private theorem bxor_small (m n : Nat) (hm : m < 2 ^ 31) (hn : n < 2 ^ 31) :
    bxor m n = ((m ^^^ n : Nat) : Int) := by
  simp only [bxor, BitVec.toInt_xor, toI32_natCast, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : m < 2 ^ 32), Nat.mod_eq_of_lt (by omega : n < 2 ^ 32)]
  exact bmod32_small _ (Nat.xor_lt_two_pow hm hn)

private theorem ushr_bor (m n : Nat) : ushr (bor m n) 0 = (((m ||| n) % 2 ^ 32 : Nat) : Int) := by
  simp only [ushr, bor, toI32, BitVec.ofInt_toInt, shiftCount,
    show (BitVec.ofInt 32 0).toNat % 32 = 0 from rfl, BitVec.ushiftRight_zero,
    BitVec.toNat_or, BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.or_mod_two_pow]

private theorem ushr_bxor (m n : Nat) : ushr (bxor m n) 0 = (((m ^^^ n) % 2 ^ 32 : Nat) : Int) := by
  simp only [ushr, bxor, toI32, BitVec.ofInt_toInt, shiftCount,
    show (BitVec.ofInt 32 0).toNat % 32 = 0 from rfl, BitVec.ushiftRight_zero,
    BitVec.toNat_xor, BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.xor_mod_two_pow]

private theorem clz32_nat (n : Nat) (h0 : n ≠ 0) (h : n < 2 ^ 32) : clz32 n = 31 - n.log2 := by
  simp only [clz32, toI32_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, h0, ↓reduceIte]


theorem land53_correct (a b : Nat) (ha : U53 a) (hb : U53 b) :
    New.land53 a b = (a &&& b : Nat) := by
  have h1 : a / 2 ^ 32 < 2 ^ 31 := by omega
  have h2 : b / 2 ^ 32 < 2 ^ 31 := by omega
  simp only [New.land53, tdiv32, bor_zero_small _ h1, bor_zero_small _ h2, band_small _ _ h1 h2,
    ushr_band, ← Nat.and_div_two_pow]
  have := Nat.div_add_mod (a &&& b) (2 ^ 32)
  omega

theorem lor53_correct (a b : Nat) (ha : U53 a) (hb : U53 b) :
    New.lor53 a b = (a ||| b : Nat) := by
  have h1 : a / 2 ^ 32 < 2 ^ 31 := by omega
  have h2 : b / 2 ^ 32 < 2 ^ 31 := by omega
  simp only [New.lor53, tdiv32, bor_zero_small _ h1, bor_zero_small _ h2, bor_small _ _ h1 h2,
    ushr_bor, ← Nat.or_div_two_pow]
  have := Nat.div_add_mod (a ||| b) (2 ^ 32)
  omega

theorem xor53_correct (a b : Nat) (ha : U53 a) (hb : U53 b) :
    New.xor53 a b = (a ^^^ b : Nat) := by
  have h1 : a / 2 ^ 32 < 2 ^ 31 := by omega
  have h2 : b / 2 ^ 32 < 2 ^ 31 := by omega
  simp only [New.xor53, tdiv32, bor_zero_small _ h1, bor_zero_small _ h2, bxor_small _ _ h1 h2,
    ushr_bxor, ← Nat.xor_div_two_pow]
  have := Nat.div_add_mod (a ^^^ b) (2 ^ 32)
  omega

theorem log2_53_correct (a : Nat) (ha : U53 a) : New.log2_53 a = a.log2 := by
  unfold New.log2_53
  by_cases hsmall : (a : Int) < 2 ^ 32
  · simp only [hsmall, ↓reduceIte]
    by_cases h0 : a = 0
    · subst h0; rfl
    · have hlt := (Nat.log2_lt h0).mpr (show a < 2 ^ 32 by omega)
      simp only [show ¬ ((a : Int) = 0) by omega, ↓reduceIte, clz32_nat a h0 (by omega)]
      omega
  · simp only [hsmall, ↓reduceIte, tdiv32]
    have hh0 : a / 2 ^ 32 ≠ 0 := by omega
    have hlt := (Nat.log2_lt hh0).mpr (show a / 2 ^ 32 < 2 ^ 21 by omega)
    rw [clz32_nat _ hh0 (by omega)]
    have key : a.log2 = (a / 2 ^ 32).log2 + 32 := by
      have h0 : a ≠ 0 := by omega
      rw [Nat.log2_eq_iff h0]
      have l1 := Nat.log2_self_le hh0
      have l2 := (Nat.lt_log2_self (n := a / 2 ^ 32))
      constructor
      · rw [Nat.pow_add]
        exact (Nat.le_div_iff_mul_le (by decide)).mp l1
      · rw [Nat.add_right_comm, Nat.pow_add]
        exact (Nat.div_lt_iff_lt_mul (by decide)).mp l2
    omega

/-- `uint53__lean_uint64_land` computes `UInt64.land`, which never needs the removed check. -/
theorem uint53__lean_uint64_land_correct (a b : Nat) (ha : U53 a) (hb : U53 b) :
    New.land53 a b = (UInt64.ofNat a &&& UInt64.ofNat b).toNat ∧
    toNum53 (UInt64.ofNat a &&& UInt64.ofNat b).toNat = some (New.land53 a b) := by
  have e : (UInt64.ofNat a &&& UInt64.ofNat b).toNat = (a &&& b : Nat) := by
    rw [UInt64.toNat_and, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt (by omega : a < 2 ^ 64), Nat.mod_eq_of_lt (by omega : b < 2 ^ 64)]
  have hlt : (a &&& b : Nat) < 2 ^ 53 := Nat.and_lt_two_pow a hb
  rw [e, land53_correct a b ha hb]
  exact ⟨rfl, toNum53_of_eq rfl (by unfold maxSafe; omega)⟩

theorem uint53__lean_uint64_lor_correct (a b : Nat) (ha : U53 a) (hb : U53 b) :
    New.lor53 a b = (UInt64.ofNat a ||| UInt64.ofNat b).toNat ∧
    toNum53 (UInt64.ofNat a ||| UInt64.ofNat b).toNat = some (New.lor53 a b) := by
  have e : (UInt64.ofNat a ||| UInt64.ofNat b).toNat = (a ||| b : Nat) := by
    rw [UInt64.toNat_or, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt (by omega : a < 2 ^ 64), Nat.mod_eq_of_lt (by omega : b < 2 ^ 64)]
  have hlt : (a ||| b : Nat) < 2 ^ 53 := Nat.or_lt_two_pow ha hb
  rw [e, lor53_correct a b ha hb]
  exact ⟨rfl, toNum53_of_eq rfl (by unfold maxSafe; omega)⟩

theorem uint53__lean_uint64_xor_correct (a b : Nat) (ha : U53 a) (hb : U53 b) :
    New.xor53 a b = (UInt64.ofNat a ^^^ UInt64.ofNat b).toNat ∧
    toNum53 (UInt64.ofNat a ^^^ UInt64.ofNat b).toNat = some (New.xor53 a b) := by
  have e : (UInt64.ofNat a ^^^ UInt64.ofNat b).toNat = (a ^^^ b : Nat) := by
    rw [UInt64.toNat_xor, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt (by omega : a < 2 ^ 64), Nat.mod_eq_of_lt (by omega : b < 2 ^ 64)]
  have hlt : (a ^^^ b : Nat) < 2 ^ 53 := Nat.xor_lt_two_pow ha hb
  rw [e, xor53_correct a b ha hb]
  exact ⟨rfl, toNum53_of_eq rfl (by unfold maxSafe; omega)⟩

theorem uint53__lean_uint64_log2_correct (a : Nat) (ha : U53 a) :
    New.log2_53 a = (UInt64.ofNat a).log2.toNat ∧
    toNum53 (UInt64.ofNat a).log2.toNat = some (New.log2_53 a) := by
  have e : (UInt64.ofNat a).log2.toNat = a.log2 := by
    rw [show (UInt64.ofNat a).log2.toNat = (UInt64.ofNat a).toNat.log2 from rfl,
      UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : a < 2 ^ 64)]
  have hlt : a.log2 < 2 ^ 53 := by
    by_cases h0 : a = 0
    · subst h0; decide
    · have := (Nat.log2_lt h0).mpr ha; omega
  rw [e, log2_53_correct a ha]
  exact ⟨rfl, toNum53_of_eq rfl (by unfold maxSafe; omega)⟩

/-! ## `UInt64` below `2^53` -/

theorem uint53__lean_uint64_add_correct (a b : Nat) (ha : U53 a) (hb : U53 b) :
    New.uint53__lean_uint64_add a b = toNum53 (UInt64.ofNat a + UInt64.ofNat b).toNat ∧
    New.uint53__lean_uint64_add a b = Old.uint53__lean_uint64_add a b := by
  simp only [New.uint53__lean_uint64_add, Old.uint53__lean_uint64_add, asUintN,
    UInt64.toNat_add, UInt64.toNat_ofNat']
  constructor <;> (congr 1; omega)

theorem uint53__lean_uint64_sub_correct (a b : Nat) (ha : U53 a) (hb : U53 b) :
    New.uint53__lean_uint64_sub a b = toNum53 (UInt64.ofNat a - UInt64.ofNat b).toNat ∧
    New.uint53__lean_uint64_sub a b = Old.uint53__lean_uint64_sub a b := by
  simp only [New.uint53__lean_uint64_sub, Old.uint53__lean_uint64_sub, asUintN,
    UInt64.toNat_sub, UInt64.toNat_ofNat']
  by_cases h : (a : Int) ≥ b
  · simp only [h, ↓reduceIte]
    exact ⟨(toNum53_of_eq (by omega) (by unfold maxSafe; omega)).symm,
      (toNum53_of_eq (by omega) (by unfold maxSafe; omega)).symm⟩
  · simp only [h, ↓reduceIte]
    refine ⟨?_, trivial⟩
    congr 1
    rw [natCast_two_pow_64]
    omega

theorem uint53__lean_uint64_neg_correct (a : Nat) (ha : U53 a) :
    New.uint53__lean_uint64_neg a = toNum53 (-UInt64.ofNat a).toNat ∧
    New.uint53__lean_uint64_neg a = Old.uint53__lean_uint64_neg a := by
  simp only [New.uint53__lean_uint64_neg, Old.uint53__lean_uint64_neg, asUintN,
    UInt64.toNat_neg, UInt64.toNat_ofNat', UInt64.size]
  by_cases h : (a : Int) = 0
  · simp only [h, ↓reduceIte]
    exact ⟨(toNum53_of_eq (by omega) (by unfold maxSafe; omega)).symm,
      (toNum53_of_eq (by omega) (by unfold maxSafe; omega)).symm⟩
  · simp only [h, ↓reduceIte]
    constructor <;> (congr 1; omega)

theorem uint53__lean_uint64_complement_correct (a : Nat) :
    New.uint53__lean_uint64_complement a = toNum53 (~~~UInt64.ofNat a).toNat := by
  simp only [New.uint53__lean_uint64_complement, asUintN, UInt64.toNat_not, UInt64.toNat_ofNat',
    UInt64.size]
  congr 1; omega

theorem uint53__lean_uint64_mul_correct (a b : Nat) (ha : U53 a) (hb : U53 b) :
    New.uint53__lean_uint64_mul a b = toNum53 (UInt64.ofNat a * UInt64.ofNat b).toNat := by
  rw [UInt64.toNat_mul, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt (by omega : a < 2^64), Nat.mod_eq_of_lt (by omega : b < 2^64),
    Int.natCast_emod, Int.natCast_mul]
  rfl

/-- `uint53__lean_uint64_div` computes `UInt64.div`, and the old check never fired. -/
theorem uint53__lean_uint64_div_correct (a b : Nat) (ha : U53 a) (hb : U53 b) :
    New.uint53__lean_uint64_div a b = (UInt64.ofNat a / UInt64.ofNat b).toNat ∧
    Old.uint53__lean_uint64_div a b = some (New.uint53__lean_uint64_div a b) := by
  have hq : a / b ≤ a := Nat.div_le_self a b
  have hq' : ((a : Int) / b) = ((a / b : Nat) : Int) := (Int.natCast_ediv a b).symm
  have hnn : 0 ≤ (a : Int) / b := Int.ediv_nonneg (by omega) (by omega)
  simp only [New.uint53__lean_uint64_div, Old.uint53__lean_uint64_div, asUintN,
    UInt64.toNat_div, UInt64.toNat_ofNat', Int.fdiv_eq_ediv_of_nonneg _ (Int.natCast_nonneg b),
    ← Int.natCast_ediv]
  rw [Nat.mod_eq_of_lt (by omega : a < 2^64), Nat.mod_eq_of_lt (by omega : b < 2^64)]
  by_cases h : (b : Int) = 0
  · have : b = 0 := by omega
    subst this
    simp [toNum53, maxSafe]
  · simp only [h, ↓reduceIte]
    rw [natCast_two_pow_64]
    exact ⟨trivial, toNum53_of_eq (by omega) (by unfold maxSafe; omega)⟩

theorem uint53__lean_uint64_mod_correct (a b : Nat) (ha : U53 a) (hb : U53 b) :
    New.uint53__lean_uint64_mod a b = (UInt64.ofNat a % UInt64.ofNat b).toNat ∧
    Old.uint53__lean_uint64_mod a b = some (New.uint53__lean_uint64_mod a b) := by
  have hq : a % b ≤ a := Nat.mod_le a b
  have hq' : ((a : Int) % b) = ((a % b : Nat) : Int) := (Int.natCast_emod a b).symm
  simp only [New.uint53__lean_uint64_mod, Old.uint53__lean_uint64_mod,
    UInt64.toNat_mod, UInt64.toNat_ofNat', Int.tmod_eq_emod_of_nonneg (Int.natCast_nonneg a),
    ← Int.natCast_emod]
  rw [Nat.mod_eq_of_lt (by omega : a < 2^64), Nat.mod_eq_of_lt (by omega : b < 2^64)]
  by_cases h : (b : Int) = 0
  · have : b = 0 := by omega
    subst this
    simp only [h, ↓reduceIte, Nat.mod_zero]
    exact ⟨trivial, toNum53_of_eq rfl (by unfold maxSafe; omega)⟩
  · simp only [h, ↓reduceIte]
    exact ⟨trivial, toNum53_of_eq (by omega) (by unfold maxSafe; omega)⟩

theorem uint53__lean_uint64_shift_right_correct (a b : Nat) (ha : U53 a) (hb : U53 b) :
    New.uint53__lean_uint64_shift_right a b = (UInt64.ofNat a >>> UInt64.ofNat b).toNat ∧
    Old.uint53__lean_uint64_shift_right a b = some (New.uint53__lean_uint64_shift_right a b) := by
  have hq : a / 2 ^ (b % 64) ≤ a := Nat.div_le_self _ _
  have e1 : (b : Int).tmod 64 = ((b % 64 : Nat) : Int) := by
    rw [Int.tmod_eq_emod_of_nonneg (Int.natCast_nonneg b), Int.natCast_emod]; rfl
  have e2 : (((b : Int) % 64 + 64) % 64).toNat = b % 64 := by omega
  simp only [New.uint53__lean_uint64_shift_right, Old.uint53__lean_uint64_shift_right,
    UInt64.toNat_shiftRight, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow,
    Int.shiftRight_eq_div_pow, e1, e2, Int.toNat_natCast]
  rw [Nat.mod_eq_of_lt (by omega : a < 2^64), Nat.mod_eq_of_lt (by omega : b < 2^64)]
  have e3 : ((2 : Int) ^ (b % 64)) = ((2 ^ (b % 64) : Nat) : Int) := by push_cast; rfl
  rw [e3, Int.fdiv_eq_ediv_of_nonneg _ (Int.natCast_nonneg _)]
  have hq' := (Int.natCast_ediv a (2 ^ (b % 64))).symm
  have hnn : 0 ≤ (a : Int) / ((2 ^ (b % 64) : Nat) : Int) :=
    Int.ediv_nonneg (by omega) (Int.natCast_nonneg _)
  exact ⟨by omega, toNum53_of_eq rfl (by unfold maxSafe; omega)⟩

theorem uint53__lean_uint64_of_nat_correct (a : Nat) (ha : U53 a) :
    New.uint53__lean_uint64_of_nat a = (UInt64.ofNat a).toNat ∧
    toNum53 (UInt64.ofNat a).toNat = some (New.uint53__lean_uint64_of_nat a) := by
  simp only [New.uint53__lean_uint64_of_nat, UInt64.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (by omega : a < 2^64)]
  exact ⟨rfl, toNum53_of_eq rfl (by unfold maxSafe; omega)⟩

/-! ## `Int64` of absolute value below `2^53` -/

private theorem bmod64_of_small (x : Int) (h1 : -2 ^ 63 ≤ x) (h2 : x < 2 ^ 63) :
    x.bmod (2 ^ 64) = x := by
  rw [Int.bmod_def]; split <;> omega

private theorem ofInt64_toInt (a : Int) (ha : IsSafe a) : (Int64.ofInt a).toInt = a := by
  rw [Int64.toInt_ofInt]; unfold IsSafe maxSafe at ha
  exact bmod64_of_small a (by omega) (by omega)

private theorem natAbs_tmod_le (a b : Int) : (a.tmod b).natAbs ≤ a.natAbs := by
  have key : ∀ n : Nat, 0 ≤ (n : Int).tmod b ∧ (n : Int).tmod b ≤ n := by
    intro n
    rw [Int.tmod_eq_emod_of_nonneg (by omega)]
    have : (n : Int) % b = ((n % b.natAbs : Nat) : Int) := by
      rcases Int.natAbs_eq b with h | h
      · conv => lhs; rw [h]
        rw [Int.natCast_emod]
      · conv => lhs; rw [h]
        rw [Int.emod_neg, Int.natCast_emod]
    rw [this]
    exact ⟨Int.natCast_nonneg _, Int.ofNat_le.mpr (Nat.mod_le _ _)⟩
  rcases Int.natAbs_eq a with h | h
  · have := key a.natAbs; rw [h]; omega
  · have := key a.natAbs; rw [h, Int.neg_tmod]; omega

/-- The shift count of `int53__lean_int64_shift_right`: `((b % 64) + 64) % 64` (JavaScript's
`%` truncates) is `b` modulo 64. -/
private theorem js_shift_count (b : Int) : ((b.tmod 64 + 64).tmod 64) = b % 64 := by
  rw [Int.tmod_eq_emod (a := b), Int.tmod_eq_emod]
  by_cases h1 : 0 ≤ b ∨ (64 : Int) ∣ b
  · simp only [h1, ↓reduceIte]
    by_cases h2 : 0 ≤ b % 64 - ↑(0 : Nat) + 64 ∨ (64 : Int) ∣ b % 64 - ↑(0 : Nat) + 64
    · simp only [h2, ↓reduceIte]; omega
    · simp only [h2, ↓reduceIte]; omega
  · simp only [h1, ↓reduceIte]
    have : 0 ≤ b % 64 - ↑(Int.natAbs 64) + 64 := by simp; omega
    simp only [this, true_or, ↓reduceIte]; simp

private theorem smod64_toNat (b : Int64) : (b.toBitVec.smod 64).toNat = (b.toInt % 64).toNat := by
  have h1 : (b.toBitVec.smod 64).toInt = b.toInt % 64 := by
    rw [BitVec.toInt_smod, Int.fmod_eq_emod_of_nonneg _ (by decide), Int64.toInt_toBitVec]
    rfl
  have h2 := BitVec.toInt_eq_toNat_cond (b.toBitVec.smod 64)
  have h3 := (b.toBitVec.smod 64).isLt
  rw [h1] at h2
  split at h2 <;> omega

theorem int53__lean_int64_of_int_correct (a : Int) (ha : IsSafe a) :
    New.int53__lean_int64_of_int a = (Int64.ofInt a).toInt ∧
    Old.int53__lean_int64_of_int a = some (New.int53__lean_int64_of_int a) := by
  have h := ha; unfold IsSafe maxSafe at h
  refine ⟨(ofInt64_toInt a ha).symm, ?_⟩
  simp only [Old.int53__lean_int64_of_int, New.int53__lean_int64_of_int, asIntN]
  exact toNum53_of_eq (bmod64_of_small a (by omega) (by omega)) (by unfold maxSafe; omega)

theorem int53__lean_int64_abs_correct (a : Int) (ha : IsSafe a) :
    New.int53__lean_int64_abs a = (Int64.ofInt a).abs.toInt ∧
    Old.int53__lean_int64_abs a = some (New.int53__lean_int64_abs a) := by
  have h := ha; unfold IsSafe maxSafe at h
  have hne : (Int64.ofInt a).toBitVec ≠ BitVec.intMin 64 := by
    intro he
    have := congrArg BitVec.toInt he
    rw [Int64.toInt_toBitVec, ofInt64_toInt a ha, BitVec.toInt_intMin] at this
    simp at this
    omega
  refine ⟨?_, ?_⟩
  · show _ = ((Int64.ofInt a).toBitVec.abs).toInt
    rw [BitVec.toInt_abs_eq_natAbs_of_ne_intMin hne, Int64.toInt_toBitVec, ofInt64_toInt a ha]
    rfl
  · have e : (if a < 0 then -a else a) = (a.natAbs : Int) := by split <;> omega
    simp only [Old.int53__lean_int64_abs, New.int53__lean_int64_abs, asIntN, e]
    exact toNum53_of_eq (bmod64_of_small _ (by omega) (by omega)) (by unfold maxSafe; omega)
    

theorem int53__lean_int64_neg_correct (a : Int) (ha : IsSafe a) :
    New.int53__lean_int64_neg a = (-Int64.ofInt a).toInt ∧
    IsSafe (New.int53__lean_int64_neg a) := by
  have h := ha; unfold IsSafe maxSafe at h
  rw [Int64.toInt_neg, ofInt64_toInt a ha, bmod64_of_small _ (by omega) (by omega)]
  simp only [New.int53__lean_int64_neg, IsSafe, maxSafe]
  omega

theorem int53__lean_int64_add_correct (a b : Int) (ha : IsSafe a) (hb : IsSafe b) :
    New.int53__lean_int64_add a b = toNum53 (Int64.ofInt a + Int64.ofInt b).toInt ∧
    New.int53__lean_int64_add a b = Old.int53__lean_int64_add a b := by
  have h := ha; have h' := hb; unfold IsSafe maxSafe at h h'
  rw [Int64.toInt_add, ofInt64_toInt a ha, ofInt64_toInt b hb,
    bmod64_of_small _ (by omega) (by omega)]
  simp only [New.int53__lean_int64_add, Old.int53__lean_int64_add, asIntN,
    bmod64_of_small _ (by omega : -2 ^ 63 ≤ a + b) (by omega), and_self]

theorem int53__lean_int64_sub_correct (a b : Int) (ha : IsSafe a) (hb : IsSafe b) :
    New.int53__lean_int64_sub a b = toNum53 (Int64.ofInt a - Int64.ofInt b).toInt := by
  have h := ha; have h' := hb; unfold IsSafe maxSafe at h h'
  rw [Int64.toInt_sub, ofInt64_toInt a ha, ofInt64_toInt b hb,
    bmod64_of_small _ (by omega) (by omega)]
  rfl

theorem int53__lean_int64_complement_correct (a : Int) (ha : IsSafe a) :
    New.int53__lean_int64_complement a = toNum53 (~~~Int64.ofInt a).toInt := by
  have h := ha; unfold IsSafe maxSafe at h
  rw [Int64.toInt_not, ofInt64_toInt a ha, bmod64_of_small _ (by omega) (by omega)]
  rfl

theorem int53__lean_int64_div_correct (a b : Int) (ha : IsSafe a) (hb : IsSafe b) :
    New.int53__lean_int64_div a b = (Int64.ofInt a / Int64.ofInt b).toInt ∧
    Old.int53__lean_int64_div a b = some (New.int53__lean_int64_div a b) := by
  have h := ha; have h' := hb; unfold IsSafe maxSafe at h h'
  have hq := Int.natAbs_tdiv_le_natAbs a b
  rw [Int64.toInt_div, ofInt64_toInt a ha, ofInt64_toInt b hb,
    bmod64_of_small _ (by omega) (by omega)]
  simp only [New.int53__lean_int64_div, Old.int53__lean_int64_div, asIntN]
  by_cases hb0 : b = 0
  · subst hb0; simp [Int.tdiv_zero, toNum53, maxSafe]
  · simp only [hb0, ↓reduceIte]
    exact ⟨trivial, toNum53_of_eq (bmod64_of_small _ (by omega) (by omega)) (by unfold maxSafe; omega)⟩

theorem int53__lean_int64_mod_correct (a b : Int) (ha : IsSafe a) (hb : IsSafe b) :
    New.int53__lean_int64_mod a b = (Int64.ofInt a % Int64.ofInt b).toInt ∧
    IsSafe (New.int53__lean_int64_mod a b) := by
  have h := ha; unfold IsSafe maxSafe at h
  have hq := natAbs_tmod_le a b
  rw [Int64.toInt_mod, ofInt64_toInt a ha, ofInt64_toInt b hb]
  simp only [New.int53__lean_int64_mod]
  by_cases hb0 : b = 0
  · subst hb0; simp only [↓reduceIte, Int.tmod_zero]; exact ⟨trivial, ha⟩
  · simp only [hb0, ↓reduceIte]
    refine ⟨trivial, ?_⟩
    unfold IsSafe maxSafe; omega

theorem int53__lean_int64_shift_right_correct (a b : Int) (ha : IsSafe a) (hb : IsSafe b) :
    New.int53__lean_int64_shift_right a b = (Int64.ofInt a >>> Int64.ofInt b).toInt ∧
    IsSafe (New.int53__lean_int64_shift_right a b) := by
  have e : New.int53__lean_int64_shift_right a b = a / ((2 ^ (b % 64).toNat : Nat) : Int) := by
    simp only [New.int53__lean_int64_shift_right, js_shift_count, Int.natCast_pow]
    exact Int.fdiv_eq_ediv_of_nonneg _ (Int.pow_nonneg (by decide))
  rw [e]
  refine ⟨?_, ?_⟩
  · show _ = ((Int64.ofInt a).toBitVec.sshiftRight' ((Int64.ofInt b).toBitVec.smod 64)).toInt
    rw [BitVec.toInt_sshiftRight', smod64_toNat, Int64.toInt_toBitVec, ofInt64_toInt a ha,
      ofInt64_toInt b hb, Int.shiftRight_eq_div_pow]
  · have := Int.natAbs_ediv_le_natAbs a ((2 ^ (b % 64).toNat : Nat) : Int)
    unfold IsSafe maxSafe at ha ⊢
    omega

/-! ## `Nat` / `Int` conversions -/

theorem int53__uint53__lean_nat_abs_correct (a : Int) (ha : IsSafe a) :
    New.int53__uint53__lean_nat_abs a = a.natAbs ∧ IsSafe (New.int53__uint53__lean_nat_abs a) := by
  refine ⟨rfl, ?_⟩
  unfold IsSafe maxSafe at ha ⊢
  simp only [New.int53__uint53__lean_nat_abs]
  omega

theorem uint53__int53__lean_int_neg_succ_of_nat_correct (a : Nat) :
    New.uint53__int53__lean_int_neg_succ_of_nat a = Int.negSucc a := by
  simp only [New.uint53__int53__lean_int_neg_succ_of_nat, Int.negSucc_eq]
  omega

end RuntimeSpec
