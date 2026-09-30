module

public import HashableFloat.HashableFloat
public import HashableFloat.HashableFloat32

@[expose] public section

set_option autoImplicit false

/-!
# Exact identities of IEEE arithmetic

The few laws of `Float` (and `Float32`) arithmetic that hold *exactly*, bit for bit, in Lean's
logical model of floats (`Float.Model`, `UnpackedFloat`):

* `x * 1 = x`, `1 * x = x` and `x / 1 = x`, for every `x` (`NaN` included: the model has one
  `NaN`);
* `x - 0 = x` for every `x`;
* `x + 0 = x` and `0 + x = x` for every `x` except `-0` (`-0 + 0` is `+0`).

The first four are what the `Term` optimiser uses to drop a unit operand of a float operation
(`LeanScript.Term.Optimize.FloatUnit`); the last two are not used there, since a JavaScript
caller may pass `-0`.

The core fact is that rounding a finite float that is already *canonical* for its format (its
exponent is the target exponent of its magnitude, as every unpacked float is:
`unpack_finite_canonical`) is the identity, even when it is written with `k` more mantissa bits
(`roundWithAccuracy_canonical`).  Multiplying or dividing by `1 = 2^k · 2^(-k)` produces exactly
such a value.

Note that re-associating (`(x + a) + b = x + (a + b)`) is **not** among these laws: it changes
the rounding.
-/

namespace LeanScript.FloatIdentities

open Float.Model UnpackedFloat

/-! ## Rounding a canonical float -/

theorem shift_mul_pow (k : Nat) : ∀ m : Nat,
    (⟨m * 2 ^ k, false, false⟩ : ExtendedMantissa) >>> k = ⟨m, false, false⟩ := by
  induction k with
  | zero => intro m; simp [HShiftRight.hShiftRight, Nat.repeat]
  | succ k ih =>
    intro m
    show ExtendedMantissa.shiftRightOne ((⟨m * 2 ^ (k+1), false, false⟩ : ExtendedMantissa) >>> k) = _
    have : m * 2 ^ (k+1) = (m * 2) * 2 ^ k := by rw [Nat.pow_succ]; ac_rfl
    rw [this, ih]
    simp [ExtendedMantissa.shiftRightOne]

theorem log2_mul_pow (m : Nat) (hm : 0 < m) (k : Nat) : (m * 2 ^ k).log2 = m.log2 + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm _ 2, Nat.log2_two_mul, ih]
    · omega
    · exact Nat.ne_of_gt (Nat.mul_pos hm (Nat.two_pow_pos k))

theorem totalExponent_mul_pow (m : Nat) (hm : 0 < m) (e : Int) (k : Nat) :
    totalExponent (m * 2 ^ k) (e - k) = totalExponent m e := by
  unfold totalExponent
  rw [log2_mul_pow m hm k]; push_cast; omega

/-- Rounding `m · 2^k · 2^(e - k)`, when `m · 2^e` is canonical, gives `m · 2^e` back. -/
theorem roundWithAccuracy_canonical (spec : Format) (s : Sign) (m : Nat) (hm : 0 < m) (e : Int)
    (k : Nat) (hc : spec.targetExponent (totalExponent m e) = e) :
    roundWithAccuracy spec s (m * 2 ^ k) (e - k) .exact = .finite s m e hm := by
  unfold roundWithAccuracy shiftToTargetExponent shiftToExponent
  simp only [totalExponent_mul_pow m hm e k, hc]
  have h1 : (e - (e - (k : Int))).toNat = k := by omega
  have h2 : (e - e).toNat = 0 := by omega
  simp only [h1, ExtendedMantissa.ofMantissaAndAccuracy, shift_mul_pow,
    ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy, Accuracy.roundToNearestEven]
  simp only [Int.sub_add_cancel, hc]
  have h3 : ((⟨m, false, false⟩ : ExtendedMantissa) >>> (e - e).toNat) = ⟨m, false, false⟩ := by
    rw [h2]; rfl
  split
  · rename_i h; rw [h3] at h; simp at h; omega
  · congr 1
    · rw [h3]
    · simp

/-- Every finite float that `unpack` produces is canonical. -/
theorem unpack_finite_canonical (spec : Format) (b : BitVec spec.numBits) (s : Sign) (m : Nat)
    (e : Int) (hm : 0 < m) (h : UnpackedFloat.unpack spec b = .finite s m e hm) :
    spec.targetExponent (totalExponent m e) = e := by
  have hP : 2 ≤ 2 ^ (spec.exponentBits - 1) := by
    have := spec.he
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (spec.exponentBits - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hmv := (unpackMantissa b).isLt
  have hPI : ((2:Int) ^ (spec.exponentBits - 1)) = ((2 ^ (spec.exponentBits - 1) : Nat) : Int) := by
    rw [Int.natCast_pow]; rfl
  unfold UnpackedFloat.unpack at h
  simp only at h
  split at h
  · split at h <;> cases h
  · split at h
    · split at h
      · cases h
      · cases h
        rename_i _ hz _
        have hl : (unpackMantissa b).toNat.log2 < spec.mantissaBitsWithoutImplicit :=
          (Nat.log2_lt (by omega)).2 hmv
        rw [hz]
        simp only [Format.targetExponent, Format.minExponent, Format.exponentBias,
          Format.mantissaBits, totalExponent, BitVec.toNat_ofNat, Nat.zero_mod, hPI]
        generalize 2 ^ (spec.exponentBits - 1) = P at *
        omega
    · cases h
      rename_i _ hnz
      have hE : (unpackExponent b).toNat ≠ 0 := by
        intro h0; apply hnz; exact BitVec.eq_of_toNat_eq (by simpa using h0)
      have happ : (1#1 ++ unpackMantissa b).toNat =
          2 ^ spec.mantissaBitsWithoutImplicit + (unpackMantissa b).toNat := by
        rw [BitVec.toNat_append, show (1#1).toNat = 1 from rfl, Nat.one_shiftLeft]
        have := Nat.two_pow_add_eq_or_of_lt hmv 1
        rw [Nat.mul_one] at this
        exact this.symm
      have hl : (1#1 ++ unpackMantissa b).toNat.log2 = spec.mantissaBitsWithoutImplicit := by
        rw [happ, Nat.log2_eq_iff
          (by have := Nat.two_pow_pos spec.mantissaBitsWithoutImplicit; omega)]
        constructor
        · omega
        · rw [Nat.pow_succ]; omega
      simp only [Format.targetExponent, Format.minExponent, Format.exponentBias,
        Format.mantissaBits, totalExponent, hl, hPI]
      generalize 2 ^ (spec.exponentBits - 1) = P at *
      omega

/-! ## The identities on unpacked floats -/

theorem sign_mul_positive (s : Sign) : s * Sign.positive = s := by cases s <;> rfl
theorem sign_positive_mul (s : Sign) : Sign.positive * s = s := by cases s <;> rfl
theorem sign_div_positive (s : Sign) : s / Sign.positive = s := by cases s <;> rfl

/-- `x · 1 = x`, `1` written `2^k · 2^(-k)`. -/
theorem mul_one (spec : Format) (b : BitVec spec.numBits) (k : Nat) (hk : 0 < 2 ^ k) :
    UnpackedFloat.mul spec (UnpackedFloat.unpack spec b) (.finite .positive (2 ^ k) (-(k : Int)) hk) =
      UnpackedFloat.unpack spec b := by
  generalize hu : UnpackedFloat.unpack spec b = u
  cases u with
  | notANumber => rfl
  | infinity s => simp [UnpackedFloat.mul, sign_mul_positive]
  | zero s => simp [UnpackedFloat.mul, sign_mul_positive]
  | finite s m e hm =>
    have hc := unpack_finite_canonical spec b s m e hm hu
    simp only [UnpackedFloat.mul, sign_mul_positive]
    rw [show e + -(k : Int) = e - (k : Int) by omega]
    exact roundWithAccuracy_canonical spec s m hm e k hc

/-- `1 · x = x`. -/
theorem one_mul (spec : Format) (b : BitVec spec.numBits) (k : Nat) (hk : 0 < 2 ^ k) :
    UnpackedFloat.mul spec (.finite .positive (2 ^ k) (-(k : Int)) hk) (UnpackedFloat.unpack spec b) =
      UnpackedFloat.unpack spec b := by
  generalize hu : UnpackedFloat.unpack spec b = u
  cases u with
  | notANumber => rfl
  | infinity s => simp [UnpackedFloat.mul, sign_positive_mul]
  | zero s => simp [UnpackedFloat.mul, sign_positive_mul]
  | finite s m e hm =>
    have hc := unpack_finite_canonical spec b s m e hm hu
    simp only [UnpackedFloat.mul, sign_positive_mul]
    rw [show -(k : Int) + e = e - (k : Int) by omega, Nat.mul_comm]
    exact roundWithAccuracy_canonical spec s m hm e k hc

/-- `x / 1 = x`. -/
theorem div_one (spec : Format) (b : BitVec spec.numBits) (k : Nat) (hk : 0 < 2 ^ k) :
    UnpackedFloat.div spec (UnpackedFloat.unpack spec b) (.finite .positive (2 ^ k) (-(k : Int)) hk) =
      UnpackedFloat.unpack spec b := by
  generalize hu : UnpackedFloat.unpack spec b = u
  cases u with
  | notANumber => rfl
  | infinity s => simp [UnpackedFloat.div, sign_div_positive]
  | zero s => simp [UnpackedFloat.div, sign_div_positive]
  | finite s m e hm =>
    have hc := unpack_finite_canonical spec b s m e hm hu
    have ht : totalExponent (2 ^ k) (-(k : Int)) = 1 := by
      unfold totalExponent; rw [Nat.log2_two_pow]; omega
    simp only [UnpackedFloat.div, divCore, ht, sign_div_positive]
    have hT : ∃ j : Nat, spec.targetExponent (totalExponent m e - 1) = e - j := by
      refine ⟨(e - spec.targetExponent (totalExponent m e - 1)).toNat, ?_⟩
      have := hc; simp only [Format.targetExponent] at this ⊢; omega
    obtain ⟨j, hj⟩ := hT
    rw [hj]
    have hmin : min (e - -(k : Int)) (e - j) = e - j := by omega
    rw [hmin]
    have hs : (e - -(k : Int) - (e - j)).toNat = j + k := by omega
    rw [hs, Nat.shiftLeft_eq, Nat.pow_add, ← Nat.mul_assoc, Nat.mul_div_cancel _ (Nat.two_pow_pos k),
      Nat.mul_mod_left]
    simp only [accuracyOfFraction, ite_true]
    exact roundWithAccuracy_canonical spec s m hm e j hc

/-- `x + 0 = x`, except for `x = -0`. -/
theorem add_zero (spec : Format) (u : UnpackedFloat) (h : u ≠ .zero .negative) :
    UnpackedFloat.add spec u (.zero .positive) = u := by
  cases u with
  | zero s => cases s <;> simp_all [UnpackedFloat.add]
  | _ => simp [UnpackedFloat.add]

/-- `0 + x = x`, except for `x = -0`. -/
theorem zero_add (spec : Format) (u : UnpackedFloat) (h : u ≠ .zero .negative) :
    UnpackedFloat.add spec (.zero .positive) u = u := by
  cases u with
  | zero s => cases s <;> simp_all [UnpackedFloat.add]
  | _ => simp [UnpackedFloat.add]

/-- `x - 0 = x`. -/
theorem sub_zero (spec : Format) (u : UnpackedFloat) :
    UnpackedFloat.sub spec u (.zero .positive) = u := by
  cases u with
  | zero s => cases s <;> rfl
  | _ => simp [UnpackedFloat.sub]

/-! ## `Float` -/

theorem Float.pack_unpack (m : Float.Model) : Float.Model.pack m.unpack = m := by
  cases m with
  | mk b v =>
    simp only [Float.Model.pack, Float.Model.unpack]
    congr 1
    apply UInt64.toBitVec_inj.mp
    simpa using pack_unpack_of_valid v

/-- The bits of `1.0`. -/
abbrev Float.oneBits : UInt64 := 0x3FF0000000000000

theorem Float.zero_unpack : (Float.ofBits 0).toModel.unpack = .zero .positive := rfl

theorem Float.one_unpack : (Float.ofBits Float.oneBits).toModel.unpack =
    .finite .positive (2 ^ 52) (-(52 : Nat)) (Nat.two_pow_pos 52) := rfl

theorem Float.unpack_ne_negZero (f : Float) (h : f ≠ (-0 : Float)) :
    f.toModel.unpack ≠ .zero .negative := by
  intro hu
  apply h
  rw [← _root_.Float.toBits_inj, ← UInt64.toBitVec_inj]
  exact (unpack_eq_zero_iff_of_valid f.toModel.valid).1 hu

theorem Float.mul_one (f : Float) : Float.mul f (Float.ofBits Float.oneBits) = f := by
  cases f with
  | ofModel m =>
  show _root_.Float.ofModel (Float.Model.pack
    (UnpackedFloat.mul _ m.unpack (_root_.Float.ofBits Float.oneBits).toModel.unpack)) = _
  rw [Float.one_unpack]
  congr 1
  conv => rhs; rw [← Float.pack_unpack m]
  congr 1
  exact FloatIdentities.mul_one _ _ 52 _

theorem Float.one_mul (f : Float) : Float.mul (Float.ofBits Float.oneBits) f = f := by
  cases f with
  | ofModel m =>
  show _root_.Float.ofModel (Float.Model.pack
    (UnpackedFloat.mul _ (_root_.Float.ofBits Float.oneBits).toModel.unpack m.unpack)) = _
  rw [Float.one_unpack]
  congr 1
  conv => rhs; rw [← Float.pack_unpack m]
  congr 1
  exact FloatIdentities.one_mul _ _ 52 _

theorem Float.div_one (f : Float) : Float.div f (Float.ofBits Float.oneBits) = f := by
  cases f with
  | ofModel m =>
  show _root_.Float.ofModel (Float.Model.pack
    (UnpackedFloat.div _ m.unpack (_root_.Float.ofBits Float.oneBits).toModel.unpack)) = _
  rw [Float.one_unpack]
  congr 1
  conv => rhs; rw [← Float.pack_unpack m]
  congr 1
  exact FloatIdentities.div_one _ _ 52 _

theorem Float.sub_zero (f : Float) : Float.sub f (Float.ofBits 0) = f := by
  cases f with
  | ofModel m =>
  show _root_.Float.ofModel (Float.Model.pack
    (UnpackedFloat.sub _ m.unpack (_root_.Float.ofBits 0).toModel.unpack)) = _
  rw [Float.zero_unpack, FloatIdentities.sub_zero, Float.pack_unpack]

theorem Float.add_zero (f : Float) (h : f ≠ (-0 : Float)) : Float.add f (Float.ofBits 0) = f := by
  have hu := Float.unpack_ne_negZero f h
  cases f with
  | ofModel m =>
  show _root_.Float.ofModel (Float.Model.pack
    (UnpackedFloat.add _ m.unpack (_root_.Float.ofBits 0).toModel.unpack)) = _
  rw [Float.zero_unpack, FloatIdentities.add_zero _ _ hu, Float.pack_unpack]

theorem Float.zero_add (f : Float) (h : f ≠ (-0 : Float)) : Float.add (Float.ofBits 0) f = f := by
  have hu := Float.unpack_ne_negZero f h
  cases f with
  | ofModel m =>
  show _root_.Float.ofModel (Float.Model.pack
    (UnpackedFloat.add _ (_root_.Float.ofBits 0).toModel.unpack m.unpack)) = _
  rw [Float.zero_unpack, FloatIdentities.zero_add _ _ hu, Float.pack_unpack]

/-! ## `Float32` -/

theorem Float32.pack_unpack (m : Float32.Model) : Float32.Model.pack m.unpack = m := by
  cases m with
  | mk b v =>
    simp only [Float32.Model.pack, Float32.Model.unpack]
    congr 1
    apply UInt32.toBitVec_inj.mp
    simpa using pack_unpack_of_valid v

/-- The bits of `1.0 : Float32`. -/
abbrev Float32.oneBits : UInt32 := 0x3F800000

theorem Float32.zero_unpack : (Float32.ofBits 0).toModel.unpack = .zero .positive := rfl

theorem Float32.one_unpack : (Float32.ofBits Float32.oneBits).toModel.unpack =
    .finite .positive (2 ^ 23) (-(23 : Nat)) (Nat.two_pow_pos 23) := rfl

theorem Float32.unpack_ne_negZero (f : Float32) (h : f ≠ (-0 : Float32)) :
    f.toModel.unpack ≠ .zero .negative := by
  intro hu
  apply h
  rw [← _root_.Float32.toBits_inj, ← UInt32.toBitVec_inj]
  exact (unpack_eq_zero_iff_of_valid f.toModel.valid).1 hu

theorem Float32.mul_one (f : Float32) : Float32.mul f (Float32.ofBits Float32.oneBits) = f := by
  cases f with
  | ofModel m =>
  show _root_.Float32.ofModel (Float32.Model.pack
    (UnpackedFloat.mul _ m.unpack (_root_.Float32.ofBits Float32.oneBits).toModel.unpack)) = _
  rw [Float32.one_unpack]
  congr 1
  conv => rhs; rw [← Float32.pack_unpack m]
  congr 1
  exact FloatIdentities.mul_one _ _ 23 _

theorem Float32.one_mul (f : Float32) : Float32.mul (Float32.ofBits Float32.oneBits) f = f := by
  cases f with
  | ofModel m =>
  show _root_.Float32.ofModel (Float32.Model.pack
    (UnpackedFloat.mul _ (_root_.Float32.ofBits Float32.oneBits).toModel.unpack m.unpack)) = _
  rw [Float32.one_unpack]
  congr 1
  conv => rhs; rw [← Float32.pack_unpack m]
  congr 1
  exact FloatIdentities.one_mul _ _ 23 _

theorem Float32.div_one (f : Float32) : Float32.div f (Float32.ofBits Float32.oneBits) = f := by
  cases f with
  | ofModel m =>
  show _root_.Float32.ofModel (Float32.Model.pack
    (UnpackedFloat.div _ m.unpack (_root_.Float32.ofBits Float32.oneBits).toModel.unpack)) = _
  rw [Float32.one_unpack]
  congr 1
  conv => rhs; rw [← Float32.pack_unpack m]
  congr 1
  exact FloatIdentities.div_one _ _ 23 _

theorem Float32.sub_zero (f : Float32) : Float32.sub f (Float32.ofBits 0) = f := by
  cases f with
  | ofModel m =>
  show _root_.Float32.ofModel (Float32.Model.pack
    (UnpackedFloat.sub _ m.unpack (_root_.Float32.ofBits 0).toModel.unpack)) = _
  rw [Float32.zero_unpack, FloatIdentities.sub_zero, Float32.pack_unpack]

theorem Float32.add_zero (f : Float32) (h : f ≠ (-0 : Float32)) :
    Float32.add f (Float32.ofBits 0) = f := by
  have hu := Float32.unpack_ne_negZero f h
  cases f with
  | ofModel m =>
  show _root_.Float32.ofModel (Float32.Model.pack
    (UnpackedFloat.add _ m.unpack (_root_.Float32.ofBits 0).toModel.unpack)) = _
  rw [Float32.zero_unpack, FloatIdentities.add_zero _ _ hu, Float32.pack_unpack]

theorem Float32.zero_add (f : Float32) (h : f ≠ (-0 : Float32)) :
    Float32.add (Float32.ofBits 0) f = f := by
  have hu := Float32.unpack_ne_negZero f h
  cases f with
  | ofModel m =>
  show _root_.Float32.ofModel (Float32.Model.pack
    (UnpackedFloat.add _ (_root_.Float32.ofBits 0).toModel.unpack m.unpack)) = _
  rw [Float32.zero_unpack, FloatIdentities.zero_add _ _ hu, Float32.pack_unpack]

end LeanScript.FloatIdentities
