module

public import HashableFloat.Identities

@[expose] public section

set_option autoImplicit false

/-!
# `(b - b) + (y + z) = ((b - b) + y) + z`, exactly

IEEE addition is not associative, but it is when the first operand is `b - b`: that is `+0`
(for a finite `b`) or `NaN` (`sub_self`), and `+0 + w` is `w` unless `w = -0`, which a sum
`y + z` is only when `y` and `z` are both `-0` (round to nearest: an exact cancellation gives
`+0`, and a sum never rounds a nonzero value to zero; `add_eq_negZero`).  Hence
`Float.sub_self_add_add`, bit for bit, for every `Float` (`NaN`, infinities and both zeros
included), in Lean's logical model of floats (`Float.Model`, `UnpackedFloat`).

The core fact is about rounding: a positive mantissa at an exponent from the format's least
one (`-1074` for `binary64`) up rounds to a *finite* float whose mantissa is below `2^53`
(`round_bounds`), and such a float is not packed into the bits of a zero
(`pack_finite_ne_zero`).

In the language's floats (`HashableFloat`, no `NaN` or `-0`), `b - b` is always `+0`
(`HashableFloat.toFloat_normalize_sub_self`).  The `Term` optimiser uses this to write
`(a - a) + (a + a)` as `a - a + a + a` in JavaScript (`LeanScript.Term.Optimize.FloatComm`).
-/

namespace LeanScript.FloatIdentities

open Float.Model UnpackedFloat


theorem shiftR_mantissa (k : Nat) : ∀ em : ExtendedMantissa,
    (em >>> k).mantissa = em.mantissa / 2 ^ k := by
  induction k with
  | zero => intro em; simp [HShiftRight.hShiftRight, Nat.repeat]
  | succ k ih =>
    intro em
    show (ExtendedMantissa.shiftRightOne (em >>> k)).mantissa = _
    simp only [ExtendedMantissa.shiftRightOne, ih, Nat.div_div_eq_div_mul, Nat.pow_succ]

theorem ofMantissaAndAccuracy_mantissa (m : Nat) (a : Accuracy) :
    (ExtendedMantissa.ofMantissaAndAccuracy m a).mantissa = m := by
  cases a with
  | exact => rfl
  | inexact o => cases o <;> rfl

theorem le_roundToNearestEven (m : Nat) (a : Accuracy) : m ≤ a.roundToNearestEven m := by
  cases a with
  | exact => exact Nat.le_refl _
  | inexact o => cases o <;> simp [Accuracy.roundToNearestEven] <;> omega

theorem binary64_targetExponent (t : Int) :
    Format.binary64.targetExponent t = max (t - 53) (-1074) := by
  simp only [Format.targetExponent]; rfl

/-- Shifting a positive mantissa to its target exponent keeps it positive and below `2^53`. -/
theorem shift_bounds (M : Nat) (hM : 0 < M) (E : Int) (hE : -1074 ≤ E) :
    0 < M / 2 ^ (Format.binary64.targetExponent (totalExponent M E) - E).toNat ∧
    M / 2 ^ (Format.binary64.targetExponent (totalExponent M E) - E).toNat < 2 ^ 53 := by
  rw [binary64_targetExponent]
  unfold totalExponent
  have h1 := Nat.log2_self_le (Nat.ne_of_gt hM)
  have h2 := @Nat.lt_log2_self M
  generalize M.log2 = L at *
  by_cases hL : 52 ≤ L
  · have hk : (max ((L : Int) + 1 + E - 53) (-1074) - E).toNat = L - 52 := by omega
    rw [hk]
    have hp : 2 ^ L = 2 ^ 52 * 2 ^ (L - 52) := by rw [← Nat.pow_add]; congr 1; omega
    have hq : 2 ^ (L + 1) = 2 ^ 53 * 2 ^ (L - 52) := by rw [← Nat.pow_add]; congr 1; omega
    constructor
    · apply Nat.div_pos _ (Nat.two_pow_pos _)
      calc 2 ^ (L - 52) ≤ 2 ^ 52 * 2 ^ (L - 52) := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
        _ = 2 ^ L := hp.symm
        _ ≤ M := h1
    · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← hq]; exact h2
  · have hk : (max ((L : Int) + 1 + E - 53) (-1074) - E).toNat = 0 := by omega
    rw [hk, Nat.pow_zero, Nat.div_one]
    refine ⟨hM, Nat.lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) (by omega))⟩

theorem roundWithAccuracy_bounds (s : Sign) (M : Nat) (hM : 0 < M) (E : Int) (hE : -1074 ≤ E)
    (acc : Accuracy) :
    ∃ F E' h, roundWithAccuracy Format.binary64 s M E acc = .finite s F E' h ∧ F < 2 ^ 53 ∧
      -1074 ≤ E' := by
  obtain ⟨b1, _⟩ := shift_bounds M hM E hE
  unfold roundWithAccuracy shiftToTargetExponent shiftToExponent
  simp only [shiftR_mantissa, ofMantissaAndAccuracy_mantissa]
  generalize hk : (Format.binary64.targetExponent (totalExponent M E) - E).toNat = k at *
  generalize hR : ExtendedMantissa.roundedMantissa _ = R
  have hR1 : 0 < R := by
    rw [← hR]; unfold ExtendedMantissa.roundedMantissa
    rw [shiftR_mantissa, ofMantissaAndAccuracy_mantissa]
    exact Nat.lt_of_lt_of_le b1 (le_roundToNearestEven _ _)
  obtain ⟨c1, c2⟩ := shift_bounds R hR1 (E + k) (by omega)
  split
  · rename_i h; omega
  · refine ⟨_, _, c1, rfl, c2, ?_⟩
    omega


theorem round_bounds (s : Sign) (M : Nat) (hM : 0 < M) (E : Int) (hE : -1074 ≤ E) :
    ∃ F E' h, round Format.binary64 s M E = .finite s F E' h ∧ F < 2 ^ 53 ∧ -1074 ≤ E' := by
  unfold round decreaseExponent
  simp only
  apply roundWithAccuracy_bounds
  · rw [Nat.shiftLeft_eq]; exact Nat.mul_pos hM (Nat.two_pow_pos _)
  · rw [binary64_targetExponent]; omega

theorem binary64_minExponent : Format.binary64.minExponent = -1074 := by decide

/-- A finite float with a mantissa below `2^53` and an exponent from `-1074` up is not packed
    into the bits of a zero. -/
theorem pack_finite_ne_zero (s s' : Sign) (F : Nat) (E : Int) (h : 0 < F) (hF : F < 2 ^ 53)
    (hE : -1074 ≤ E) :
    UnpackedFloat.pack Format.binary64 (.finite s F E h) ≠ packedZero Format.binary64 s' := by
  intro heq
  unfold UnpackedFloat.pack at heq
  simp only at heq
  split at heq
  · have := congrArg unpackExponent heq
    simp only [packedInfinity, packedZero, unpackExponent_packComponents] at this
    exact absurd this (by decide)
  · split at heq
    · have := congrArg unpackExponent heq
      simp only [packedZero, unpackExponent_packComponents] at this
      have h2 := congrArg BitVec.toNat this
      rename_i hb _
      have hbias : Format.binary64.exponentBias = 1023 := by decide
      rw [hbias] at h2 hb
      simp only [BitVec.toNat_ofNat] at h2
      change _ = (0 : Nat) at h2
      omega
    · have := congrArg unpackMantissa heq
      simp only [packedZero, unpackMantissa_packComponents] at this
      have h2 := congrArg BitVec.toNat this
      rename_i hl
      simp only [BitVec.toNat_ofNat] at h2
      change _ = (0 : Nat) at h2
      simp only [show Format.binary64.mantissaBits = 53 from rfl] at hl
      have hl2 : F.log2 < 53 := (Nat.log2_lt (by omega)).2 hF
      have hF2 : F < 2 ^ 52 := (Nat.log2_lt (by omega)).1 (by omega)
      rw [Nat.mod_eq_of_lt hF2] at h2
      omega


/-- The exponent of every finite float that `unpack` produces is at least `-1074`. -/
theorem unpack_exponent_ge (b : BitVec Format.binary64.numBits) (s : Sign) (m : Nat) (e : Int)
    (hm : 0 < m) (h : UnpackedFloat.unpack Format.binary64 b = .finite s m e hm) : -1074 ≤ e := by
  have := unpack_finite_canonical Format.binary64 b s m e hm h
  rw [binary64_targetExponent] at this
  omega

theorem pack_inf_ne_negZero (s : Sign) :
    UnpackedFloat.pack Format.binary64 (.infinity s) ≠ packedZero Format.binary64 .negative := by
  cases s <;> decide

theorem pack_nan_ne_negZero :
    UnpackedFloat.pack Format.binary64 .notANumber ≠ packedZero Format.binary64 .negative := by
  decide

theorem pack_zero_eq_negZero (s : Sign)
    (h : UnpackedFloat.pack Format.binary64 (.zero s) = packedZero Format.binary64 .negative) :
    s = .negative := by
  cases s
  · rfl
  · exact absurd h (by decide)

theorem round_ne_negZero (s : Sign) (M : Nat) (hM : 0 < M) (E : Int) (hE : -1074 ≤ E) :
    UnpackedFloat.pack Format.binary64 (round Format.binary64 s M E) ≠
      packedZero Format.binary64 .negative := by
  obtain ⟨F, E', hF, heq, b1, b2⟩ := round_bounds s M hM E hE
  rw [heq]
  exact pack_finite_ne_zero _ _ _ _ _ b1 b2

/-- **Only `-0 + -0` is `-0`** (round to nearest): a sum of two floats is packed into the bits
    of `-0` only when both are `-0`. -/
theorem add_eq_negZero (y z : Float.Model)
    (h : UnpackedFloat.pack Format.binary64 (UnpackedFloat.add Format.binary64 y.unpack z.unpack) =
      packedZero Format.binary64 .negative) :
    y.unpack = .zero .negative ∧ z.unpack = .zero .negative := by
  have cy := unpack_exponent_ge y.toBits.toBitVec
  have cz := unpack_exponent_ge z.toBits.toBitVec
  have vz := z.valid
  have pz := pack_unpack_of_valid vz
  have uz := @unpack_eq_zero_iff_of_valid _ Sign.negative _ vz
  have vy := y.valid
  have py := pack_unpack_of_valid vy
  have uy := @unpack_eq_zero_iff_of_valid _ Sign.negative _ vy
  simp only [Float.Model.unpack] at h ⊢
  generalize UnpackedFloat.unpack Format.binary64 y.toBits.toBitVec = yu at *
  generalize UnpackedFloat.unpack Format.binary64 z.toBits.toBitVec = zu at *
  cases yu <;> cases zu <;> simp only [UnpackedFloat.add] at h
  case notANumber.notANumber | notANumber.infinity | notANumber.zero | notANumber.finite
    | infinity.notANumber | zero.notANumber | finite.notANumber =>
    exact absurd h pack_nan_ne_negZero
  case infinity.zero | infinity.finite | zero.infinity | finite.infinity =>
    exact absurd h (pack_inf_ne_negZero _)
  case infinity.infinity =>
    split at h
    · exact absurd h (pack_inf_ne_negZero _)
    · exact absurd h pack_nan_ne_negZero
  case zero.zero =>
    split at h
    · rename_i hs
      have h1 := pack_zero_eq_negZero _ h
      subst h1
      have h2 := eq_of_beq hs
      subst h2
      exact ⟨rfl, rfl⟩
    · exact absurd (pack_zero_eq_negZero _ h) (by decide)
  case zero.finite =>
    rw [pz] at h; exact nomatch uz.2 h
  case finite.zero =>
    rw [py] at h; exact nomatch uy.2 h
  case finite.finite =>
    exfalso
    have e1 := cy _ _ _ _ rfl
    have e2 := cz _ _ _ _ rfl
    generalize (_ : Int) + _ = M at h
    unfold normalize at h
    split at h
    · rename_i hc
      have := Int.compare_eq_lt.mp hc
      exact round_ne_negZero _ _ (by omega) _ (by omega) h
    · exact absurd (pack_zero_eq_negZero _ h) (by decide)
    · rename_i hc
      have := Int.compare_eq_gt.mp hc
      exact round_ne_negZero _ _ (by omega) _ (by omega) h


/-- `x - x` is `+0` or `NaN`, for every float `x`. -/
theorem sub_self (spec : Format) (u : UnpackedFloat) :
    UnpackedFloat.sub spec u u = .zero .positive ∨ UnpackedFloat.sub spec u u = .notANumber := by
  cases u with
  | notANumber => right; rfl
  | infinity s => right; cases s <;> rfl
  | zero s => left; cases s <;> rfl
  | finite s m e hm =>
    left
    simp only [UnpackedFloat.sub, Int.sub_self, normalize]
    rfl

/-- `-0 + x = x`, except for `x = -0`. -/
theorem negZero_add (spec : Format) (u : UnpackedFloat) (h : u ≠ .zero .negative) :
    UnpackedFloat.add spec (.zero .negative) u = u := by
  cases u with
  | zero s => cases s <;> simp_all [UnpackedFloat.add]
  | _ => simp [UnpackedFloat.add]

theorem unpack_pack_ne_negZero (y z : Float.Model) (hy : y.unpack ≠ .zero .negative) :
    (Float.Model.pack (UnpackedFloat.add Format.binary64 y.unpack z.unpack)).unpack ≠
      .zero .negative := by
  intro h
  apply hy
  apply (add_eq_negZero y z _).1
  exact (unpack_eq_zero_iff_of_valid valid_pack).1 h

/-- **`(b - b) + (y + z) = ((b - b) + y) + z`**, exactly (bit for bit), for every `Float`s `b`,
    `y`, `z`: `b - b` is `+0` or `NaN` (`sub_self`), and `+0 + w = w` unless `w = -0`, which a
    sum is only when both operands are `-0` (`add_eq_negZero`). -/
theorem Float.sub_self_add_add (b y z : Float) :
    Float.add (Float.sub b b) (Float.add y z) = Float.add (Float.add (Float.sub b b) y) z := by
  cases b with | ofModel mb =>
  cases y with | ofModel my =>
  cases z with | ofModel mz =>
  show _root_.Float.ofModel (Float.Model.pack (UnpackedFloat.add _
      (Float.Model.pack (UnpackedFloat.sub _ mb.unpack mb.unpack)).unpack
      (Float.Model.pack (UnpackedFloat.add _ my.unpack mz.unpack)).unpack)) =
    _root_.Float.ofModel (Float.Model.pack (UnpackedFloat.add _
      (Float.Model.pack (UnpackedFloat.add _
        (Float.Model.pack (UnpackedFloat.sub _ mb.unpack mb.unpack)).unpack my.unpack)).unpack
      mz.unpack))
  congr 1
  rcases sub_self Format.binary64 mb.unpack with hx | hx <;> rw [hx]
  · have u0 : (Float.Model.pack (.zero .positive)).unpack = .zero .positive := rfl
    rw [u0]
    by_cases hy : my.unpack = .zero .negative
    · have hpn : UnpackedFloat.add Format.binary64 (.zero .positive) (.zero .negative) =
          .zero .positive := rfl
      rw [hy, hpn, u0]
      by_cases hz : mz.unpack = .zero .negative
      · rw [hz]; rfl
      · rw [negZero_add _ _ hz, Float.pack_unpack]
    · rw [FloatIdentities.zero_add _ _ hy, Float.pack_unpack,
        FloatIdentities.zero_add _ _ (unpack_pack_ne_negZero my mz hy), Float.pack_unpack]
  · have un : (Float.Model.pack .notANumber).unpack = .notANumber := rfl
    simp only [un, UnpackedFloat.add]


/-- `f - f` is `+0` or `NaN`, for every `Float` `f`. -/
theorem Float.sub_self_cases (f : Float) :
    Float.sub f f = Float.ofBits 0 ∨ Float.sub f f = Float.nan := by
  cases f with | ofModel m =>
  show _root_.Float.ofModel (Float.Model.pack (UnpackedFloat.sub _ m.unpack m.unpack)) = _ ∨
    _root_.Float.ofModel (Float.Model.pack (UnpackedFloat.sub _ m.unpack m.unpack)) = _
  rcases sub_self Format.binary64 m.unpack with h | h <;> rw [h]
  · left; rfl
  · right; rfl

end LeanScript.FloatIdentities

/-- In the language's floats, `f - f` is `+0`. -/
theorem HashableFloat.toFloat_normalize_sub_self (f : Float) :
    (HashableFloat.normalize (Float.sub f f)).toFloat = Float.ofBits 0 := by
  rcases LeanScript.FloatIdentities.Float.sub_self_cases f with h | h <;> rw [h]
  · exact HashableFloat.toFloat_normalize_of_ne (by decide) (by decide)
  · simp only [HashableFloat.normalize, ↓reduceDIte]; rfl
