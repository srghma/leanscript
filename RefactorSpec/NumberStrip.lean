module

public import JsTerm.Syntax.NumberLit

@[expose] public section

set_option autoImplicit false

/-!
# The removed `NumberForm`, and why its digits are those of `JSNumber.normalize`

`Legacy` is the `number` literal code as it was before `NumberForm` was reduced to
`int | float (u : UnpackedFloat)`: its own `nan`/`infinity`/`negZero` constructors, and its own
removal of trailing zeros (`Legacy.stripZeros`, at most 400 of them).

The facts proved here:
* `Legacy.stripZeros_eq`: on a positive mantissa with fewer than 400 trailing zeros the old
  removal of trailing zeros is `JSNumber.stripZeros`, the one of the JavaScript trees;
* `shortestDecimal_digits_ok`: the digits `shortestDecimal m e` finds for a mantissa
  `0 < m < 2 ^ 53` are positive and have fewer than 400 trailing zeros;
* `unpack_mantissa_lt`: the mantissa of an unpacked IEEE float is below `2 ^ 53` (`2 ^ 24` for a
  `Float32`).
-/

namespace MoreJs.Legacy

open Float.Model (UnpackedFloat)
open Float.Model.UnpackedFloat (Sign)

/-- The removed form of a `number`. -/
inductive NumberForm where
  | nan
  | infinity (neg : Bool)
  | negZero
  | int (n : Int)
  | decimal (neg : Bool) (digits : Nat) (exponent : Int)
  deriving Inhabited, Repr, BEq, DecidableEq

/-- The removed `signIsNeg`. -/
def signIsNeg : Sign → Bool
  | .negative => true
  | .positive => false

/-- The removed removal of trailing zeros. -/
def stripGo : Nat → Nat → Int → Nat × Int
  | 0, d, ex => (d, ex)
  | fuel + 1, d, ex => if d != 0 && d % 10 == 0 then stripGo fuel (d / 10) (ex + 1) else (d, ex)

/-- The removed `NumberForm.ofUnpacked.stripZeros`. -/
def stripZeros (p : Nat × Int) : Nat × Int := stripGo 400 p.1 p.2

/-- The removed `NumberForm.ofUnpacked`. -/
def ofUnpacked : UnpackedFloat → NumberForm
  | .notANumber => .nan
  | .infinity s => .infinity (signIsNeg s)
  | .zero s => if signIsNeg s then .negZero else .int 0
  | .finite s m e _ =>
    match MoreJs.NumberForm.smallNat? m e with
    | some v => .int (if signIsNeg s then -(v : Int) else v)
    | none =>
      let (d, ex) := stripZeros (shortestDecimal m e)
      .decimal (signIsNeg s) d ex

/-- The removed `NumberForm.ofFloat`. -/
def ofFloat (f : Float) : NumberForm := ofUnpacked f.toModel.unpack

/-- The removed `NumberForm.ofFloat32`. -/
def ofFloat32 (f : Float32) : NumberForm := ofUnpacked f.toModel.unpack

end MoreJs.Legacy

namespace MoreJs.RefactorSpec

-- `10 ^ 400` (the fuel of the removed code) is above the default size up to which numerals are
-- evaluated.
set_option exponentiation.threshold 512

open Language.JavaScript (JSNumber)
open Float.Model (UnpackedFloat)

/-- The old loop is the loop of `JSNumber` on a positive mantissa. -/
theorem stripGo_eq_aux : ∀ (F d : Nat) (ex : Int), 0 < d →
    Legacy.stripGo F d ex = JSNumber.stripZerosAux F d ex := by
  intro F
  induction F with
  | zero => intro d ex _; rfl
  | succ F ih =>
    intro d ex hd
    simp only [Legacy.stripGo, JSNumber.stripZerosAux]
    by_cases h : d % 10 = 0
    · have : 0 < d / 10 := by omega
      simp [h, Nat.pos_iff_ne_zero.mp hd, ih _ _ this]
    · simp [h]

/-- Once the fuel covers the trailing zeros, more fuel changes nothing. -/
theorem aux_fuel_indep : ∀ (F G d : Nat) (ex : Int), 0 < d → ¬ 10 ^ F ∣ d → F ≤ G →
    JSNumber.stripZerosAux F d ex = JSNumber.stripZerosAux G d ex := by
  intro F
  induction F with
  | zero => intro G d ex _ h; simp at h
  | succ F ih =>
    intro G d ex hd hdv hFG
    obtain ⟨G, rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    simp only [JSNumber.stripZerosAux]
    by_cases h : d % 10 = 0
    · have h1 : 0 < d / 10 := by omega
      have h2 : ¬ 10 ^ F ∣ d / 10 := by
        intro ⟨c, hc⟩
        apply hdv
        refine ⟨c, ?_⟩
        have := Nat.div_add_mod d 10
        rw [h, hc, Nat.add_zero] at this
        rw [← this, Nat.pow_succ, Nat.mul_left_comm, Nat.mul_assoc]
      simp [h, ih G _ _ h1 h2 (by omega)]
    · simp [h]

/-- The old removal of trailing zeros is the one of `JSNumber`, on a positive mantissa with
    fewer than 400 trailing zeros. -/
theorem Legacy.stripZeros_eq (d : Nat) (ex : Int) (hd : 0 < d) (h : ¬ 10 ^ 400 ∣ d) :
    Legacy.stripZeros (d, ex) = JSNumber.stripZeros d ex := by
  have hself : ¬ 10 ^ d ∣ d := fun hdv =>
    Nat.lt_irrefl d (Nat.lt_of_lt_of_le (Nat.lt_pow_self (by decide)) (Nat.le_of_dvd hd hdv))
  simp only [Legacy.stripZeros, JSNumber.stripZeros, stripGo_eq_aux _ _ _ hd]
  have : (d == 0) = false := by simp; omega
  rw [this]
  simp only [Bool.false_eq_true, ite_false]
  by_cases h4 : 400 ≤ d
  · exact aux_fuel_indep _ _ _ _ hd h h4
  · exact (aux_fuel_indep _ _ _ _ hd hself (by omega)).symm

/-- A two-way `if` has a property of its first component when both branches have it. -/
theorem ite_fst {c : Prop} [Decidable c] {a b : Nat × Int} (P : Nat → Prop) (ha : P a.1)
    (hb : P b.1) : P (if c then a else b).1 := by
  split <;> assumption

/-- The digits the search of `shortestDecimal` finds are the exact digits `D`, or a positive
    number of at most 20 digits. -/
theorem go_ok (D K : Nat) (exact : Float) (L : Nat) (hD1 : 10 ^ (L - 1) ≤ D) (hD2 : D < 10 ^ L) :
    ∀ fuel k, 1 ≤ k → k + fuel ≤ 21 →
      (shortestDecimal.go D K exact L fuel k).1 = D ∨
      (0 < (shortestDecimal.go D K exact L fuel k).1 ∧
        (shortestDecimal.go D K exact L fuel k).1 ≤ 10 ^ 20) := by
  intro fuel
  induction fuel with
  | zero => intro k _ _; left; simp [shortestDecimal.go]
  | succ fuel ih =>
    intro k hk hkf
    rw [shortestDecimal.go]
    by_cases hkL : k ≥ L
    · simp [hkL]
    · simp only [hkL, ite_false]
      have hq1 : 1 ≤ D / 10 ^ (L - k) := by
        rw [Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))]
        exact Nat.le_trans (by rw [Nat.one_mul]; exact Nat.pow_le_pow_right (by decide) (by omega)) hD1
      have hq2 : D / 10 ^ (L - k) < 10 ^ k := by
        rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide)), ← Nat.pow_add]
        have : k + (L - k) = L := by omega
        rw [this]; exact hD2
      have hk20 : 10 ^ k ≤ 10 ^ 20 := Nat.pow_le_pow_right (by decide) (by omega)
      refine ite_fst (fun x => x = D ∨ (0 < x ∧ x ≤ 10 ^ 20)) ?_ (ih (k + 1) (by omega) (by omega))
      right
      dsimp only
      split <;> omega

/-- If `a` and `b` are coprime and `0 < m < a ^ n`, then `(a * b) ^ n` does not divide
    `m * b ^ t`. -/
theorem not_dvd_mul_pow {a b m t n : Nat} (hab : Nat.Coprime a b) (hm : 0 < m) (hlt : m < a ^ n)
    (h : (a * b) ^ n ∣ m * b ^ t) : False := by
  have h1 : a ^ n ∣ m * b ^ t := Nat.dvd_trans ⟨b ^ n, (Nat.mul_pow a b n)⟩ h
  have h2 : a ^ n ∣ m := (Nat.Coprime.pow n t hab).dvd_of_dvd_mul_right h1
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt (Nat.le_of_dvd hm h2))

/-- A positive `D` has `(toString D).length` decimal digits. -/
theorem digits_bounds (D : Nat) (hD : 0 < D) :
    10 ^ ((toString D).length - 1) ≤ D ∧ D < 10 ^ (toString D).length := by
  rw [Nat.toString_eq_repr]
  have hpos := @Nat.length_repr_pos D
  refine ⟨?_, (Nat.length_repr_le_iff hpos).mp (Nat.le_refl _)⟩
  by_cases h1 : D.repr.length = 1
  · rw [h1]; show 1 ≤ D; exact hD
  · refine Nat.le_of_not_lt fun hlt => ?_
    have := (Nat.length_repr_le_iff (n := D) (k := D.repr.length - 1) (by omega)).mpr hlt
    omega

/-- The digits `shortestDecimal` finds for a mantissa `0 < m < 2 ^ 53` are positive and have
    fewer than 400 trailing zeros. -/
theorem shortestDecimal_digits_ok (m : Nat) (e : Int) (hm : 0 < m) (hm' : m < 2 ^ 53) :
    0 < (shortestDecimal m e).1 ∧ ¬ 10 ^ 400 ∣ (shortestDecimal m e).1 := by
  have key : ∀ D K, 0 < D → ¬ 10 ^ 400 ∣ D →
      0 < (shortestDecimal.go D K (Float.ofScientific D true K) (toString D).length 20 1).1 ∧
      ¬ 10 ^ 400 ∣ (shortestDecimal.go D K (Float.ofScientific D true K) (toString D).length 20 1).1 := by
    intro D K hD hD'
    obtain ⟨h1, h2⟩ := digits_bounds D hD
    rcases go_ok D K (Float.ofScientific D true K) _ h1 h2 20 1 (by decide) (by decide) with h | ⟨h3, h4⟩
    · rw [h]; exact ⟨hD, hD'⟩
    · refine ⟨h3, fun hdv => ?_⟩
      have := Nat.le_of_dvd h3 hdv
      have : (10:Nat) ^ 20 < 10 ^ 400 := Nat.pow_lt_pow_right (by decide) (by decide)
      omega
  unfold shortestDecimal
  by_cases he : e ≥ 0
  · simp only [he, ite_true]
    apply key
    · exact Nat.mul_pos hm (Nat.pow_pos (by decide))
    · intro h
      refine not_dvd_mul_pow (a := 5) (b := 2) (t := e.toNat) (n := 400) (by decide) hm
        (Nat.lt_of_lt_of_le hm' (by decide)) ?_
      rw [show (5 * 2 : Nat) = 10 from rfl]; exact h
  · simp only [he, ite_false]
    apply key
    · exact Nat.mul_pos hm (Nat.pow_pos (by decide))
    · intro h
      refine not_dvd_mul_pow (a := 2) (b := 5) (t := e.natAbs) (n := 400) (by decide) hm
        (Nat.lt_of_lt_of_le hm' (Nat.pow_le_pow_right (by decide) (by decide))) ?_
      rw [show (2 * 5 : Nat) = 10 from rfl]; exact h

/-- The value `smallNat?` finds for a positive mantissa is positive. -/
theorem smallNat?_pos {m v : Nat} {e : Int} (hm : 0 < m)
    (h : NumberForm.smallNat? m e = some v) : 0 < v := by
  unfold NumberForm.smallNat? at h
  by_cases he : e ≥ 0
  · simp only [he, ite_true] at h
    split at h <;> cases h
    exact Nat.mul_pos hm (Nat.pow_pos (by decide))
  · simp only [he, ite_false] at h
    by_cases hd : m % 2 ^ e.natAbs = 0
    · simp only [hd, BEq.rfl, ite_true] at h
      split at h <;> cases h
      exact Nat.div_pos (Nat.le_of_dvd hm (Nat.dvd_of_mod_eq_zero hd)) (Nat.pow_pos (by decide))
    · simp [hd] at h

/-- The value `smallNat?` finds is at most `2 ^ 53`. -/
theorem smallNat?_le {m v : Nat} {e : Int} (h : NumberForm.smallNat? m e = some v) :
    v ≤ 2 ^ 53 := by
  have key : ∀ o : Option Nat,
      (match o with
        | some v => if v ≤ 2 ^ 53 then some v else none
        | none => none) = some v → v ≤ 2 ^ 53 := by
    intro o ho
    cases o with
    | none => cases ho
    | some w =>
      simp only at ho
      split at ho
      · cases ho; assumption
      · cases ho
  exact key _ h

/-- The mantissa of an unpacked float is below `2 ^ (mantissa bits + 1)`. -/
theorem unpack_mantissa_lt (spec : Float.Model.Format) (b : BitVec spec.numBits)
    {s : UnpackedFloat.Sign} {m : Nat} {e : Int} {h : 0 < m}
    (hu : UnpackedFloat.unpack spec b = .finite s m e h) :
    m < 2 ^ (spec.mantissaBitsWithoutImplicit + 1) := by
  unfold UnpackedFloat.unpack at hu
  simp only at hu
  split at hu
  · split at hu <;> cases hu
  · split at hu
    · split at hu
      · cases hu
      · cases hu
        have := (UnpackedFloat.unpackMantissa b).isLt
        rw [Nat.pow_succ]; omega
    · cases hu
      exact Nat.lt_of_lt_of_eq (1#1 ++ UnpackedFloat.unpackMantissa b).isLt (by rw [Nat.add_comm])

/-- The mantissa of a double is below `2 ^ 53`. -/
theorem float_mantissa_lt (f : Float) {s : UnpackedFloat.Sign} {m : Nat} {e : Int} {h : 0 < m}
    (hu : f.toModel.unpack = .finite s m e h) : m < 2 ^ 53 := by
  have h1 := unpack_mantissa_lt _ _ hu
  have : Float.Model.Format.binary64.mantissaBitsWithoutImplicit = 52 := by decide
  rw [this] at h1; exact h1

/-- The mantissa of a `Float32` is below `2 ^ 24`, so below `2 ^ 53`. -/
theorem float32_mantissa_lt (f : Float32) {s : UnpackedFloat.Sign} {m : Nat} {e : Int}
    {h : 0 < m} (hu : f.toModel.unpack = .finite s m e h) : m < 2 ^ 53 := by
  have h1 := unpack_mantissa_lt _ _ hu
  have : Float.Model.Format.binary32.mantissaBitsWithoutImplicit = 23 := by decide
  rw [this] at h1; exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) (by decide))

end MoreJs.RefactorSpec

end
