module


@[expose] public section

set_option autoImplicit false

/-!
# Equality of floats against a finite non-zero literal

`Float` is a leaf of the language: its values are literals, and the instance
`instDecidableEqFloat` (which decides `a = b` by comparing the models, a projection of the leaf)
has no translation.  A `match` on float literals (`| 1.0 => …`) decides `x = 1.0` with it.

When one side is a finite non-zero float `c` (its model unpacks to `.finite`), the structural
equality `x = c` is the IEEE comparison `x == c` (`Float.beq`, the extern `lean_float_beq`,
`===` in JavaScript): the two differ only on the zeros (`0.0 == -0.0` but `0.0 ≠ -0.0`) and
on NaN (`NaN = NaN` but `!(NaN == NaN)`).  `#leanscript_to_term` (`trDecide`,
`LeanScript/TermElab/ToTerm/Expr/Calls.lean`) translates `decide (x = c)` as `x == c` for such
a `c`, and any other `x = y` as the comparison of the bit patterns `x.toBits = y.toBits`
(`Float.toBits` and `UInt64.decEq` are externs); this file proves each translation decides the
same as the original (`decide_float_eq_beq_of_finite`, `decide_float_eq_toBits`).
-/

namespace LeanScript.Gen

open Float.Model Float.Model.UnpackedFloat

/-- What a bit pattern unpacking to a finite number looks like: its sign, and either a normal
    number (a biased exponent other than `0` and all ones; the implicit leading `1`) or a
    subnormal one (the exponent `0`). -/
theorem unpack_eq_finite {b : BitVec Format.binary64.numBits} {s : Sign} {m : Nat} {e : Int}
    {h : 0 < m} (hb : unpack Format.binary64 b = .finite s m e h) :
    Sign.ofBitVec (unpackSign b) = s ∧
      ((unpackExponent b ≠ 0 ∧ m = 2 ^ 52 + (unpackMantissa b).toNat ∧
          e = ((unpackExponent b).toNat : Int) - 1075) ∨
        (unpackExponent b = 0 ∧ m = (unpackMantissa b).toNat)) := by
  unfold UnpackedFloat.unpack at hb
  simp only at hb
  split at hb
  · split at hb <;> cases hb
  · split at hb
    · split at hb
      · cases hb
      · cases hb
        exact ⟨rfl, Or.inr ⟨by assumption, rfl⟩⟩
    · cases hb
      refine ⟨rfl, Or.inl ⟨by assumption, ?_, rfl⟩⟩
      rw [BitVec.toNat_append]
      have hlt := (unpackMantissa (spec := Format.binary64) b).isLt
      simp only at hlt ⊢
      rw [Nat.shiftLeft_eq, show (1#1).toNat = 1 from rfl, Nat.one_mul]
      have := Nat.two_pow_add_eq_or_of_lt hlt 1
      rw [Nat.mul_one] at this
      exact this.symm

/-- A 64-bit pattern is its sign, exponent and mantissa. -/
theorem bits_eq_of_fields (b₁ b₂ : BitVec 64)
    (hs : b₁.extractLsb' 63 1 = b₂.extractLsb' 63 1)
    (hm : b₁.extractLsb' 0 52 = b₂.extractLsb' 0 52)
    (hx : b₁.extractLsb' 52 11 = b₂.extractLsb' 52 11) : b₁ = b₂ := by
  simp only [BitVec.toNat_eq, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] at *
  have := b₁.isLt
  have := b₂.isLt
  omega

/-- A finite number has one bit pattern. -/
theorem unpack_finite_inj {b₁ b₂ : BitVec Format.binary64.numBits} {s : Sign} {m : Nat}
    {e : Int} {h : 0 < m} (h₁ : unpack Format.binary64 b₁ = .finite s m e h)
    (h₂ : unpack Format.binary64 b₂ = .finite s m e h) : b₁ = b₂ := by
  obtain ⟨hs₁, hc₁⟩ := unpack_eq_finite h₁
  obtain ⟨hs₂, hc₂⟩ := unpack_eq_finite h₂
  have hsign : unpackSign b₁ = unpackSign b₂ := by
    rw [← hs₂] at hs₁
    unfold Sign.ofBitVec at hs₁
    revert hs₁
    generalize unpackSign b₁ = x
    generalize unpackSign b₂ = y
    intro hs
    split at hs <;> split at hs <;> (try cases hs) <;> bv_omega
  have hmant : unpackMantissa b₁ = unpackMantissa b₂ ∧ unpackExponent b₁ = unpackExponent b₂ := by
    have hl₁ := (unpackMantissa (spec := Format.binary64) b₁).isLt
    have hl₂ := (unpackMantissa (spec := Format.binary64) b₂).isLt
    simp only at hl₁ hl₂
    rcases hc₁ with ⟨hx₁, hm₁, he₁⟩ | ⟨hx₁, hm₁⟩ <;>
      rcases hc₂ with ⟨hx₂, hm₂, he₂⟩ | ⟨hx₂, hm₂⟩
    · refine ⟨BitVec.eq_of_toNat_eq (by omega), BitVec.eq_of_toNat_eq (by omega)⟩
    · omega
    · omega
    · exact ⟨BitVec.eq_of_toNat_eq (by omega), hx₁.trans hx₂.symm⟩
  obtain ⟨hm, hx⟩ := hmant
  exact bits_eq_of_fields b₁ b₂ hsign hm hx

/-- A float is equal to a finite float `c` exactly when it compares `==` to it. -/
theorem float_eq_iff_beq_of_finite (x c : Float) {s : Sign} {m : Nat} {e : Int} {h : 0 < m}
    (hc : c.toModel.unpack = .finite s m e h) : x = c ↔ (x == c) = true := by
  constructor
  · intro hxc
    rw [hxc]
    show UnpackedFloat.beq (Float.Model.unpack c.toModel) (Float.Model.unpack c.toModel) = true
    rw [hc]
    cases s <;> simp [UnpackedFloat.beq, UnpackedFloat.compare, Ordering.then, Ordering.swap]
  · intro hbeq
    change UnpackedFloat.beq (Float.Model.unpack x.toModel) (Float.Model.unpack c.toModel) = true
      at hbeq
    rw [hc] at hbeq
    have hx : x.toModel.unpack = .finite s m e h := by
      revert hbeq
      generalize x.toModel.unpack = u
      intro hbeq
      cases u with
      | notANumber => simp [UnpackedFloat.beq, UnpackedFloat.compare] at hbeq
      | infinity s' =>
        cases s <;> cases s' <;> simp [UnpackedFloat.beq, UnpackedFloat.compare] at hbeq
      | zero s' =>
        cases s <;> cases s' <;> simp [UnpackedFloat.beq, UnpackedFloat.compare] at hbeq
      | finite s' m' e' h' =>
        cases s <;> cases s' <;>
          simp [UnpackedFloat.beq, UnpackedFloat.compare, Ordering.then, Ordering.swap] at hbeq
        all_goals
          revert hbeq
          cases he : compare e' e <;> cases hm : compare m' m <;> simp
          cases Int.compare_eq_eq.mp he
          cases Nat.compare_eq_eq.mp hm
          exact ⟨rfl, rfl⟩
    have hbits := unpack_finite_inj hx hc
    rcases x with ⟨⟨xb, xv⟩⟩
    rcases c with ⟨⟨cb, cv⟩⟩
    have : xb = cb := UInt64.eq_of_toBitVec_eq hbits
    subst this
    rfl

/-- The translation of `x = c` on `Float`, for a finite non-zero `c`, decides the same as the
    original. -/
theorem decide_float_eq_beq_of_finite (x c : Float) {s : Sign} {m : Nat} {e : Int} {h : 0 < m}
    (hc : c.toModel.unpack = .finite s m e h) : decide (x = c) = (x == c) := by
  by_cases hxc : x = c
  · simp only [hxc, decide_true]
    exact ((float_eq_iff_beq_of_finite c c hc).1 rfl).symm
  · simp only [hxc, decide_false]
    cases hb : (x == c)
    · rfl
    · exact absurd ((float_eq_iff_beq_of_finite x c hc).2 hb) hxc

/-- Two floats are equal exactly when their bit patterns are. -/
theorem float_eq_iff_toBits_eq (x y : Float) : x = y ↔ x.toBits = y.toBits := by
  constructor
  · intro h
    rw [h]
  · intro h
    rcases x with ⟨⟨xb, xv⟩⟩
    rcases y with ⟨⟨yb, yv⟩⟩
    change xb = yb at h
    subst h
    rfl

/-- The translation of `x = y` on `Float` in general (a side that is not a finite non-zero
    literal: a zero, where `0.0 == -0.0`, or NaN, where `!(NaN == NaN)`): the comparison of the
    bit patterns, which decides the same as the original. -/
theorem decide_float_eq_toBits (x y : Float) :
    decide (x = y) = decide (x.toBits = y.toBits) := by
  simp only [float_eq_iff_toBits_eq]

end LeanScript.Gen

end
