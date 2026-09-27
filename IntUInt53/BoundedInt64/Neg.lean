import IntUInt53.BoundedInt64.Sub

/-!
# Negation and absolute value on `BoundedInt64`

Negation is the one unary operation that can leave the range: on an asymmetric
range such as `[-8, 7]` the negation of `-8` is not representable.  It
therefore comes in the same four variants as the binary operations, and so does
the absolute value:

* `checked_neg` / `checked_abs`         — `none` when the exact value is out of range;
* `overflowing_neg` / `overflowing_abs` — the wrapped value together with a flag;
* `wrapping_neg` / `wrapping_abs`       — reduction modulo the period;
* `saturating_neg` / `saturating_abs`   — the exact value, clamped to `[lo, hi]`.

Every statement is an equation between exact integers.
-/

set_option autoImplicit false

namespace BoundedInt64

variable {lo hi : Int64}

/-! ### The exact values -/

/-- The exact negation of the integer denoted by `a`. -/
def exactNeg (a : BoundedInt64 lo hi) : Int := -a.toInt

/-- The exact absolute value of the integer denoted by `a`. -/
def exactAbs (a : BoundedInt64 lo hi) : Int := a.toInt.natAbs

theorem exactAbs_eq (a : BoundedInt64 lo hi) :
    exactAbs a = if 0 ≤ a.toInt then a.toInt else -a.toInt := by
  unfold exactAbs
  split <;> omega

/-- Negation overflows when the negated value leaves the range. -/
def negOverflows (a : BoundedInt64 lo hi) : Prop := ¬ InRange lo hi (exactNeg a)

/-- The absolute value overflows when it leaves the range. -/
def absOverflows (a : BoundedInt64 lo hi) : Prop := ¬ InRange lo hi (exactAbs a)

instance (a : BoundedInt64 lo hi) : Decidable (negOverflows a) := by
  unfold negOverflows; infer_instance

instance (a : BoundedInt64 lo hi) : Decidable (absOverflows a) := by
  unfold absOverflows; infer_instance

theorem negOverflows_iff {a : BoundedInt64 lo hi} :
    negOverflows a ↔ (-a.toInt < lo.toInt ∨ hi.toInt < -a.toInt) := by
  unfold negOverflows InRange exactNeg; omega

/-! ### The checked variants -/

/-- Checked negation: `none` exactly when `-a` is out of range. -/
def checked_neg (a : BoundedInt64 lo hi) : Option (BoundedInt64 lo hi) :=
  ofInt? lo hi (exactNeg a)

/-- Checked absolute value: `none` exactly when `|a|` is out of range. -/
def checked_abs (a : BoundedInt64 lo hi) : Option (BoundedInt64 lo hi) :=
  ofInt? lo hi (exactAbs a)

theorem checked_neg_eq_some_iff {a c : BoundedInt64 lo hi} :
    checked_neg a = some c ↔ c.toInt = -a.toInt := ofInt?_eq_some_iff

theorem checked_abs_eq_some_iff {a c : BoundedInt64 lo hi} :
    checked_abs a = some c ↔ c.toInt = a.toInt.natAbs := ofInt?_eq_some_iff

/-- Exactness: whenever checked negation succeeds, its result is `-a`. -/
theorem toInt_of_checked_neg {a c : BoundedInt64 lo hi} (h : checked_neg a = some c) :
    c.toInt = -a.toInt := checked_neg_eq_some_iff.mp h

/-- Exactness: whenever the checked absolute value succeeds, it is `|a|`. -/
theorem toInt_of_checked_abs {a c : BoundedInt64 lo hi} (h : checked_abs a = some c) :
    c.toInt = a.toInt.natAbs := checked_abs_eq_some_iff.mp h

theorem checked_neg_eq_none_iff {a : BoundedInt64 lo hi} :
    checked_neg a = none ↔ negOverflows a := ofInt?_eq_none_iff

theorem checked_abs_eq_none_iff {a : BoundedInt64 lo hi} :
    checked_abs a = none ↔ absOverflows a := ofInt?_eq_none_iff

theorem checked_neg_of_not_overflows {a : BoundedInt64 lo hi} (h : ¬ negOverflows a) :
    ∃ c, checked_neg a = some c ∧ c.toInt = -a.toInt := by
  have hr : InRange lo hi (exactNeg a) := Decidable.of_not_not h
  exact ⟨ofIntMem lo hi (exactNeg a) hr.1 hr.2, ofInt?_of_inRange hr, by simp [exactNeg]⟩

theorem checked_abs_of_not_overflows {a : BoundedInt64 lo hi} (h : ¬ absOverflows a) :
    ∃ c, checked_abs a = some c ∧ c.toInt = a.toInt.natAbs := by
  have hr : InRange lo hi (exactAbs a) := Decidable.of_not_not h
  exact ⟨ofIntMem lo hi (exactAbs a) hr.1 hr.2, ofInt?_of_inRange hr, by simp [exactAbs]⟩

/-! ### The wrapping variants -/

/-- Wrapping negation: `-a` reduced modulo the period. -/
def wrapping_neg (a : BoundedInt64 lo hi) : BoundedInt64 lo hi :=
  ofIntWrap (lo_le_hi a) (exactNeg a)

/-- Wrapping absolute value: `|a|` reduced modulo the period. -/
def wrapping_abs (a : BoundedInt64 lo hi) : BoundedInt64 lo hi :=
  ofIntWrap (lo_le_hi a) (exactAbs a)

theorem toInt_wrapping_neg_of_not_overflows {a : BoundedInt64 lo hi} (h : ¬ negOverflows a) :
    (wrapping_neg a).toInt = -a.toInt :=
  ofIntWrap_of_inRange (lo_le_hi a) (Decidable.of_not_not h)

theorem toInt_wrapping_abs_of_not_overflows {a : BoundedInt64 lo hi} (h : ¬ absOverflows a) :
    (wrapping_abs a).toInt = a.toInt.natAbs :=
  ofIntWrap_of_inRange (lo_le_hi a) (Decidable.of_not_not h)

/-! ### The overflowing variants -/

/-- Overflowing negation: the wrapped value together with an overflow flag. -/
def overflowing_neg (a : BoundedInt64 lo hi) : BoundedInt64 lo hi × Bool :=
  (wrapping_neg a, decide (¬ InRange lo hi (exactNeg a)))

/-- Overflowing absolute value: the wrapped value together with an overflow flag. -/
def overflowing_abs (a : BoundedInt64 lo hi) : BoundedInt64 lo hi × Bool :=
  (wrapping_abs a, decide (¬ InRange lo hi (exactAbs a)))

@[simp] theorem overflowing_neg_fst (a : BoundedInt64 lo hi) :
    (overflowing_neg a).1 = wrapping_neg a := rfl

@[simp] theorem overflowing_abs_fst (a : BoundedInt64 lo hi) :
    (overflowing_abs a).1 = wrapping_abs a := rfl

theorem overflowing_neg_snd_iff {a : BoundedInt64 lo hi} :
    (overflowing_neg a).2 = true ↔ negOverflows a := by
  unfold overflowing_neg negOverflows; simp

theorem overflowing_abs_snd_iff {a : BoundedInt64 lo hi} :
    (overflowing_abs a).2 = true ↔ absOverflows a := by
  unfold overflowing_abs absOverflows; simp

/-! ### The saturating variants -/

/-- Saturating negation: `-a`, clamped to `[lo, hi]`. -/
def saturating_neg (a : BoundedInt64 lo hi) : BoundedInt64 lo hi :=
  ofIntSat (lo_le_hi a) (exactNeg a)

/-- Saturating absolute value: `|a|`, clamped to `[lo, hi]`. -/
def saturating_abs (a : BoundedInt64 lo hi) : BoundedInt64 lo hi :=
  ofIntSat (lo_le_hi a) (exactAbs a)

@[simp] theorem toInt_saturating_neg (a : BoundedInt64 lo hi) :
    (saturating_neg a).toInt = max lo.toInt (min (-a.toInt) hi.toInt) := by
  unfold saturating_neg exactNeg; rw [toInt_ofIntSat]

@[simp] theorem toInt_saturating_abs (a : BoundedInt64 lo hi) :
    (saturating_abs a).toInt = max lo.toInt (min (a.toInt.natAbs) hi.toInt) := by
  unfold saturating_abs exactAbs; rw [toInt_ofIntSat]

theorem toInt_saturating_neg_of_not_overflows {a : BoundedInt64 lo hi}
    (h : ¬ negOverflows a) : (saturating_neg a).toInt = -a.toInt :=
  ofIntSat_of_inRange (lo_le_hi a) (Decidable.of_not_not h)

theorem toInt_saturating_abs_of_not_overflows {a : BoundedInt64 lo hi}
    (h : ¬ absOverflows a) : (saturating_abs a).toInt = a.toInt.natAbs :=
  ofIntSat_of_inRange (lo_le_hi a) (Decidable.of_not_not h)

/-! ### Agreement of the four variants -/

/-- When `-a` is representable, all four variants of negation denote it. -/
theorem neg_variants_agree {a : BoundedInt64 lo hi} (h : ¬ negOverflows a) :
    (∃ c, checked_neg a = some c ∧ c.toInt = -a.toInt) ∧
      (wrapping_neg a).toInt = -a.toInt ∧
      (overflowing_neg a).1.toInt = -a.toInt ∧
      (overflowing_neg a).2 = false ∧
      (saturating_neg a).toInt = -a.toInt := by
  refine ⟨checked_neg_of_not_overflows h, toInt_wrapping_neg_of_not_overflows h,
    toInt_wrapping_neg_of_not_overflows h, ?_, toInt_saturating_neg_of_not_overflows h⟩
  cases hb : (overflowing_neg a).2 with
  | false => rfl
  | true => exact absurd (overflowing_neg_snd_iff.mp hb) h

/-- When `|a|` is representable, all four variants of the absolute value denote it. -/
theorem abs_variants_agree {a : BoundedInt64 lo hi} (h : ¬ absOverflows a) :
    (∃ c, checked_abs a = some c ∧ c.toInt = a.toInt.natAbs) ∧
      (wrapping_abs a).toInt = a.toInt.natAbs ∧
      (overflowing_abs a).1.toInt = a.toInt.natAbs ∧
      (overflowing_abs a).2 = false ∧
      (saturating_abs a).toInt = a.toInt.natAbs := by
  refine ⟨checked_abs_of_not_overflows h, toInt_wrapping_abs_of_not_overflows h,
    toInt_wrapping_abs_of_not_overflows h, ?_, toInt_saturating_abs_of_not_overflows h⟩
  cases hb : (overflowing_abs a).2 with
  | false => rfl
  | true => exact absurd (overflowing_abs_snd_iff.mp hb) h

/-! ### Laws -/

/-- On a range symmetric around zero negation never overflows. -/
theorem not_negOverflows_of_symm (hsym : lo.toInt = -hi.toInt) (a : BoundedInt64 lo hi) :
    ¬ negOverflows a := by
  rw [negOverflows_iff]
  have h₁ := lo_le_toInt a
  have h₂ := toInt_le_hi a
  omega

/-- On a range symmetric around zero the absolute value never overflows. -/
theorem not_absOverflows_of_symm (hsym : lo.toInt = -hi.toInt) (a : BoundedInt64 lo hi) :
    ¬ absOverflows a := by
  unfold absOverflows InRange exactAbs
  have h₁ := lo_le_toInt a
  have h₂ := toInt_le_hi a
  omega

/-- Negation is an involution wherever it does not overflow. -/
theorem checked_neg_checked_neg {a b c : BoundedInt64 lo hi}
    (h₁ : checked_neg a = some b) (h₂ : checked_neg b = some c) : c = a := by
  apply ext
  rw [toInt_of_checked_neg h₂, toInt_of_checked_neg h₁, Int.neg_neg]

end BoundedInt64
