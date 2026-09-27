import IntUInt53.BoundedInt64.Mul

/-!
# Division and remainder on `BoundedInt64`

Division here truncates towards zero, i.e. it is `Int.tdiv` / `Int.tmod`, the
convention of the machine integer types (and of Rust): `(-7) / 2 = -3` and
`(-7) % 2 = -1`, so the remainder has the sign of the dividend.

Two things can go wrong, and the variants differ only in how they report them:

* the divisor is `0`;
* the exact quotient (or remainder) leaves `[lo, hi]`.  Both are always bounded
  in absolute value by the dividend — `|a.tdiv b| ≤ |a|` and `|a.tmod b| ≤ |a|`
  — so this can only happen for a range that is not symmetric around `0`; in
  particular it never happens on `Int53`.

Every statement below is an equation between exact integers.
-/

set_option autoImplicit false

namespace BoundedInt64

variable {lo hi : Int64}

/-! ### The exact quotient and remainder -/

/-- The exact quotient, truncating towards zero (`0` if the divisor is `0`). -/
def exactDiv (a b : BoundedInt64 lo hi) : Int := a.toInt.tdiv b.toInt

/-- The exact remainder, with the sign of the dividend (`a` if the divisor is `0`). -/
def exactMod (a b : BoundedInt64 lo hi) : Int := a.toInt.tmod b.toInt

/-- The defining property of division with remainder. -/
theorem mul_exactDiv_add_exactMod (a b : BoundedInt64 lo hi) :
    b.toInt * exactDiv a b + exactMod a b = a.toInt :=
  Int.mul_tdiv_add_tmod a.toInt b.toInt

/-- The quotient is no larger in absolute value than the dividend. -/
theorem natAbs_exactDiv_le (a b : BoundedInt64 lo hi) :
    (exactDiv a b).natAbs ≤ a.toInt.natAbs :=
  Int.natAbs_tdiv_le_natAbs _ _

/-- The remainder is no larger in absolute value than the dividend. -/
theorem natAbs_exactMod_le (a b : BoundedInt64 lo hi) :
    (exactMod a b).natAbs ≤ a.toInt.natAbs := by
  unfold exactMod
  rw [Int.natAbs_tmod]
  exact Nat.mod_le _ _

/-- The remainder is smaller in absolute value than a nonzero divisor. -/
theorem natAbs_exactMod_lt {a b : BoundedInt64 lo hi} (h : b.toInt ≠ 0) :
    (exactMod a b).natAbs < b.toInt.natAbs := by
  unfold exactMod
  rw [Int.natAbs_tmod]
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero (fun hb => h (Int.natAbs_eq_zero.mp hb)))

/-! ### Failure -/

/-- Division fails when the divisor is zero or when the exact quotient leaves the range. -/
def divFails (a b : BoundedInt64 lo hi) : Prop :=
  b.toInt = 0 ∨ ¬ InRange lo hi (exactDiv a b)

/-- The remainder fails when the divisor is zero or when the exact remainder
leaves the range. -/
def modFails (a b : BoundedInt64 lo hi) : Prop :=
  b.toInt = 0 ∨ ¬ InRange lo hi (exactMod a b)

instance (a b : BoundedInt64 lo hi) : Decidable (divFails a b) := by
  unfold divFails; infer_instance

instance (a b : BoundedInt64 lo hi) : Decidable (modFails a b) := by
  unfold modFails; infer_instance

/-- On a range symmetric around zero nothing but a zero divisor can make
division fail. -/
theorem divFails_iff_of_symm (hsym : lo.toInt = -hi.toInt) (a b : BoundedInt64 lo hi) :
    divFails a b ↔ b.toInt = 0 := by
  unfold divFails InRange
  constructor
  · rintro (h | h)
    · exact h
    · refine absurd ?_ h
      have hle : (exactDiv a b).natAbs ≤ a.toInt.natAbs := natAbs_exactDiv_le a b
      have h₁ := lo_le_toInt a
      have h₂ := toInt_le_hi a
      omega
  · intro h; exact Or.inl h

/-- On a range symmetric around zero nothing but a zero divisor can make the
remainder fail. -/
theorem modFails_iff_of_symm (hsym : lo.toInt = -hi.toInt) (a b : BoundedInt64 lo hi) :
    modFails a b ↔ b.toInt = 0 := by
  unfold modFails InRange
  constructor
  · rintro (h | h)
    · exact h
    · refine absurd ?_ h
      have hle : (exactMod a b).natAbs ≤ a.toInt.natAbs := natAbs_exactMod_le a b
      have h₁ := lo_le_toInt a
      have h₂ := toInt_le_hi a
      omega
  · intro h; exact Or.inl h

/-! ### The checked variants -/

/-- Checked division: `none` on a zero divisor or when the quotient is out of range. -/
def checked_div (a b : BoundedInt64 lo hi) : Option (BoundedInt64 lo hi) :=
  if b.toInt = 0 then none else ofInt? lo hi (exactDiv a b)

/-- Checked remainder: `none` on a zero divisor or when the remainder is out of range. -/
def checked_mod (a b : BoundedInt64 lo hi) : Option (BoundedInt64 lo hi) :=
  if b.toInt = 0 then none else ofInt? lo hi (exactMod a b)

theorem checked_div_eq_some_iff {a b c : BoundedInt64 lo hi} :
    checked_div a b = some c ↔ (b.toInt ≠ 0 ∧ c.toInt = a.toInt.tdiv b.toInt) := by
  unfold checked_div
  split
  · next h => simp_all
  · next h =>
    constructor
    · intro hs; exact ⟨h, ofInt?_eq_some_iff.mp hs⟩
    · intro hv; exact ofInt?_eq_some_iff.mpr hv.2

theorem checked_mod_eq_some_iff {a b c : BoundedInt64 lo hi} :
    checked_mod a b = some c ↔ (b.toInt ≠ 0 ∧ c.toInt = a.toInt.tmod b.toInt) := by
  unfold checked_mod
  split
  · next h => simp_all
  · next h =>
    constructor
    · intro hs; exact ⟨h, ofInt?_eq_some_iff.mp hs⟩
    · intro hv; exact ofInt?_eq_some_iff.mpr hv.2

/-- Exactness: whenever checked division succeeds, its result is the exact quotient. -/
theorem toInt_of_checked_div {a b c : BoundedInt64 lo hi} (h : checked_div a b = some c) :
    c.toInt = a.toInt.tdiv b.toInt := (checked_div_eq_some_iff.mp h).2

/-- Exactness: whenever the checked remainder succeeds, its result is exact. -/
theorem toInt_of_checked_mod {a b c : BoundedInt64 lo hi} (h : checked_mod a b = some c) :
    c.toInt = a.toInt.tmod b.toInt := (checked_mod_eq_some_iff.mp h).2

theorem checked_div_eq_none_iff {a b : BoundedInt64 lo hi} :
    checked_div a b = none ↔ divFails a b := by
  unfold checked_div divFails
  split
  · next h => simp [h]
  · next h => rw [ofInt?_eq_none_iff]; simp [h]

theorem checked_mod_eq_none_iff {a b : BoundedInt64 lo hi} :
    checked_mod a b = none ↔ modFails a b := by
  unfold checked_mod modFails
  split
  · next h => simp [h]
  · next h => rw [ofInt?_eq_none_iff]; simp [h]

/-- Checked division succeeds, with the exact quotient, whenever it does not fail. -/
theorem checked_div_of_not_fails {a b : BoundedInt64 lo hi} (h : ¬ divFails a b) :
    ∃ c, checked_div a b = some c ∧ c.toInt = a.toInt.tdiv b.toInt := by
  unfold divFails at h
  have hb : b.toInt ≠ 0 := fun hz => h (Or.inl hz)
  have hr : InRange lo hi (exactDiv a b) := Decidable.of_not_not (fun hc => h (Or.inr hc))
  refine ⟨ofIntMem lo hi (exactDiv a b) hr.1 hr.2, ?_, by simp [exactDiv]⟩
  unfold checked_div
  rw [ite_eq_right hb]
  exact ofInt?_of_inRange hr

/-- The checked remainder succeeds, exactly, whenever it does not fail. -/
theorem checked_mod_of_not_fails {a b : BoundedInt64 lo hi} (h : ¬ modFails a b) :
    ∃ c, checked_mod a b = some c ∧ c.toInt = a.toInt.tmod b.toInt := by
  unfold modFails at h
  have hb : b.toInt ≠ 0 := fun hz => h (Or.inl hz)
  have hr : InRange lo hi (exactMod a b) := Decidable.of_not_not (fun hc => h (Or.inr hc))
  refine ⟨ofIntMem lo hi (exactMod a b) hr.1 hr.2, ?_, by simp [exactMod]⟩
  unfold checked_mod
  rw [ite_eq_right hb]
  exact ofInt?_of_inRange hr

/-! ### The wrapping variants -/

/-- Wrapping division: the exact quotient reduced modulo the period.  A zero
divisor gives the wrap of `0`, following the core convention `a / 0 = 0`. -/
def wrapping_div (a b : BoundedInt64 lo hi) : BoundedInt64 lo hi :=
  ofIntWrap (lo_le_hi a) (exactDiv a b)

/-- Wrapping remainder: the exact remainder reduced modulo the period.  A zero
divisor gives the wrap of `a`, following the core convention `a % 0 = a`. -/
def wrapping_mod (a b : BoundedInt64 lo hi) : BoundedInt64 lo hi :=
  ofIntWrap (lo_le_hi a) (exactMod a b)

/-- Exactness: wrapping division returns the exact quotient when it is in range. -/
theorem toInt_wrapping_div_of_inRange {a b : BoundedInt64 lo hi}
    (h : InRange lo hi (exactDiv a b)) :
    (wrapping_div a b).toInt = a.toInt.tdiv b.toInt :=
  ofIntWrap_of_inRange (lo_le_hi a) h

/-- Exactness: the wrapping remainder is exact when it is in range. -/
theorem toInt_wrapping_mod_of_inRange {a b : BoundedInt64 lo hi}
    (h : InRange lo hi (exactMod a b)) :
    (wrapping_mod a b).toInt = a.toInt.tmod b.toInt :=
  ofIntWrap_of_inRange (lo_le_hi a) h

/-! ### The overflowing variants -/

/-- Overflowing division: the wrapped quotient together with a flag that is
`true` exactly when the division fails. -/
def overflowing_div (a b : BoundedInt64 lo hi) : BoundedInt64 lo hi × Bool :=
  (wrapping_div a b, decide (b.toInt = 0 ∨ ¬ InRange lo hi (exactDiv a b)))

/-- Overflowing remainder: the wrapped remainder together with a flag that is
`true` exactly when it fails. -/
def overflowing_mod (a b : BoundedInt64 lo hi) : BoundedInt64 lo hi × Bool :=
  (wrapping_mod a b, decide (b.toInt = 0 ∨ ¬ InRange lo hi (exactMod a b)))

@[simp] theorem overflowing_div_fst (a b : BoundedInt64 lo hi) :
    (overflowing_div a b).1 = wrapping_div a b := rfl

@[simp] theorem overflowing_mod_fst (a b : BoundedInt64 lo hi) :
    (overflowing_mod a b).1 = wrapping_mod a b := rfl

theorem overflowing_div_snd_iff {a b : BoundedInt64 lo hi} :
    (overflowing_div a b).2 = true ↔ divFails a b := by
  unfold overflowing_div divFails; simp

theorem overflowing_mod_snd_iff {a b : BoundedInt64 lo hi} :
    (overflowing_mod a b).2 = true ↔ modFails a b := by
  unfold overflowing_mod modFails; simp

/-! ### The saturating variants -/

/-- Saturating division: the exact quotient, clamped to `[lo, hi]`. -/
def saturating_div (a b : BoundedInt64 lo hi) : BoundedInt64 lo hi :=
  ofIntSat (lo_le_hi a) (exactDiv a b)

/-- Saturating remainder: the exact remainder, clamped to `[lo, hi]`. -/
def saturating_mod (a b : BoundedInt64 lo hi) : BoundedInt64 lo hi :=
  ofIntSat (lo_le_hi a) (exactMod a b)

@[simp] theorem toInt_saturating_div (a b : BoundedInt64 lo hi) :
    (saturating_div a b).toInt = max lo.toInt (min (a.toInt.tdiv b.toInt) hi.toInt) := by
  unfold saturating_div exactDiv; rw [toInt_ofIntSat]

@[simp] theorem toInt_saturating_mod (a b : BoundedInt64 lo hi) :
    (saturating_mod a b).toInt = max lo.toInt (min (a.toInt.tmod b.toInt) hi.toInt) := by
  unfold saturating_mod exactMod; rw [toInt_ofIntSat]

/-- Exactness: saturating division returns the exact quotient when it is in range. -/
theorem toInt_saturating_div_of_inRange {a b : BoundedInt64 lo hi}
    (h : InRange lo hi (exactDiv a b)) :
    (saturating_div a b).toInt = a.toInt.tdiv b.toInt :=
  ofIntSat_of_inRange (lo_le_hi a) h

/-- Exactness: the saturating remainder is exact when it is in range. -/
theorem toInt_saturating_mod_of_inRange {a b : BoundedInt64 lo hi}
    (h : InRange lo hi (exactMod a b)) :
    (saturating_mod a b).toInt = a.toInt.tmod b.toInt :=
  ofIntSat_of_inRange (lo_le_hi a) h

/-! ### Agreement of the four variants -/

/-- When the division does not fail, all four variants denote the exact
quotient and the flag is `false`. -/
theorem div_variants_agree {a b : BoundedInt64 lo hi} (h : ¬ divFails a b) :
    (∃ c, checked_div a b = some c ∧ c.toInt = a.toInt.tdiv b.toInt) ∧
      (wrapping_div a b).toInt = a.toInt.tdiv b.toInt ∧
      (overflowing_div a b).1.toInt = a.toInt.tdiv b.toInt ∧
      (overflowing_div a b).2 = false ∧
      (saturating_div a b).toInt = a.toInt.tdiv b.toInt := by
  have hr : InRange lo hi (exactDiv a b) := by
    unfold divFails at h
    exact Decidable.of_not_not (fun hc => h (Or.inr hc))
  refine ⟨checked_div_of_not_fails h, toInt_wrapping_div_of_inRange hr,
    toInt_wrapping_div_of_inRange hr, ?_, toInt_saturating_div_of_inRange hr⟩
  cases hb : (overflowing_div a b).2 with
  | false => rfl
  | true => exact absurd (overflowing_div_snd_iff.mp hb) h

/-- When the remainder does not fail, all four variants denote the exact
remainder and the flag is `false`. -/
theorem mod_variants_agree {a b : BoundedInt64 lo hi} (h : ¬ modFails a b) :
    (∃ c, checked_mod a b = some c ∧ c.toInt = a.toInt.tmod b.toInt) ∧
      (wrapping_mod a b).toInt = a.toInt.tmod b.toInt ∧
      (overflowing_mod a b).1.toInt = a.toInt.tmod b.toInt ∧
      (overflowing_mod a b).2 = false ∧
      (saturating_mod a b).toInt = a.toInt.tmod b.toInt := by
  have hr : InRange lo hi (exactMod a b) := by
    unfold modFails at h
    exact Decidable.of_not_not (fun hc => h (Or.inr hc))
  refine ⟨checked_mod_of_not_fails h, toInt_wrapping_mod_of_inRange hr,
    toInt_wrapping_mod_of_inRange hr, ?_, toInt_saturating_mod_of_inRange hr⟩
  cases hb : (overflowing_mod a b).2 with
  | false => rfl
  | true => exact absurd (overflowing_mod_snd_iff.mp hb) h

end BoundedInt64
