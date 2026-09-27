module

public import HashableFloat.Compare

@[expose] public section

set_option autoImplicit false

/-!
# `HashableFloat`: a `Float` that is neither `NaN` nor `-0.0`

`Float` has no lawful `BEq`: `NaN != NaN`, and `0.0 == -0.0` although the two have different
bits (so no hash of the bits respects `==`).  Once those two values are excluded, IEEE
equality *is* equality of the bits, and so

* `==` is lawful (`LawfulBEq`), and agrees with the derived `DecidableEq`;
* hashing the bits is lawful (`LawfulHashable`);
* the IEEE order is a linear order: `compare` is oriented, transitive and agrees with `=`,
  `==`, `<` and `≤` (`Std.TransOrd`, `Std.LawfulEqOrd`, `Std.LawfulBEqOrd`,
  `Std.LawfulOrderOrd`, `Std.IsLinearOrder`, …).

Literals (`OfScientific`, `OfNat`) and arithmetic go through `HashableFloat.normalize`, which
turns `NaN` and `-0.0` into `0.0`.
-/

/-- A 64-bit float that is neither `NaN` nor `-0.0`. -/
structure HashableFloat where
  ofFloat ::
  /-- The underlying float. -/
  toFloat : Float
  notNaN : toFloat ≠ Float.nan
  notNegZero : toFloat ≠ (-0 : Float)
  deriving DecidableEq

namespace HashableFloat

open Float.Model

theorem ext {a b : HashableFloat} (h : a.toFloat = b.toFloat) : a = b := by
  cases a; cases b; cases h; rfl

theorem toFloat_inj {a b : HashableFloat} : a.toFloat = b.toFloat ↔ a = b :=
  ⟨ext, fun h => h ▸ rfl⟩

/-! ## Equality and hashing -/

/-- IEEE equality of the underlying floats (which is equality, see `beq_iff_eq`). -/
instance : BEq HashableFloat where
  beq a b := a.toFloat == b.toFloat

theorem beq_def (a b : HashableFloat) : (a == b) = (a.toFloat == b.toFloat) := rfl

/-- On floats that are neither `NaN` nor `-0.0`, IEEE equality is equality. -/
theorem beq_iff_eq {a b : HashableFloat} : (a == b) = true ↔ a = b := by
  rw [beq_def, Float.beq_iff_ne_nan_and_eq, ← toFloat_inj]
  constructor
  · rintro ⟨_, _, h | ⟨_, h⟩ | ⟨h, _⟩⟩
    · exact h
    · exact absurd h b.notNegZero
    · exact absurd h a.notNegZero
  · intro h
    exact ⟨a.notNaN, b.notNaN, Or.inl h⟩

instance : ReflBEq HashableFloat where
  rfl := beq_iff_eq.mpr rfl

instance : LawfulBEq HashableFloat where
  eq_of_beq := beq_iff_eq.mp

/-- The hash of the bits. -/
instance : Hashable HashableFloat where
  hash f := hash f.toFloat.toBits

instance : LawfulHashable HashableFloat where
  hash_eq a b h := by rw [beq_iff_eq.mp h]

/-! ## Construction -/

/-- `0.0`. -/
instance : Inhabited HashableFloat where
  default := ⟨0.0, by decide, by decide⟩

/-- The float, if it is neither `NaN` nor `-0.0`. -/
def ofFloat? (f : Float) : Option HashableFloat :=
  if h_nan : f = Float.nan then none
  else if h_neg : f = (-0 : Float) then none
  else some ⟨f, h_nan, h_neg⟩

/-- The float; panics if it is `NaN` or `-0.0`. -/
def ofFloat! (f : Float) : HashableFloat :=
  match ofFloat? f with
  | some hf => hf
  | none => panic! s!"Invalid HashableFloat: {f} is either NaN or -0.0"

/-- The float, with `NaN` and `-0.0` replaced by `0.0`. -/
def normalize (f : Float) : HashableFloat :=
  if h_nan : f = Float.nan then default
  else if h_neg : f = (-0 : Float) then default
  else ⟨f, h_nan, h_neg⟩

theorem ofFloat?_eq_some_iff {f : Float} {a : HashableFloat} :
    ofFloat? f = some a ↔ a.toFloat = f := by
  unfold ofFloat?
  constructor
  · intro h; split at h
    · cases h
    · split at h
      · cases h
      · cases h; rfl
  · intro h; subst h
    simp [a.notNaN, a.notNegZero]

@[simp] theorem ofFloat?_toFloat (a : HashableFloat) : ofFloat? a.toFloat = some a :=
  ofFloat?_eq_some_iff.mpr rfl

@[simp] theorem normalize_toFloat (a : HashableFloat) : normalize a.toFloat = a := by
  simp [normalize, a.notNaN, a.notNegZero]

theorem toFloat_normalize_of_ne {f : Float} (h_nan : f ≠ Float.nan) (h_neg : f ≠ (-0 : Float)) :
    (normalize f).toFloat = f := by
  simp [normalize, h_nan, h_neg]

/-- Decimal literals (`1.5`, `2e10`, …), through `normalize`. -/
instance : OfScientific HashableFloat where
  ofScientific m s e := normalize (OfScientific.ofScientific m s e)

/-- Natural-number literals, through `normalize`. -/
instance (n : Nat) : OfNat HashableFloat n where
  ofNat := normalize (OfNat.ofNat n)

instance : Coe HashableFloat Float where
  coe f := f.toFloat

instance : Repr HashableFloat where
  reprPrec f := reprPrec f.toFloat

instance : ToString HashableFloat where
  toString f := toString f.toFloat

/-! ## Arithmetic

Every operation is the one of `Float`, followed by `normalize`: a result `NaN` (`0.0 / 0.0`,
`inf - inf`, …) or `-0.0` (`-0.0`, `-1.0 * 0.0`, …) becomes `0.0`. -/

instance : Neg HashableFloat where
  neg a := normalize (-a.toFloat)

instance : Add HashableFloat where
  add a b := normalize (a.toFloat + b.toFloat)

instance : Sub HashableFloat where
  sub a b := normalize (a.toFloat - b.toFloat)

instance : Mul HashableFloat where
  mul a b := normalize (a.toFloat * b.toFloat)

instance : Div HashableFloat where
  div a b := normalize (a.toFloat / b.toFloat)

/-! ## Order -/

instance : LT HashableFloat where
  lt a b := a.toFloat < b.toFloat

instance : LE HashableFloat where
  le a b := a.toFloat ≤ b.toFloat

instance (a b : HashableFloat) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toFloat < b.toFloat))

instance (a b : HashableFloat) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toFloat ≤ b.toFloat))

/-- The IEEE comparison of the underlying floats (total here: there is no `NaN`). -/
instance : Ord HashableFloat where
  compare a b :=
    if a.toFloat < b.toFloat then Ordering.lt
    else if a.toFloat == b.toFloat then Ordering.eq
    else Ordering.gt

/-- `min a b` is `a` when `a ≤ b`, else `b`. -/
instance : Min HashableFloat where
  min a b := if a ≤ b then a else b

/-- `max a b` is `a` when `b ≤ a`, else `b`. -/
instance : Max HashableFloat where
  max a b := if b ≤ a then a else b

/-- The model of the underlying float. -/
abbrev unpack (a : HashableFloat) : UnpackedFloat := a.toFloat.toModel.unpack

theorem unpack_ne_notANumber (a : HashableFloat) : a.unpack ≠ .notANumber := by
  have := @Float.isNaN_eq_decide_eq_nan a.toFloat
  simp [a.notNaN, Float.isNaN, Float.Model.isNaN] at this
  intro e; rw [unpack] at e; rw [e] at this; simp [UnpackedFloat.isNaN] at this

theorem lt_iff_unpack (a b : HashableFloat) : a < b ↔ a.unpack.compare b.unpack = some .lt := by
  show decide (a.unpack.lt b.unpack = true) = true ↔ _
  simp [UnpackedFloat.lt]

theorem le_iff_unpack (a b : HashableFloat) : a ≤ b ↔ a.unpack.le b.unpack = true :=
  decide_eq_true_iff

theorem beq_iff_unpack (a b : HashableFloat) :
    (a == b) = true ↔ a.unpack.compare b.unpack = some .eq := by
  show (a.unpack.compare b.unpack == some .eq) = true ↔ _
  simp

/-- `compare` is the comparison of the model (`Float.Model.UnpackedFloat.compare`). -/
theorem some_compare (a b : HashableFloat) : some (compare a b) = a.unpack.compare b.unpack := by
  have hs := LeanScript.FloatOrder.compare_isSome a.unpack_ne_notANumber b.unpack_ne_notANumber
  have hlt := lt_iff_unpack a b
  have heq := beq_iff_unpack a b
  show some (if a < b then _ else if (a == b) = true then _ else _) = _
  rcases h : a.unpack.compare b.unpack with _ | _ | _ | _
  · simp [h] at hs
  · simp [hlt.mpr h]
  · have : ¬ a < b := by simp [hlt, h]
    simp [this, heq.mpr h]
  · have h1 : ¬ a < b := by simp [hlt, h]
    have h2 : ¬ (a == b) = true := by simp [heq, h]
    simp [h1, h2]

instance : Std.OrientedOrd HashableFloat where
  eq_swap {a b} := LeanScript.FloatOrder.oriented_of unpack compare some_compare a b

instance : Std.TransOrd HashableFloat where
  isLE_trans := LeanScript.FloatOrder.trans_of unpack compare some_compare

/-- Proves that `compare a b = Ordering.eq` if and only if `a == b`. -/
theorem compare_eq_iff_beq (a b : HashableFloat) : compare a b = Ordering.eq ↔ (a == b) = true := by
  rw [beq_iff_unpack, ← some_compare, Option.some.injEq]

/-- Proves that `compare a b = Ordering.eq` if and only if `a = b`. -/
theorem compare_eq_iff_eq (a b : HashableFloat) : compare a b = Ordering.eq ↔ a = b := by
  rw [compare_eq_iff_beq, beq_iff_eq]

/-- Proves that `compare a b = Ordering.lt` if and only if `a < b`. -/
theorem compare_lt_iff_lt (a b : HashableFloat) : compare a b = Ordering.lt ↔ a < b := by
  rw [lt_iff_unpack, ← some_compare, Option.some.injEq]

/-- Proves that `compare a b = Ordering.gt` if and only if `a > b`. -/
theorem compare_gt_iff_gt (a b : HashableFloat) : compare a b = Ordering.gt ↔ a > b := by
  rw [Std.OrientedOrd.eq_swap, Ordering.swap_eq_gt, compare_lt_iff_lt]

/-- Proves that `(compare a b).isLE` if and only if `a ≤ b`. -/
theorem isLE_compare_iff_le (a b : HashableFloat) : (compare a b).isLE ↔ a ≤ b := by
  rw [le_iff_unpack]; exact LeanScript.FloatOrder.isLE_iff_of unpack compare some_compare a b

instance : Std.LawfulEqOrd HashableFloat where
  compare_self {a} := (compare_eq_iff_eq a a).mpr rfl
  eq_of_compare {a b} h := (compare_eq_iff_eq a b).mp h

instance : Std.LawfulBEqOrd HashableFloat where
  compare_eq_iff_beq {a b} := compare_eq_iff_beq a b

instance : Std.LawfulOrderOrd HashableFloat where
  isLE_compare := isLE_compare_iff_le
  isGE_compare a b := by
    rw [← isLE_compare_iff_le, Std.OrientedOrd.eq_swap (a := b), Ordering.isLE_swap]

instance : Std.IsLinearOrder HashableFloat := by
  apply Std.IsLinearOrder.of_le
  · constructor; intro a b hab hba
    rw [← isLE_compare_iff_le] at hab hba
    rw [Std.OrientedOrd.eq_swap, Ordering.isLE_swap] at hba
    rw [← compare_eq_iff_eq]
    revert hab hba; cases compare a b <;> decide
  · constructor; intro a b c hab hbc
    rw [← isLE_compare_iff_le] at *
    exact Std.TransOrd.isLE_trans hab hbc
  · constructor; intro a b
    rw [← isLE_compare_iff_le, ← isLE_compare_iff_le, Std.OrientedOrd.eq_swap (a := b),
      Ordering.isLE_swap]
    cases compare a b <;> decide

instance : Std.LawfulOrderLT HashableFloat where
  lt_iff a b := by
    rw [← compare_lt_iff_lt, ← isLE_compare_iff_le, ← isLE_compare_iff_le,
      Std.OrientedOrd.eq_swap (a := b), Ordering.isLE_swap]
    cases compare a b <;> decide

instance : Std.LawfulOrderBEq HashableFloat where
  beq_iff_le_and_ge a b := by
    rw [← compare_eq_iff_beq, ← isLE_compare_iff_le, ← isLE_compare_iff_le,
      Std.OrientedOrd.eq_swap (a := b), Ordering.isLE_swap]
    cases compare a b <;> decide

instance : Std.LawfulOrderLeftLeaningMin HashableFloat where
  min_eq_left _ _ h := by simp only [min, h, ↓reduceIte]
  min_eq_right _ _ h := by simp only [min, h, ↓reduceIte]

instance : Std.LawfulOrderLeftLeaningMax HashableFloat where
  max_eq_left _ _ h := by simp only [max, h, ↓reduceIte]
  max_eq_right _ _ h := by simp only [max, h, ↓reduceIte]

end HashableFloat

end
