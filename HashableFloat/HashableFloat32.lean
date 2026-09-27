module

public import HashableFloat.Compare

@[expose] public section

set_option autoImplicit false

/-!
# `HashableFloat32`: a `Float32` that is neither `NaN` nor `-0.0`

`Float32` has no lawful `BEq`: `NaN != NaN`, and `0.0 == -0.0` although the two have different
bits (so no hash of the bits respects `==`).  Once those two values are excluded, IEEE
equality *is* equality of the bits, and so

* `==` is lawful (`LawfulBEq`), and agrees with the derived `DecidableEq`;
* hashing the bits is lawful (`LawfulHashable`);
* the IEEE order is a linear order: `compare` is oriented, transitive and agrees with `=`,
  `==`, `<` and `≤` (`Std.TransOrd`, `Std.LawfulEqOrd`, `Std.LawfulBEqOrd`,
  `Std.LawfulOrderOrd`, `Std.IsLinearOrder`, …).

Literals (`OfScientific`, `OfNat`) and arithmetic go through `HashableFloat32.normalize`, which
turns `NaN` and `-0.0` into `0.0`.
-/

/-- A 32-bit float that is neither `NaN` nor `-0.0`. -/
structure HashableFloat32 where
  ofFloat32 ::
  /-- The underlying float. -/
  toFloat32 : Float32
  notNaN : toFloat32 ≠ Float32.nan
  notNegZero : toFloat32 ≠ (-0 : Float32)
  deriving DecidableEq

namespace HashableFloat32

open Float.Model

theorem ext {a b : HashableFloat32} (h : a.toFloat32 = b.toFloat32) : a = b := by
  cases a; cases b; cases h; rfl

theorem toFloat32_inj {a b : HashableFloat32} : a.toFloat32 = b.toFloat32 ↔ a = b :=
  ⟨ext, fun h => h ▸ rfl⟩

/-! ## Equality and hashing -/

/-- IEEE equality of the underlying floats (which is equality, see `beq_iff_eq`). -/
instance : BEq HashableFloat32 where
  beq a b := a.toFloat32 == b.toFloat32

theorem beq_def (a b : HashableFloat32) : (a == b) = (a.toFloat32 == b.toFloat32) := rfl

/-- On floats that are neither `NaN` nor `-0.0`, IEEE equality is equality. -/
theorem beq_iff_eq {a b : HashableFloat32} : (a == b) = true ↔ a = b := by
  rw [beq_def, Float32.beq_iff_ne_nan_and_eq, ← toFloat32_inj]
  constructor
  · rintro ⟨_, _, h | ⟨_, h⟩ | ⟨h, _⟩⟩
    · exact h
    · exact absurd h b.notNegZero
    · exact absurd h a.notNegZero
  · intro h
    exact ⟨a.notNaN, b.notNaN, Or.inl h⟩

instance : ReflBEq HashableFloat32 where
  rfl := beq_iff_eq.mpr rfl

instance : LawfulBEq HashableFloat32 where
  eq_of_beq := beq_iff_eq.mp

/-- The hash of the bits. -/
instance : Hashable HashableFloat32 where
  hash f := hash f.toFloat32.toBits

instance : LawfulHashable HashableFloat32 where
  hash_eq a b h := by rw [beq_iff_eq.mp h]

/-! ## Construction -/

/-- `0.0`. -/
instance : Inhabited HashableFloat32 where
  default := ⟨0.0, by decide, by decide⟩

/-- The float, if it is neither `NaN` nor `-0.0`. -/
def ofFloat32? (f : Float32) : Option HashableFloat32 :=
  if h_nan : f = Float32.nan then none
  else if h_neg : f = (-0 : Float32) then none
  else some ⟨f, h_nan, h_neg⟩

/-- The float; panics if it is `NaN` or `-0.0`. -/
def ofFloat32! (f : Float32) : HashableFloat32 :=
  match ofFloat32? f with
  | some hf => hf
  | none => panic! s!"Invalid HashableFloat32: {f} is either NaN or -0.0"

/-- The float, with `NaN` and `-0.0` replaced by `0.0`. -/
def normalize (f : Float32) : HashableFloat32 :=
  if h_nan : f = Float32.nan then default
  else if h_neg : f = (-0 : Float32) then default
  else ⟨f, h_nan, h_neg⟩

theorem ofFloat32?_eq_some_iff {f : Float32} {a : HashableFloat32} :
    ofFloat32? f = some a ↔ a.toFloat32 = f := by
  unfold ofFloat32?
  constructor
  · intro h; split at h
    · cases h
    · split at h
      · cases h
      · cases h; rfl
  · intro h; subst h
    simp [a.notNaN, a.notNegZero]

@[simp] theorem ofFloat32?_toFloat32 (a : HashableFloat32) : ofFloat32? a.toFloat32 = some a :=
  ofFloat32?_eq_some_iff.mpr rfl

@[simp] theorem normalize_toFloat32 (a : HashableFloat32) : normalize a.toFloat32 = a := by
  simp [normalize, a.notNaN, a.notNegZero]

theorem toFloat32_normalize_of_ne {f : Float32} (h_nan : f ≠ Float32.nan)
    (h_neg : f ≠ (-0 : Float32)) :
    (normalize f).toFloat32 = f := by
  simp [normalize, h_nan, h_neg]

/-- Decimal literals (`1.5`, `2e10`, …), through `normalize`. -/
instance : OfScientific HashableFloat32 where
  ofScientific m s e := normalize (OfScientific.ofScientific m s e)

/-- Natural-number literals, through `normalize`. -/
instance (n : Nat) : OfNat HashableFloat32 n where
  ofNat := normalize (OfNat.ofNat n)

instance : Coe HashableFloat32 Float32 where
  coe f := f.toFloat32

instance : Repr HashableFloat32 where
  reprPrec f := reprPrec f.toFloat32

instance : ToString HashableFloat32 where
  toString f := toString f.toFloat32

/-! ## Arithmetic

Every operation is the one of `Float32`, followed by `normalize`: a result `NaN` (`0.0 / 0.0`,
`inf - inf`, …) or `-0.0` (`-0.0`, `-1.0 * 0.0`, …) becomes `0.0`. -/

instance : Neg HashableFloat32 where
  neg a := normalize (-a.toFloat32)

instance : Add HashableFloat32 where
  add a b := normalize (a.toFloat32 + b.toFloat32)

instance : Sub HashableFloat32 where
  sub a b := normalize (a.toFloat32 - b.toFloat32)

instance : Mul HashableFloat32 where
  mul a b := normalize (a.toFloat32 * b.toFloat32)

instance : Div HashableFloat32 where
  div a b := normalize (a.toFloat32 / b.toFloat32)

/-! ## Order -/

instance : LT HashableFloat32 where
  lt a b := a.toFloat32 < b.toFloat32

instance : LE HashableFloat32 where
  le a b := a.toFloat32 ≤ b.toFloat32

instance (a b : HashableFloat32) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toFloat32 < b.toFloat32))

instance (a b : HashableFloat32) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toFloat32 ≤ b.toFloat32))

/-- The IEEE comparison of the underlying floats (total here: there is no `NaN`). -/
instance : Ord HashableFloat32 where
  compare a b :=
    if a.toFloat32 < b.toFloat32 then Ordering.lt
    else if a.toFloat32 == b.toFloat32 then Ordering.eq
    else Ordering.gt

/-- `min a b` is `a` when `a ≤ b`, else `b`. -/
instance : Min HashableFloat32 where
  min a b := if a ≤ b then a else b

/-- `max a b` is `a` when `b ≤ a`, else `b`. -/
instance : Max HashableFloat32 where
  max a b := if b ≤ a then a else b

/-- The model of the underlying float. -/
abbrev unpack (a : HashableFloat32) : UnpackedFloat := a.toFloat32.toModel.unpack

theorem unpack_ne_notANumber (a : HashableFloat32) : a.unpack ≠ .notANumber := by
  have := @Float32.isNaN_eq_decide_eq_nan a.toFloat32
  simp [a.notNaN, Float32.isNaN, Float32.Model.isNaN] at this
  intro e; rw [unpack] at e; rw [e] at this; simp [UnpackedFloat.isNaN] at this

theorem lt_iff_unpack (a b : HashableFloat32) : a < b ↔ a.unpack.compare b.unpack = some .lt := by
  show decide (a.unpack.lt b.unpack = true) = true ↔ _
  simp [UnpackedFloat.lt]

theorem le_iff_unpack (a b : HashableFloat32) : a ≤ b ↔ a.unpack.le b.unpack = true :=
  decide_eq_true_iff

theorem beq_iff_unpack (a b : HashableFloat32) :
    (a == b) = true ↔ a.unpack.compare b.unpack = some .eq := by
  show (a.unpack.compare b.unpack == some .eq) = true ↔ _
  simp

/-- `compare` is the comparison of the model (`Float.Model.UnpackedFloat.compare`). -/
theorem some_compare (a b : HashableFloat32) : some (compare a b) = a.unpack.compare b.unpack := by
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

instance : Std.OrientedOrd HashableFloat32 where
  eq_swap {a b} := LeanScript.FloatOrder.oriented_of unpack compare some_compare a b

instance : Std.TransOrd HashableFloat32 where
  isLE_trans := LeanScript.FloatOrder.trans_of unpack compare some_compare

/-- Proves that `compare a b = Ordering.eq` if and only if `a == b`. -/
theorem compare_eq_iff_beq (a b : HashableFloat32) : compare a b = Ordering.eq ↔ (a == b) = true := by
  rw [beq_iff_unpack, ← some_compare, Option.some.injEq]

/-- Proves that `compare a b = Ordering.eq` if and only if `a = b`. -/
theorem compare_eq_iff_eq (a b : HashableFloat32) : compare a b = Ordering.eq ↔ a = b := by
  rw [compare_eq_iff_beq, beq_iff_eq]

/-- Proves that `compare a b = Ordering.lt` if and only if `a < b`. -/
theorem compare_lt_iff_lt (a b : HashableFloat32) : compare a b = Ordering.lt ↔ a < b := by
  rw [lt_iff_unpack, ← some_compare, Option.some.injEq]

/-- Proves that `compare a b = Ordering.gt` if and only if `a > b`. -/
theorem compare_gt_iff_gt (a b : HashableFloat32) : compare a b = Ordering.gt ↔ a > b := by
  rw [Std.OrientedOrd.eq_swap, Ordering.swap_eq_gt, compare_lt_iff_lt]

/-- Proves that `(compare a b).isLE` if and only if `a ≤ b`. -/
theorem isLE_compare_iff_le (a b : HashableFloat32) : (compare a b).isLE ↔ a ≤ b := by
  rw [le_iff_unpack]; exact LeanScript.FloatOrder.isLE_iff_of unpack compare some_compare a b

instance : Std.LawfulEqOrd HashableFloat32 where
  compare_self {a} := (compare_eq_iff_eq a a).mpr rfl
  eq_of_compare {a b} h := (compare_eq_iff_eq a b).mp h

instance : Std.LawfulBEqOrd HashableFloat32 where
  compare_eq_iff_beq {a b} := compare_eq_iff_beq a b

instance : Std.LawfulOrderOrd HashableFloat32 where
  isLE_compare := isLE_compare_iff_le
  isGE_compare a b := by
    rw [← isLE_compare_iff_le, Std.OrientedOrd.eq_swap (a := b), Ordering.isLE_swap]

instance : Std.IsLinearOrder HashableFloat32 := by
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

instance : Std.LawfulOrderLT HashableFloat32 where
  lt_iff a b := by
    rw [← compare_lt_iff_lt, ← isLE_compare_iff_le, ← isLE_compare_iff_le,
      Std.OrientedOrd.eq_swap (a := b), Ordering.isLE_swap]
    cases compare a b <;> decide

instance : Std.LawfulOrderBEq HashableFloat32 where
  beq_iff_le_and_ge a b := by
    rw [← compare_eq_iff_beq, ← isLE_compare_iff_le, ← isLE_compare_iff_le,
      Std.OrientedOrd.eq_swap (a := b), Ordering.isLE_swap]
    cases compare a b <;> decide

instance : Std.LawfulOrderLeftLeaningMin HashableFloat32 where
  min_eq_left _ _ h := by simp only [min, h, ↓reduceIte]
  min_eq_right _ _ h := by simp only [min, h, ↓reduceIte]

instance : Std.LawfulOrderLeftLeaningMax HashableFloat32 where
  max_eq_left _ _ h := by simp only [max, h, ↓reduceIte]
  max_eq_right _ _ h := by simp only [max, h, ↓reduceIte]

end HashableFloat32

end
