import IntUInt53.BoundedInt64.Fast
import IntUInt53.BoundedInt64.Add
import IntUInt53.BoundedInt64.Sub
import IntUInt53.BoundedInt64.Div

/-!
# Notation and instances for `BoundedInt64`

The signed counterpart of `IntUInt53.TopBoundedUInt64.Instances`, and it
follows the same core-library convention:

* **the ambient operators are the wrapping ones**: `+`, `-`, `*`, `/` and `%`
  denote `wrapping_add`, `wrapping_sub`, `wrapping_mul`, `wrapping_div` and
  `wrapping_mod`, and each binding is recorded by a theorem;
* **the checked variants get `?` names**: `add?`, `sub?`, `mul?`, `div?`,
  `mod?`.

The comparison instances are provided and proved lawful.
-/

set_option autoImplicit false

namespace BoundedInt64

variable {lo hi : Int64}

/-! ### Arithmetic notation: the ambient operators wrap -/

instance : Add (BoundedInt64 lo hi) := ⟨wrapping_add⟩
instance : Sub (BoundedInt64 lo hi) := ⟨wrapping_sub⟩
instance : Mul (BoundedInt64 lo hi) := ⟨wrapping_mul⟩
instance : Div (BoundedInt64 lo hi) := ⟨wrapping_div⟩
instance : Mod (BoundedInt64 lo hi) := ⟨wrapping_mod⟩

/-- `+` is wrapping addition. -/
@[simp] theorem add_eq (a b : BoundedInt64 lo hi) : a + b = wrapping_add a b := rfl

/-- `-` is wrapping subtraction. -/
@[simp] theorem sub_eq (a b : BoundedInt64 lo hi) : a - b = wrapping_sub a b := rfl

/-- `*` is wrapping multiplication. -/
@[simp] theorem mul_eq (a b : BoundedInt64 lo hi) : a * b = wrapping_mul a b := rfl

/-- `/` is wrapping division. -/
@[simp] theorem div_eq (a b : BoundedInt64 lo hi) : a / b = wrapping_div a b := rfl

/-- `%` is the wrapping remainder. -/
@[simp] theorem mod_eq (a b : BoundedInt64 lo hi) : a % b = wrapping_mod a b := rfl

theorem toInt_add (a b : BoundedInt64 lo hi) :
    (a + b).toInt = lo.toInt + (a.toInt + b.toInt - lo.toInt) % period lo hi :=
  toInt_wrapping_add a b

/-! ### The checked variants, named as in core -/

/-- The checked sum, `none` on overflow. -/
abbrev add? (a b : BoundedInt64 lo hi) : Option (BoundedInt64 lo hi) := checked_add a b

/-- The checked difference, `none` on overflow. -/
abbrev sub? (a b : BoundedInt64 lo hi) : Option (BoundedInt64 lo hi) := checked_sub a b

/-- The checked product, `none` on overflow. -/
abbrev mul? (a b : BoundedInt64 lo hi) : Option (BoundedInt64 lo hi) := checked_mul a b

/-- The checked quotient, `none` on a zero divisor or an out-of-range quotient. -/
abbrev div? (a b : BoundedInt64 lo hi) : Option (BoundedInt64 lo hi) := checked_div a b

/-- The checked remainder, `none` on a zero divisor or an out-of-range remainder. -/
abbrev mod? (a b : BoundedInt64 lo hi) : Option (BoundedInt64 lo hi) := checked_mod a b

/-! ### `BEq` -/

theorem beq_iff_toInt_eq {a b : BoundedInt64 lo hi} : (a == b) = true ↔ a.toInt = b.toInt := by
  rw [beq_iff_eq, ext_iff]

/-! ### `Ord` and its lawfulness -/

instance : Ord (BoundedInt64 lo hi) := ⟨fun a b => compare a.toInt b.toInt⟩

theorem compare_eq (a b : BoundedInt64 lo hi) : compare a b = compare a.toInt b.toInt := rfl

instance : Std.OrientedOrd (BoundedInt64 lo hi) where
  eq_swap {a b} := by
    rw [compare_eq, compare_eq]
    exact Std.OrientedCmp.eq_swap (cmp := (compare : Int → Int → Ordering))

instance : Std.ReflCmp (compare (α := BoundedInt64 lo hi)) where
  compare_self {a} := by
    rw [compare_eq]
    exact Std.ReflCmp.compare_self

instance : Std.TransOrd (BoundedInt64 lo hi) where
  isLE_trans {a b c} h₁ h₂ := by
    rw [compare_eq] at h₁ h₂ ⊢
    exact Std.TransCmp.isLE_trans h₁ h₂

instance : Std.LawfulEqOrd (BoundedInt64 lo hi) where
  eq_of_compare {a b} h := by
    rw [compare_eq] at h
    exact ext (Std.LawfulEqCmp.eq_of_compare h)

theorem compare_eq_eq_iff {a b : BoundedInt64 lo hi} : compare a b = Ordering.eq ↔ a = b :=
  ⟨fun h => Std.LawfulEqCmp.eq_of_compare h, fun h => h ▸ Std.ReflCmp.compare_self⟩

/-! ### `Hashable` -/

instance : Hashable (BoundedInt64 lo hi) := ⟨fun a => hash a.toInt⟩

theorem hash_eq (a : BoundedInt64 lo hi) : hash a = hash a.toInt := rfl

instance : LawfulHashable (BoundedInt64 lo hi) where
  hash_eq {a b} h := by
    rw [hash_eq, hash_eq, beq_iff_eq.mp h]

/-! ### `ToString` -/

instance : ToString (BoundedInt64 lo hi) := ⟨fun a => toString a.toInt⟩

theorem toString_eq (a : BoundedInt64 lo hi) : toString a = toString a.toInt := rfl

end BoundedInt64
