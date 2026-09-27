import IntUInt53.TopBoundedUInt64.Fast
import IntUInt53.TopBoundedUInt64.Add
import IntUInt53.TopBoundedUInt64.Sub
import IntUInt53.TopBoundedUInt64.Div

/-!
# Notation and instances for `TopBoundedUInt64`

This module follows the convention of the Lean core library for machine
integers rather than the Rust convention of wrapper types:

* **the ambient operators are the wrapping ones.**  `UInt64.add` — what `+`
  means on `UInt64` — is documented in core as "wrapping around on overflow",
  so `+`, `-` and `*` here are bound to `wrapping_add`, `wrapping_sub` and
  `wrapping_mul`, and `/` and `%` to the total `div` and `mod` (which, as in
  core, answer `0` and `a` on a zero divisor).  Every such binding is recorded
  by a theorem below, so no notation hides which function is meant;
* **the checked variants get `?` names.**  Core writes `Fin.addNat?` and
  `Int.toNat?` for the partial forms, so `add?`, `sub?`, `mul?`, `div?` and
  `mod?` are provided as abbreviations of `checked_add`, `checked_sub`,
  `checked_mul`, `checked_div` and `checked_mod`.

It also provides the comparison instances and proves them lawful: `BEq` agrees
with equality, `Ord` is oriented, transitive and decides equality, and `hash`
respects `BEq`.
-/

set_option autoImplicit false

namespace TopBoundedUInt64

variable {hi : UInt64}

/-! ### Arithmetic notation: the ambient operators wrap -/

instance : Add (TopBoundedUInt64 hi) := ⟨wrapping_add⟩
instance : Sub (TopBoundedUInt64 hi) := ⟨wrapping_sub⟩
instance : Mul (TopBoundedUInt64 hi) := ⟨wrapping_mul⟩
instance : Div (TopBoundedUInt64 hi) := ⟨div⟩
instance : Mod (TopBoundedUInt64 hi) := ⟨mod⟩

/-- `+` is wrapping addition. -/
@[simp] theorem add_eq (a b : TopBoundedUInt64 hi) : a + b = wrapping_add a b := rfl

/-- `-` is wrapping subtraction. -/
@[simp] theorem sub_eq (a b : TopBoundedUInt64 hi) : a - b = wrapping_sub a b := rfl

/-- `*` is wrapping multiplication. -/
@[simp] theorem mul_eq (a b : TopBoundedUInt64 hi) : a * b = wrapping_mul a b := rfl

/-- `/` is the total division. -/
@[simp] theorem div_eq (a b : TopBoundedUInt64 hi) : a / b = div a b := rfl

/-- `%` is the total remainder. -/
@[simp] theorem mod_eq (a b : TopBoundedUInt64 hi) : a % b = mod a b := rfl

theorem toNat_add (a b : TopBoundedUInt64 hi) :
    (a + b).toNat = (a.toNat + b.toNat) % period hi := toNat_wrapping_add a b

theorem toNat_mul (a b : TopBoundedUInt64 hi) :
    (a * b).toNat = (a.toNat * b.toNat) % period hi := toNat_wrapping_mul a b

theorem toNat_div' (a b : TopBoundedUInt64 hi) : (a / b).toNat = a.toNat / b.toNat :=
  toNat_div a b

theorem toNat_mod' (a b : TopBoundedUInt64 hi) : (a % b).toNat = a.toNat % b.toNat :=
  toNat_mod a b

/-! ### The checked variants, named as in core -/

/-- The checked sum, `none` on overflow. -/
abbrev add? (a b : TopBoundedUInt64 hi) : Option (TopBoundedUInt64 hi) := checked_add a b

/-- The checked difference, `none` on underflow. -/
abbrev sub? (a b : TopBoundedUInt64 hi) : Option (TopBoundedUInt64 hi) := checked_sub a b

/-- The checked product, `none` on overflow. -/
abbrev mul? (a b : TopBoundedUInt64 hi) : Option (TopBoundedUInt64 hi) := checked_mul a b

/-- The checked quotient, `none` on a zero divisor. -/
abbrev div? (a b : TopBoundedUInt64 hi) : Option (TopBoundedUInt64 hi) := checked_div a b

/-- The checked remainder, `none` on a zero divisor. -/
abbrev mod? (a b : TopBoundedUInt64 hi) : Option (TopBoundedUInt64 hi) := checked_mod a b

/-! ### `BEq` -/

theorem beq_iff_toNat_eq {a b : TopBoundedUInt64 hi} : (a == b) = true ↔ a.toNat = b.toNat := by
  rw [beq_iff_eq, ext_iff]

/-! ### `Ord` and its lawfulness -/

instance : Ord (TopBoundedUInt64 hi) := ⟨fun a b => compare a.toNat b.toNat⟩

theorem compare_eq (a b : TopBoundedUInt64 hi) : compare a b = compare a.toNat b.toNat := rfl

instance : Std.OrientedOrd (TopBoundedUInt64 hi) where
  eq_swap {a b} := by
    rw [compare_eq, compare_eq]
    exact Std.OrientedCmp.eq_swap (cmp := (compare : Nat → Nat → Ordering))

instance : Std.ReflCmp (compare (α := TopBoundedUInt64 hi)) where
  compare_self {a} := by
    rw [compare_eq]
    exact Std.ReflCmp.compare_self

instance : Std.TransOrd (TopBoundedUInt64 hi) where
  isLE_trans {a b c} h₁ h₂ := by
    rw [compare_eq] at h₁ h₂ ⊢
    exact Std.TransCmp.isLE_trans h₁ h₂

instance : Std.LawfulEqOrd (TopBoundedUInt64 hi) where
  eq_of_compare {a b} h := by
    rw [compare_eq] at h
    exact ext (Std.LawfulEqCmp.eq_of_compare h)

/-- Comparison is comparison of the denoted natural numbers. -/
theorem compare_eq_eq_iff {a b : TopBoundedUInt64 hi} :
    compare a b = Ordering.eq ↔ a = b :=
  ⟨fun h => Std.LawfulEqCmp.eq_of_compare h, fun h => h ▸ Std.ReflCmp.compare_self⟩

theorem compare_eq_lt_iff {a b : TopBoundedUInt64 hi} :
    compare a b = Ordering.lt ↔ a.toNat < b.toNat := by
  rw [compare_eq, Nat.compare_eq_lt]

/-! ### `Hashable` -/

instance : Hashable (TopBoundedUInt64 hi) := ⟨fun a => hash a.toNat⟩

theorem hash_eq (a : TopBoundedUInt64 hi) : hash a = hash a.toNat := rfl

instance : LawfulHashable (TopBoundedUInt64 hi) where
  hash_eq {a b} h := by
    rw [hash_eq, hash_eq, beq_iff_eq.mp h]

/-! ### `ToString` -/

instance : ToString (TopBoundedUInt64 hi) := ⟨fun a => toString a.toNat⟩

theorem toString_eq (a : TopBoundedUInt64 hi) : toString a = toString a.toNat := rfl

end TopBoundedUInt64
