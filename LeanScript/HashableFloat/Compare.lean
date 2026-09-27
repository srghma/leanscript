module

public import Batteries.Data.Float.Lemmas

@[expose] public section

set_option autoImplicit false

/-!
# The IEEE order of floats, away from `NaN`

`Float.lt`, `Float.le` and `Float.beq` (and their `Float32` counterparts) are all defined
through one function of the logical model, `Float.Model.UnpackedFloat.compare`, which returns
`none` exactly when one side is `NaN`.  This file proves the two facts about it that make the
order of floats *linear* once `NaN` is excluded:

* it is **oriented**: swapping the arguments swaps the answer (`compare_swap`);
* `UnpackedFloat.le` is **transitive** (`le_trans`).

It then packages them for any type `α` whose values unpack to non-`NaN` floats and whose
`compare` agrees with `UnpackedFloat.compare` (`oriented_of`, `isLE_iff_of`, `trans_of`).
`HashableFloat` and `HashableFloat32` use this package for their `Ord` instances.
-/

namespace LeanScript.FloatOrder

open Float.Model

/-- `UnpackedFloat.compare` is oriented: swapping the arguments swaps the answer. -/
theorem compare_swap (x y : UnpackedFloat) :
    y.compare x = (x.compare y).map Ordering.swap := by
  fun_cases UnpackedFloat.compare x y <;>
    simp_all [UnpackedFloat.compare, Ordering.swap_then]
  · cases y <;> rfl
  · rename_i a b; cases a <;> cases b <;> decide
  · rename_i m₁ e₁ _ m₂ e₂ _
    rw [Std.OrientedOrd.eq_swap (a := e₂), Std.OrientedOrd.eq_swap (a := m₂)]
    simp
  · rename_i m₁ e₁ _ m₂ e₂ _
    rw [Std.OrientedOrd.eq_swap (a := e₂), Std.OrientedOrd.eq_swap (a := m₂)]

/-- The lexicographic comparison of (exponent, mantissa) is `≤`. -/
theorem lex_isLE (e₁ e₂ : Int) (m₁ m₂ : Nat) :
    ((compare e₁ e₂).then (compare m₁ m₂)).isLE ↔ e₁ < e₂ ∨ (e₁ = e₂ ∧ m₁ ≤ m₂) := by
  rcases h : compare e₁ e₂ with _ | _ | _
  · simp [Int.compare_eq_lt] at h; simp [h]
  · simp at h; subst h; simp [Nat.isLE_compare]
  · simp [Int.compare_eq_gt] at h; simp; omega

/-- The lexicographic comparison of (exponent, mantissa) is `≥`. -/
theorem lex_isGE (e₁ e₂ : Int) (m₁ m₂ : Nat) :
    ((compare e₁ e₂).then (compare m₁ m₂)).isGE ↔ e₂ < e₁ ∨ (e₁ = e₂ ∧ m₂ ≤ m₁) := by
  rcases h : compare e₁ e₂ with _ | _ | _
  · simp [Int.compare_eq_lt] at h; simp; omega
  · simp at h; subst h; simp [Nat.isGE_compare]
  · simp [Int.compare_eq_gt] at h; simp [h]

/-- `UnpackedFloat.le` is transitive (for every input, canonical or not). -/
theorem le_trans {x y z : UnpackedFloat} : x.le y → y.le z → x.le z := by
  rcases x with ⟨_|_⟩ | _ | ⟨_|_⟩ | ⟨_|_, m1, e1, _⟩ <;>
  rcases y with ⟨_|_⟩ | _ | ⟨_|_⟩ | ⟨_|_, m2, e2, _⟩ <;>
  rcases z with ⟨_|_⟩ | _ | ⟨_|_⟩ | ⟨_|_, m3, e3, _⟩ <;>
  simp [UnpackedFloat.le, UnpackedFloat.compare, lex_isLE, lex_isGE] <;> (try omega) <;> decide

/-- Two unpacked floats other than `NaN` are always comparable. -/
theorem compare_isSome {x y : UnpackedFloat} (hx : x ≠ .notANumber) (hy : y ≠ .notANumber) :
    (x.compare y).isSome := by
  fun_cases UnpackedFloat.compare x y <;> simp_all

section Package

variable {α : Type} (u : α → UnpackedFloat) (cmp : α → α → Ordering)
  (hcmp : ∀ a b, some (cmp a b) = (u a).compare (u b))
include hcmp

/-- A comparison that agrees with `UnpackedFloat.compare` is oriented. -/
theorem oriented_of (a b : α) : cmp a b = (cmp b a).swap := by
  have h := compare_swap (u b) (u a)
  rw [← hcmp, ← hcmp] at h
  simp only [Option.map_some, Option.some.injEq] at h
  exact h

/-- A comparison that agrees with `UnpackedFloat.compare` answers `≤` exactly when
    `UnpackedFloat.le` does. -/
theorem isLE_iff_of (a b : α) : (cmp a b).isLE ↔ (u a).le (u b) := by
  simp only [UnpackedFloat.le, ← hcmp, Option.any_some]

/-- A comparison that agrees with `UnpackedFloat.compare` is transitive. -/
theorem trans_of {a b c : α} : (cmp a b).isLE → (cmp b c).isLE → (cmp a c).isLE := by
  rw [isLE_iff_of u cmp hcmp, isLE_iff_of u cmp hcmp, isLE_iff_of u cmp hcmp]
  exact le_trans

end Package

end LeanScript.FloatOrder

end
