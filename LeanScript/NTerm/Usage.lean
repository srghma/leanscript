module

@[expose] public section

set_option autoImplicit false

/-!
# Usage counters: `0 | 1 | ω`

Every binder of a normal-form term (`LeanScript.NTerm`) carries a `Usage`: how often the
variable it binds is used.  It is an abstraction of the number of occurrences:

* `zero` — never used.  This one is **enforced by the types**: a variable whose binder says
  `zero` cannot be referenced (`NTerm.UVar`, `NTerm.KVar` need `use ≠ .zero`), so a binding
  annotated `zero` is dead and can be dropped without looking at its body;
* `one` — used once, and not inside the body of a closure, a loop or a delay (a body that
  may run many times);
* `many` (ω) — anything else.

`Usage` is a commutative monoid under `+` (`zero` is the unit, everything else saturates at
`many`); `Usage.scale` is the usage of occurrences that sit inside a body that may run many
times.
-/

namespace LeanScript.NTerm

/-- How often a variable is used: never, once, or any number of times (ω). -/
inductive Usage where
  | zero
  | one
  | many
  deriving DecidableEq, Repr, Hashable, Inhabited

namespace Usage

/-- `==` is `decide (· = ·)`, so it is lawful. -/
instance : BEq Usage := instBEqOfDecidableEq

example : LawfulBEq Usage := inferInstance

/-- The usage of the occurrences of two parts together: `0 + u = u`, and two uses are ω. -/
def add : Usage → Usage → Usage
  | .zero, u => u
  | u, .zero => u
  | _, _ => .many

instance : Add Usage := ⟨add⟩

/-- The usage of occurrences inside a body that may run many times (a closure, a loop, a
    delay): any use is ω. -/
def scale : Usage → Usage
  | .zero => .zero
  | _ => .many

/-- The abstraction of a number of occurrences. -/
def ofCount : Nat → Usage
  | 0 => .zero
  | 1 => .one
  | _ => .many

/-- Whether the variable is used at all. -/
def isUsed : Usage → Bool
  | .zero => false
  | _ => true

@[simp] theorem zero_add (u : Usage) : .zero + u = u := by cases u <;> rfl
@[simp] theorem add_zero (u : Usage) : u + .zero = u := by cases u <;> rfl
theorem add_comm (u v : Usage) : u + v = v + u := by cases u <;> cases v <;> rfl
theorem add_assoc (u v w : Usage) : u + v + w = u + (v + w) := by
  cases u <;> cases v <;> cases w <;> rfl

/-- A sum is unused exactly when both parts are. -/
@[simp] theorem add_eq_zero (u v : Usage) : u + v = .zero ↔ u = .zero ∧ v = .zero := by
  cases u <;> cases v <;> decide

@[simp] theorem scale_eq_zero (u : Usage) : u.scale = .zero ↔ u = .zero := by
  cases u <;> decide

@[simp] theorem isUsed_eq_false (u : Usage) : u.isUsed = false ↔ u = .zero := by
  cases u <;> decide

theorem ofCount_eq_zero (n : Nat) : ofCount n = .zero ↔ n = 0 := by
  match n with
  | 0 => decide
  | 1 => decide
  | _ + 2 => simp [ofCount]

end Usage

end LeanScript.NTerm

end
