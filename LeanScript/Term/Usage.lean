module

@[expose] public section

set_option autoImplicit false

/-!
# Usage annotations: `0 | 1 | ω` and `1 | ω`

Every binder of a normal-form term (`LeanScript.Term`) carries a usage annotation: how often
the variable it binds is used.  There are two kinds of binders, with two types of annotations:

* **pattern binders** — the parameter of a closure, the binders of a loop body, the fields of
  a case analysis, the parameter of a join point — name something that exists anyway, and may
  legitimately be unused (`fun _ => 3`, a field that is not read).  They carry a `Usage01ω`:
  `zero`, `one` or `many`;
* **definition binders** — `letV`, `letE` and the join point itself — introduce something only
  to be used: an unused one is dead code.  They carry a `Usage1ω`: `one` or `many`.  (The type
  does not check that the annotation is the actual count; `Term.dce` recomputes it.)

The meaning of the annotations:

* `zero` — never used.  This one is **enforced by the types**: a pattern binder annotated
  `zero` cannot be referenced (`UVar.head` needs `use ≠ .zero`);
* `one` — used at most once on every path, and not inside the body of a closure, a loop or a
  delay (a body that may run many times);
* `many` (ω) — anything else.

Counting (`LeanScript.Term.Occ`) adds the usages of the parts of a straight-line piece of code
(`Usage01ω.add`: `1 + 1 = ω`), takes the maximum over the arms of a branch (`Usage01ω.max`:
only one arm runs, so a variable used once in each arm is used once), and scales the usages
inside a body that may run many times to `ω` (`Usage01ω.scale`).
-/

namespace LeanScript

/-- The usage of a pattern binder: never, once, or any number of times (ω). -/
inductive Usage01ω where
  | zero
  | one
  | many
  deriving DecidableEq, Repr, Hashable, Inhabited

/-- The usage of a definition binder: once, or any number of times (ω).  Never `zero`: an
    unused definition is dead. -/
inductive Usage1ω where
  | one
  | many
  deriving DecidableEq, Repr, Hashable, Inhabited

/-- `==` is `decide (· = ·)`, so it is lawful. -/
instance : BEq Usage01ω := instBEqOfDecidableEq

/-- `==` is `decide (· = ·)`, so it is lawful. -/
instance : BEq Usage1ω := instBEqOfDecidableEq

example : LawfulBEq Usage01ω := inferInstance
example : LawfulBEq Usage1ω := inferInstance

namespace Usage1ω

/-- A definition usage as a pattern usage. -/
def toUsage01ω : Usage1ω → Usage01ω
  | .one => .one
  | .many => .many

instance : Coe Usage1ω Usage01ω := ⟨toUsage01ω⟩

@[simp] theorem toUsage01ω_one : toUsage01ω .one = .one := rfl
@[simp] theorem toUsage01ω_many : toUsage01ω .many = .many := rfl

/-- A definition usage is never `zero`. -/
@[simp] theorem toUsage01ω_ne_zero (u : Usage1ω) : u.toUsage01ω ≠ .zero := by
  cases u <;> decide

theorem toUsage01ω_injective {u v : Usage1ω} (h : u.toUsage01ω = v.toUsage01ω) : u = v := by
  cases u <;> cases v <;> first | rfl | cases h

end Usage1ω

namespace Usage01ω

/-- The usage of the occurrences of two parts together: `0 + u = u`, and two uses are ω. -/
def add : Usage01ω → Usage01ω → Usage01ω
  | .zero, u => u
  | u, .zero => u
  | _, _ => .many

instance : Add Usage01ω := ⟨add⟩

/-- The usage of the occurrences in two arms of a branch, only one of which runs: the larger
    one (`zero ≤ one ≤ many`). -/
def max : Usage01ω → Usage01ω → Usage01ω
  | .zero, u => u
  | u, .zero => u
  | .one, .one => .one
  | _, _ => .many

/-- The usage of occurrences inside a body that may run many times (a closure, a loop, a
    delay): any use is ω. -/
def scale : Usage01ω → Usage01ω
  | .zero => .zero
  | _ => .many

/-- The abstraction of a number of occurrences. -/
def ofCount : Nat → Usage01ω
  | 0 => .zero
  | 1 => .one
  | _ => .many

/-- Whether the variable is used at all. -/
def isUsed : Usage01ω → Bool
  | .zero => false
  | _ => true

/-- A usage that is not `zero`, as a definition usage. -/
def toUsage1ω : (u : Usage01ω) → u ≠ .zero → Usage1ω
  | .zero, h => absurd rfl h
  | .one, _ => .one
  | .many, _ => .many

@[simp] theorem toUsage1ω_toUsage01ω (u : Usage01ω) (h : u ≠ .zero) :
    (u.toUsage1ω h).toUsage01ω = u := by
  cases u
  · exact absurd rfl h
  · rfl
  · rfl

@[simp] theorem zero_add (u : Usage01ω) : .zero + u = u := by cases u <;> rfl
@[simp] theorem add_zero (u : Usage01ω) : u + .zero = u := by cases u <;> rfl
theorem add_comm (u v : Usage01ω) : u + v = v + u := by cases u <;> cases v <;> rfl
theorem add_assoc (u v w : Usage01ω) : u + v + w = u + (v + w) := by
  cases u <;> cases v <;> cases w <;> rfl

@[simp] theorem zero_max (u : Usage01ω) : max .zero u = u := by cases u <;> rfl
@[simp] theorem max_zero (u : Usage01ω) : max u .zero = u := by cases u <;> rfl
@[simp] theorem max_self (u : Usage01ω) : max u u = u := by cases u <;> rfl
theorem max_comm (u v : Usage01ω) : max u v = max v u := by cases u <;> cases v <;> rfl
theorem max_assoc (u v w : Usage01ω) : max (max u v) w = max u (max v w) := by
  cases u <;> cases v <;> cases w <;> rfl

/-- One use in each arm of a branch is one use (with `add` it would be ω). -/
example : max .one .one = .one := rfl
example : Usage01ω.one + .one = .many := rfl

/-- A sum is unused exactly when both parts are. -/
@[simp] theorem add_eq_zero (u v : Usage01ω) : u + v = .zero ↔ u = .zero ∧ v = .zero := by
  cases u <;> cases v <;> decide

/-- A maximum is unused exactly when both parts are. -/
@[simp] theorem max_eq_zero (u v : Usage01ω) : max u v = .zero ↔ u = .zero ∧ v = .zero := by
  cases u <;> cases v <;> decide

@[simp] theorem scale_eq_zero (u : Usage01ω) : u.scale = .zero ↔ u = .zero := by
  cases u <;> decide

@[simp] theorem isUsed_eq_false (u : Usage01ω) : u.isUsed = false ↔ u = .zero := by
  cases u <;> decide

theorem ofCount_eq_zero (n : Nat) : ofCount n = .zero ↔ n = 0 := by
  match n with
  | 0 => decide
  | 1 => decide
  | _ + 2 => simp [ofCount]

end Usage01ω

end LeanScript

end
