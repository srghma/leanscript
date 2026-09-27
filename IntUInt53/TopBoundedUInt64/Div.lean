import IntUInt53.TopBoundedUInt64.Mul
import Aesop

/-!
# Division and remainder on `TopBoundedUInt64`

Division differs from addition, subtraction and multiplication in one respect:
on an unsigned bounded type it can never overflow, because the quotient
`a / b` and the remainder `a % b` are both at most `a`, which is in range
already.  The only way division can fail is a zero divisor.

The four variants are therefore all defined from one total function, following
the convention of the Lean core library that `n / 0 = 0` and `n % 0 = n` on
`Nat`:

* `checked_div` / `checked_mod`         — `none` exactly when the divisor is `0`;
* `overflowing_div` / `overflowing_mod` — the value together with a flag that is
  `true` exactly when the divisor is `0`;
* `wrapping_div` / `wrapping_mod`       — the total function itself (nothing ever
  wraps);
* `saturating_div` / `saturating_mod`   — the total function itself (nothing is
  ever clamped).

Every statement below is an equation between exact natural numbers.
-/

set_option autoImplicit false

namespace TopBoundedUInt64

variable {hi : UInt64}

/-! ### The exact quotient and remainder -/

/-- The exact quotient of the numbers denoted by `a` and `b` (`0` if `b` is `0`). -/
def exactDiv (a b : TopBoundedUInt64 hi) : Nat := a.toNat / b.toNat

/-- The exact remainder of the numbers denoted by `a` and `b` (`a` if `b` is `0`). -/
def exactMod (a b : TopBoundedUInt64 hi) : Nat := a.toNat % b.toNat

theorem exactDiv_le (a b : TopBoundedUInt64 hi) : exactDiv a b ≤ a.toNat :=
  Nat.div_le_self _ _

theorem exactMod_le (a b : TopBoundedUInt64 hi) : exactMod a b ≤ a.toNat :=
  Nat.mod_le _ _

/-- The quotient is always representable: it is at most the dividend. -/
theorem inRange_exactDiv (a b : TopBoundedUInt64 hi) : InRange hi (exactDiv a b) :=
  Nat.le_trans (exactDiv_le a b) (toNat_le a)

/-- The remainder is always representable: it is at most the dividend. -/
theorem inRange_exactMod (a b : TopBoundedUInt64 hi) : InRange hi (exactMod a b) :=
  Nat.le_trans (exactMod_le a b) (toNat_le a)

/-- Division by zero is the only failure mode. -/
def divByZero (b : TopBoundedUInt64 hi) : Prop := b.toNat = 0

instance (b : TopBoundedUInt64 hi) : Decidable (divByZero b) := by
  unfold divByZero; infer_instance

theorem divByZero_iff_eq_minVal {b : TopBoundedUInt64 hi} : divByZero b ↔ b = minVal hi := by
  unfold divByZero
  rw [ext_iff, toNat_minVal]

/-! ### The total division and remainder -/

/-- Total division, with `a / 0 = 0` as in the core library. -/
def div (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi :=
  ofNatLe hi (exactDiv a b) (inRange_exactDiv a b)

/-- Total remainder, with `a % 0 = a` as in the core library. -/
def mod (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi :=
  ofNatLe hi (exactMod a b) (inRange_exactMod a b)

@[simp] theorem toNat_div (a b : TopBoundedUInt64 hi) :
    (div a b).toNat = a.toNat / b.toNat := by
  unfold div exactDiv; exact toNat_ofNatLe (a.toNat / b.toNat) (inRange_exactDiv a b)

@[simp] theorem toNat_mod (a b : TopBoundedUInt64 hi) :
    (mod a b).toNat = a.toNat % b.toNat := by
  unfold mod exactMod; exact toNat_ofNatLe (a.toNat % b.toNat) (inRange_exactMod a b)

/-- The defining property of division with remainder. -/
theorem div_add_mod (a b : TopBoundedUInt64 hi) :
    b.toNat * (div a b).toNat + (mod a b).toNat = a.toNat := by
  rw [toNat_div, toNat_mod]
  exact Nat.div_add_mod a.toNat b.toNat

/-- The remainder is smaller than a nonzero divisor. -/
theorem toNat_mod_lt {a b : TopBoundedUInt64 hi} (h : ¬ divByZero b) :
    (mod a b).toNat < b.toNat := by
  rw [toNat_mod]
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

/-- The quotient is at most the dividend. -/
theorem toNat_div_le (a b : TopBoundedUInt64 hi) : (div a b).toNat ≤ a.toNat := by
  rw [toNat_div]; exact Nat.div_le_self _ _

/-! ### The checked variants -/

/-- Checked division: `none` exactly on a zero divisor. -/
def checked_div (a b : TopBoundedUInt64 hi) : Option (TopBoundedUInt64 hi) :=
  if b.toNat = 0 then none else some (div a b)

/-- Checked remainder: `none` exactly on a zero divisor. -/
def checked_mod (a b : TopBoundedUInt64 hi) : Option (TopBoundedUInt64 hi) :=
  if b.toNat = 0 then none else some (mod a b)

theorem checked_div_eq_none_iff {a b : TopBoundedUInt64 hi} :
    checked_div a b = none ↔ divByZero b := by
  unfold checked_div divByZero; split <;> simp_all

theorem checked_mod_eq_none_iff {a b : TopBoundedUInt64 hi} :
    checked_mod a b = none ↔ divByZero b := by
  unfold checked_mod divByZero; split <;> simp_all

theorem checked_div_eq_some_iff {a b c : TopBoundedUInt64 hi} :
    checked_div a b = some c ↔ (b.toNat ≠ 0 ∧ c.toNat = a.toNat / b.toNat) := by
  unfold checked_div
  split
  · next h => simp_all
  · next h =>
    constructor
    · intro hs; exact ⟨h, by rw [← Option.some.inj hs, toNat_div]⟩
    · intro hv; exact congrArg some (ext (by rw [toNat_div, hv.2]))

theorem checked_mod_eq_some_iff {a b c : TopBoundedUInt64 hi} :
    checked_mod a b = some c ↔ (b.toNat ≠ 0 ∧ c.toNat = a.toNat % b.toNat) := by
  unfold checked_mod
  split
  · next h => simp_all
  · next h =>
    constructor
    · intro hs; exact ⟨h, by rw [← Option.some.inj hs, toNat_mod]⟩
    · intro hv; exact congrArg some (ext (by rw [toNat_mod, hv.2]))

/-- Exactness: whenever checked division succeeds, its result is the exact quotient. -/
theorem toNat_of_checked_div {a b c : TopBoundedUInt64 hi} (h : checked_div a b = some c) :
    c.toNat = a.toNat / b.toNat := (checked_div_eq_some_iff.mp h).2

/-- Exactness: whenever the checked remainder succeeds, its result is exact. -/
theorem toNat_of_checked_mod {a b c : TopBoundedUInt64 hi} (h : checked_mod a b = some c) :
    c.toNat = a.toNat % b.toNat := (checked_mod_eq_some_iff.mp h).2

theorem checked_div_of_ne_zero {a b : TopBoundedUInt64 hi} (h : ¬ divByZero b) :
    checked_div a b = some (div a b) := ite_eq_right h

theorem checked_mod_of_ne_zero {a b : TopBoundedUInt64 hi} (h : ¬ divByZero b) :
    checked_mod a b = some (mod a b) := ite_eq_right h

/-! ### The wrapping variants -/

/-- Wrapping division.  Nothing can wrap: the quotient of two representable
values is representable, so this is the total division. -/
def wrapping_div (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi := div a b

/-- Wrapping remainder.  Nothing can wrap. -/
def wrapping_mod (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi := mod a b

@[simp] theorem toNat_wrapping_div (a b : TopBoundedUInt64 hi) :
    (wrapping_div a b).toNat = a.toNat / b.toNat := toNat_div a b

@[simp] theorem toNat_wrapping_mod (a b : TopBoundedUInt64 hi) :
    (wrapping_mod a b).toNat = a.toNat % b.toNat := toNat_mod a b

/-! ### The overflowing variants -/

/-- Overflowing division: the quotient together with a flag that is `true`
exactly on a zero divisor (the only way division can fail). -/
def overflowing_div (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi × Bool :=
  (div a b, decide (b.toNat = 0))

/-- Overflowing remainder: the remainder together with a flag that is `true`
exactly on a zero divisor. -/
def overflowing_mod (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi × Bool :=
  (mod a b, decide (b.toNat = 0))

@[simp] theorem overflowing_div_fst (a b : TopBoundedUInt64 hi) :
    (overflowing_div a b).1 = div a b := rfl

@[simp] theorem overflowing_mod_fst (a b : TopBoundedUInt64 hi) :
    (overflowing_mod a b).1 = mod a b := rfl

theorem overflowing_div_snd_iff {a b : TopBoundedUInt64 hi} :
    (overflowing_div a b).2 = true ↔ divByZero b := by
  unfold overflowing_div divByZero; simp

theorem overflowing_mod_snd_iff {a b : TopBoundedUInt64 hi} :
    (overflowing_mod a b).2 = true ↔ divByZero b := by
  unfold overflowing_mod divByZero; simp

/-! ### The saturating variants -/

/-- Saturating division.  Nothing can be clamped: the quotient is always
representable, so this is the total division. -/
def saturating_div (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi := div a b

/-- Saturating remainder.  Nothing can be clamped. -/
def saturating_mod (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi := mod a b

@[simp] theorem toNat_saturating_div (a b : TopBoundedUInt64 hi) :
    (saturating_div a b).toNat = a.toNat / b.toNat := toNat_div a b

@[simp] theorem toNat_saturating_mod (a b : TopBoundedUInt64 hi) :
    (saturating_mod a b).toNat = a.toNat % b.toNat := toNat_mod a b

/-! ### Agreement of the four variants -/

/-- On a nonzero divisor all four variants of division denote the exact
quotient, and the overflow flag is `false`. -/
theorem div_variants_agree {a b : TopBoundedUInt64 hi} (h : ¬ divByZero b) :
    (∃ c, checked_div a b = some c ∧ c.toNat = a.toNat / b.toNat) ∧
      (wrapping_div a b).toNat = a.toNat / b.toNat ∧
      (overflowing_div a b).1.toNat = a.toNat / b.toNat ∧
      (overflowing_div a b).2 = false ∧
      (saturating_div a b).toNat = a.toNat / b.toNat := by
  refine ⟨⟨div a b, checked_div_of_ne_zero h, toNat_div a b⟩, toNat_div a b, toNat_div a b,
    ?_, toNat_div a b⟩
  cases hb : (overflowing_div a b).2 with
  | false => rfl
  | true => exact absurd (overflowing_div_snd_iff.mp hb) h

/-- On a nonzero divisor all four variants of the remainder denote the exact
remainder, and the overflow flag is `false`. -/
theorem mod_variants_agree {a b : TopBoundedUInt64 hi} (h : ¬ divByZero b) :
    (∃ c, checked_mod a b = some c ∧ c.toNat = a.toNat % b.toNat) ∧
      (wrapping_mod a b).toNat = a.toNat % b.toNat ∧
      (overflowing_mod a b).1.toNat = a.toNat % b.toNat ∧
      (overflowing_mod a b).2 = false ∧
      (saturating_mod a b).toNat = a.toNat % b.toNat := by
  refine ⟨⟨mod a b, checked_mod_of_ne_zero h, toNat_mod a b⟩, toNat_mod a b, toNat_mod a b,
    ?_, toNat_mod a b⟩
  cases hb : (overflowing_mod a b).2 with
  | false => rfl
  | true => exact absurd (overflowing_mod_snd_iff.mp hb) h

/-! ### Laws -/

/-- Division of a value by itself is `1`, for a nonzero value. -/
theorem toNat_div_self {a : TopBoundedUInt64 hi} (h : ¬ divByZero a) :
    (div a a).toNat = 1 := by
  rw [toNat_div]
  exact Nat.div_self (Nat.pos_of_ne_zero h)

/-- A value is divisible by `b` exactly when the remainder is `0`; in that case
multiplying the quotient back by `b` recovers the value. -/
theorem mul_div_of_mod_eq_zero {a b : TopBoundedUInt64 hi} (h : (mod a b).toNat = 0) :
    b.toNat * (div a b).toNat = a.toNat := by
  have := div_add_mod a b
  omega

/-- Dividing by a larger value gives `0`. -/
theorem toNat_div_eq_zero_of_lt {a b : TopBoundedUInt64 hi} (h : a.toNat < b.toNat) :
    (div a b).toNat = 0 := by
  rw [toNat_div]
  exact Nat.div_eq_of_lt h

/-- Division is monotone in the dividend. -/
theorem toNat_div_le_div_of_le {a a' b : TopBoundedUInt64 hi} (h : a.toNat ≤ a'.toNat) :
    (div a b).toNat ≤ (div a' b).toNat := by
  rw [toNat_div, toNat_div]
  exact Nat.div_le_div_right h

end TopBoundedUInt64
