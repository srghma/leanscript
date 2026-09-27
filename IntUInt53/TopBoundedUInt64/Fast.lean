import IntUInt53.TopBoundedUInt64.Add
import IntUInt53.TopBoundedUInt64.Sub
import IntUInt53.TopBoundedUInt64.Mul
import IntUInt53.TopBoundedUInt64.Div

/-!
# A machine-word implementation of the operations on `TopBoundedUInt64`

The operations of the previous modules are *specified* through `toNat`: each of
them converts its arguments to natural numbers, does the arithmetic there —
where it is exact and unbounded — and converts back.  That is the right way to
say what the operations mean, but it is not the way a machine should compute
them: a `Nat` is a GMP integer, so the computation allocates even though every
value involved fits in a 64-bit word.

This module supplies, for each operation, an implementation that stays inside
`UInt64`, proves it equal to the specification, and registers the equation with
`@[csimp]`.  The compiler then uses the machine implementation while the kernel
still sees only the original definition, so nothing is taken on trust:
`@[csimp]` equations are ordinary theorems (unlike the `implemented_by`
attribute, which is not used anywhere in this development).

Two side conditions appear, both tested at run time on the *bound* only — one
comparison per call, with the bound typically a literal:

* `smallBound hi` (`hi ≤ 2 ^ 63 - 1`) guarantees that the machine sum of two
  values in range cannot wrap a 64-bit word, which is what makes the fast paths
  for addition and for the wrapping subtraction correct.  It holds for
  `UInt53`.
* `pow2Period hi` (the period `hi + 1` is a power of two) makes the wrapping
  product computable as a mask of the low 64 bits of the machine product.  It
  also holds for `UInt53`, whose period is `2 ^ 53`.

When a side condition fails the fast path falls back to the original `Nat`
computation, so every equation below holds for *every* bound.
-/

set_option autoImplicit false

open BoundedWordAux

namespace TopBoundedUInt64

variable {hi : UInt64}

/-! ### Building a value from a machine word -/

/-- Build a value directly from a machine word that is known to be in range.  Unlike
`ofNatLe` this involves no `Nat` at all, so it is the constructor the fast paths use. -/
def ofWordLe (hi : UInt64) (v : UInt64) (h : v ≤ hi) : TopBoundedUInt64 hi := ⟨v, h⟩

@[simp] theorem toNat_ofWordLe (v : UInt64) (h : v ≤ hi) :
    (ofWordLe hi v h).toNat = v.toNat := rfl

/-- The number denoted by a value is the number denoted by its underlying word. -/
theorem toNat_val (a : TopBoundedUInt64 hi) : a.val.toNat = a.toNat := rfl

/-! ### The two side conditions, and the machine facts they buy -/

/-- The bound is at most `2 ^ 63 - 1`, so that the machine sum of two values in
range cannot wrap. -/
def smallBound (hi : UInt64) : Bool := hi ≤ 0x7fffffffffffffff

theorem smallBound_iff {hi : UInt64} : smallBound hi = true ↔ hi.toNat < 2 ^ 63 := by
  have hc : (0x7fffffffffffffff : UInt64).toNat = 2 ^ 63 - 1 := by decide +kernel
  unfold smallBound
  simp only [decide_eq_true_eq, UInt64.le_iff_toNat_le, hc]
  omega

/-- The period `hi + 1` is a power of two. -/
def pow2Period (hi : UInt64) : Bool := decide (period hi).isPowerOfTwo

theorem pow2Period_iff {hi : UInt64} :
    pow2Period hi = true ↔ ∃ k, period hi = 2 ^ k := by
  unfold pow2Period Nat.isPowerOfTwo
  apply Iff.intro
  · intro a
    grind only
  · intro a
    simp_all only [decide_true]

/-- Under `smallBound`, the machine sum of two values in range is the exact sum. -/
theorem toNat_val_add_of_smallBound (hs : smallBound hi = true) (a b : TopBoundedUInt64 hi) :
    (a.val + b.val).toNat = a.toNat + b.toNat := by
  have ha := toNat_le a
  have hb := toNat_le b
  have hlt := smallBound_iff.mp hs
  have ha' : a.val.toNat = a.toNat := rfl
  have hb' : b.val.toNat = b.toNat := rfl
  rw [UInt64.toNat_add, ha', hb']
  exact Nat.mod_eq_of_lt (by omega)

/-- Machine subtraction is exact when it does not go below zero. -/
theorem toNat_word_sub {x y : UInt64} (h : y.toNat ≤ x.toNat) :
    (x - y).toNat = x.toNat - y.toNat := by
  have hx := UInt64.toNat_lt x
  have hy := UInt64.toNat_lt y
  rw [UInt64.toNat_sub]
  have hrw : 2 ^ 64 - y.toNat + x.toNat = (x.toNat - y.toNat) + 2 ^ 64 := by omega
  rw [hrw, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem toNat_word_one : (1 : UInt64).toNat = 1 := by decide +kernel

/-- Under `pow2Period`, masking with the bound is reduction modulo the period. -/
theorem toNat_and_of_pow2Period (hp : pow2Period hi = true) (x : UInt64) :
    (x &&& hi).toNat = x.toNat % period hi := by
  obtain ⟨k, hk⟩ := pow2Period_iff.mp hp
  have hval : hi.toNat = 2 ^ k - 1 := by
    have hper : period hi = hi.toNat + 1 := rfl
    omega
  rw [UInt64.toNat_and, hval, Nat.and_two_pow_sub_one_eq_mod, hk]

/-- Under `pow2Period`, the period divides `2 ^ 64`, so reducing the low 64 bits of a
number modulo the period is the same as reducing the number itself. -/
theorem mod_period_of_pow2Period (hp : pow2Period hi = true) (n : Nat) :
    n % 2 ^ 64 % period hi = n % period hi := by
  obtain ⟨k, hk⟩ := pow2Period_iff.mp hp
  have hlt : hi.toNat < 2 ^ 64 := UInt64.toNat_lt hi
  have hper : period hi = hi.toNat + 1 := rfl
  have hk64 : k ≤ 64 := by
    refine (Nat.pow_le_pow_iff_right (a := 2) (by omega)).mp ?_
    omega
  exact Nat.mod_mod_of_dvd n (by rw [hk]; exact Nat.pow_dvd_pow 2 hk64)

/-! ### Addition -/

/-- Machine-word checked addition. -/
def checked_add_fast (a b : TopBoundedUInt64 hi) : Option (TopBoundedUInt64 hi) :=
  if smallBound hi then
    if h : a.val + b.val ≤ hi then some (ofWordLe hi (a.val + b.val) h) else none
  else ofNat? hi (exactAdd a b)

@[csimp] theorem checked_add_eq_fast : @checked_add = @checked_add_fast := by
  funext hi a b
  unfold checked_add_fast
  split
  · next hs =>
    have hkey := toNat_val_add_of_smallBound hs a b
    split
    · next h =>
      have hle := uint64_le_iff.mp h
      have hr : InRange hi (exactAdd a b) := by
        unfold InRange exactAdd
        omega
      show ofNat? hi (exactAdd a b) = _
      rw [ofNat?_of_inRange hr]
      refine congrArg some (ext ?_)
      rw [toNat_ofNatLe, toNat_ofWordLe, hkey]
      rfl
    · next h =>
      show ofNat? hi (exactAdd a b) = _
      rw [ofNat?_eq_none_iff]
      intro hc
      exact h (uint64_le_iff.mpr (by unfold InRange exactAdd at hc; omega))
  · rfl

/-- Machine-word wrapping addition. -/
def wrapping_add_fast (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi :=
  if smallBound hi then
    if h : a.val + b.val ≤ hi then ofWordLe hi (a.val + b.val) h
    else if h' : a.val + b.val - hi - 1 ≤ hi then ofWordLe hi (a.val + b.val - hi - 1) h'
    else minVal hi
  else ofNatWrap hi (exactAdd a b)

@[csimp] theorem wrapping_add_eq_fast : @wrapping_add = @wrapping_add_fast := by
  funext hi a b
  unfold wrapping_add_fast
  split
  · next hs =>
    have hkey := toNat_val_add_of_smallBound hs a b
    have ha := toNat_le a
    have hb := toNat_le b
    have hper : period hi = hi.toNat + 1 := rfl
    split
    · next h =>
      have hle := uint64_le_iff.mp h
      apply ext
      rw [toNat_wrapping_add, toNat_ofWordLe, hkey]
      exact Nat.mod_eq_of_lt (by omega)
    · next h =>
      have hgt : hi.toNat < (a.val + b.val).toNat := by
        rcases Nat.lt_or_ge hi.toNat (a.val + b.val).toNat with h' | h'
        · exact h'
        · exact absurd (uint64_le_iff.mpr h') h
      have hsub1 : (a.val + b.val - hi).toNat = (a.val + b.val).toNat - hi.toNat :=
        toNat_word_sub (x := a.val + b.val) (y := hi) (by omega)
      have hone : (1 : UInt64).toNat ≤ (a.val + b.val - hi).toNat := by
        rw [hsub1, toNat_word_one]; omega
      have hsub : (a.val + b.val - hi - 1).toNat = (a.val + b.val).toNat - hi.toNat - 1 := by
        rw [toNat_word_sub hone, hsub1, toNat_word_one]
      split
      · next h' =>
        apply ext
        rw [toNat_wrapping_add, toNat_ofWordLe, hsub, hkey]
        have h1 : a.toNat + b.toNat - hi.toNat - 1 < period hi := by omega
        have h2 : a.toNat + b.toNat
            = (a.toNat + b.toNat - hi.toNat - 1) + period hi := by omega
        rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt h1]
        omega
      · next h' =>
        exact absurd (uint64_le_iff.mpr (by rw [hsub, hkey]; omega)) h'
  · rfl

/-- Machine-word overflowing addition. -/
def overflowing_add_fast (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi × Bool :=
  if smallBound hi then (wrapping_add_fast a b, hi < a.val + b.val)
  else (wrapping_add a b, decide (hi.toNat < exactAdd a b))

@[csimp] theorem overflowing_add_eq_fast : @overflowing_add = @overflowing_add_fast := by
  funext hi a b
  unfold overflowing_add_fast
  split
  · next hs =>
    have hkey := toNat_val_add_of_smallBound hs a b
    have hflag : decide (hi.toNat < exactAdd a b) = decide (hi < a.val + b.val) := by
      have hlt : (hi < a.val + b.val) ↔ (hi.toNat < (a.val + b.val).toNat) :=
        UInt64.lt_iff_toNat_lt
      simp only [exactAdd, ← hkey, hlt]
    show (wrapping_add a b, decide (hi.toNat < exactAdd a b)) = _
    rw [hflag, congrFun (congrFun (congrFun wrapping_add_eq_fast hi) a) b]
  · rfl

/-- Machine-word saturating addition. -/
def saturating_add_fast (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi :=
  if smallBound hi then
    if h : a.val + b.val ≤ hi then ofWordLe hi (a.val + b.val) h else maxVal hi
  else ofNatSat hi (exactAdd a b)

@[csimp] theorem saturating_add_eq_fast : @saturating_add = @saturating_add_fast := by
  funext hi a b
  unfold saturating_add_fast
  split
  · next hs =>
    have hkey := toNat_val_add_of_smallBound hs a b
    split
    · next h =>
      have hle := uint64_le_iff.mp h
      apply ext
      rw [toNat_saturating_add, toNat_ofWordLe, hkey]
      omega
    · next h =>
      have hgt : hi.toNat < (a.val + b.val).toNat := by
        rcases Nat.lt_or_ge hi.toNat (a.val + b.val).toNat with h' | h'
        · exact h'
        · exact absurd (uint64_le_iff.mpr h') h
      apply ext
      rw [toNat_saturating_add, toNat_maxVal]
      omega
  · rfl

/-! ### Subtraction -/

theorem val_sub_le (a b : TopBoundedUInt64 hi) (h : b.val ≤ a.val) : a.val - b.val ≤ hi := by
  have hle := uint64_le_iff.mp h
  have hmax := toNat_le a
  exact uint64_le_iff.mpr
    (by rw [toNat_word_sub hle]; exact Nat.le_trans (Nat.sub_le _ _) hmax)

/-- Machine-word checked subtraction. -/
def checked_sub_fast (a b : TopBoundedUInt64 hi) : Option (TopBoundedUInt64 hi) :=
  if h : b.val ≤ a.val then some (ofWordLe hi (a.val - b.val) (val_sub_le a b h)) else none

@[csimp] theorem checked_sub_eq_fast : @checked_sub = @checked_sub_fast := by
  funext hi a b
  unfold checked_sub_fast checked_sub
  by_cases h : b.val ≤ a.val
  · have hle : b.toNat ≤ a.toNat := uint64_le_iff.mp h
    rw [ite_eq_left hle, dite_eq_left h]
    refine congrArg some (ext ?_)
    rw [toNat_ofNatLe, toNat_ofWordLe, toNat_word_sub hle]
    rfl
  · have hnle : ¬ b.toNat ≤ a.toNat := fun hc => h (uint64_le_iff.mpr hc)
    rw [ite_eq_right hnle, dite_eq_right h]

/-- Machine-word wrapping subtraction. -/
def wrapping_sub_fast (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi :=
  if h : b.val ≤ a.val then ofWordLe hi (a.val - b.val) (val_sub_le a b h)
  else if smallBound hi then
    if h' : a.val + (hi - b.val) + 1 ≤ hi then ofWordLe hi (a.val + (hi - b.val) + 1) h'
    else minVal hi
  else ofNatWrap hi (a.toNat + (period hi - b.toNat))

@[csimp] theorem wrapping_sub_eq_fast : @wrapping_sub = @wrapping_sub_fast := by
  funext hi a b
  unfold wrapping_sub_fast
  have ha := toNat_le a
  have hb := toNat_le b
  have hav := toNat_val a
  have hbv := toNat_val b
  have hper : period hi = hi.toNat + 1 := rfl
  split
  · next h =>
    have hle := uint64_le_iff.mp h
    apply ext
    rw [toNat_wrapping_sub, toNat_ofWordLe, toNat_word_sub hle]
    have h1 : a.toNat + period hi - b.toNat = (a.toNat - b.toNat) + period hi := by omega
    have h2 : a.val.toNat - b.val.toNat = a.toNat - b.toNat := rfl
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), h2]
  · next h =>
    have hgt : a.toNat < b.toNat := by
      rcases Nat.lt_or_ge a.toNat b.toNat with h' | h'
      · exact h'
      · exact absurd (uint64_le_iff.mpr h') h
    split
    · next hs =>
      have hsmall := smallBound_iff.mp hs
      have hbsub : (hi - b.val).toNat = hi.toNat - b.toNat := toNat_word_sub hb
      have hadd : (a.val + (hi - b.val)).toNat = a.toNat + (hi.toNat - b.toNat) := by
        rw [UInt64.toNat_add, hbsub]
        exact Nat.mod_eq_of_lt (by omega)
      have hsum : (a.val + (hi - b.val) + 1).toNat = a.toNat + (hi.toNat - b.toNat) + 1 := by
        rw [UInt64.toNat_add, hadd, toNat_word_one]
        exact Nat.mod_eq_of_lt (by omega)
      split
      · next h' =>
        apply ext
        rw [toNat_wrapping_sub, toNat_ofWordLe, hsum]
        have heq : a.toNat + period hi - b.toNat = a.toNat + (hi.toNat - b.toNat) + 1 := by
          omega
        rw [heq, Nat.mod_eq_of_lt (by omega)]
      · next h' =>
        exact absurd (uint64_le_iff.mpr (by rw [hsum]; omega)) h'
    · next hs => rfl

/-- Machine-word overflowing subtraction. -/
def overflowing_sub_fast (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi × Bool :=
  (wrapping_sub_fast a b, a.val < b.val)

@[csimp] theorem overflowing_sub_eq_fast : @overflowing_sub = @overflowing_sub_fast := by
  funext hi a b
  unfold overflowing_sub_fast
  show (wrapping_sub a b, decide (a.toNat < b.toNat)) = _
  have hflag : decide (a.toNat < b.toNat) = decide (a.val < b.val) := by
    have hlt : (a.val < b.val) ↔ (a.val.toNat < b.val.toNat) := UInt64.lt_iff_toNat_lt
    simp only [decide_eq_decide, hlt]
    rfl
  rw [hflag, congrFun (congrFun (congrFun wrapping_sub_eq_fast hi) a) b]

/-- Machine-word saturating subtraction. -/
def saturating_sub_fast (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi :=
  if h : b.val ≤ a.val then ofWordLe hi (a.val - b.val) (val_sub_le a b h) else minVal hi

@[csimp] theorem saturating_sub_eq_fast : @saturating_sub = @saturating_sub_fast := by
  funext hi a b
  unfold saturating_sub_fast
  split
  · next h =>
    have hle := uint64_le_iff.mp h
    apply ext
    rw [toNat_saturating_sub, toNat_ofWordLe, toNat_word_sub hle]
    rfl
  · next h =>
    have hgt : a.toNat < b.toNat := by
      rcases Nat.lt_or_ge a.toNat b.toNat with h' | h'
      · exact h'
      · exact absurd (uint64_le_iff.mpr h') h
    apply ext
    rw [toNat_saturating_sub, toNat_minVal]
    omega

/-! ### Multiplication -/

/-- The overflow test for multiplication, done with a machine division: the product
`a * b` fits exactly when `a ≤ hi / b`. -/
theorem mul_le_iff_le_div {a b : UInt64} (hb : b.toNat ≠ 0) :
    a.toNat * b.toNat ≤ hi.toNat ↔ a.toNat ≤ (hi / b).toNat := by
  rw [UInt64.toNat_div]
  exact (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hb)).symm

theorem toNat_word_mul_of_le {a b : UInt64} (h : a.toNat * b.toNat ≤ hi.toNat) :
    (a * b).toNat = a.toNat * b.toNat := by
  have hlt := UInt64.toNat_lt hi
  rw [UInt64.toNat_mul]
  exact Nat.mod_eq_of_lt (by omega)

theorem val_eq_zero_iff {b : TopBoundedUInt64 hi} : b.val = 0 ↔ b.toNat = 0 := by
  constructor
  · intro h; show b.val.toNat = 0; rw [h]; decide +kernel
  · intro h; exact UInt64.toNat_inj.mp (by
  simp_all only [UInt64.toNat_zero]
  exact h)

theorem val_mul_le {a b : TopBoundedUInt64 hi} (hb : ¬ b.val = 0) (h : a.val ≤ hi / b.val) :
    a.val * b.val ≤ hi := by
  have hb' : b.val.toNat ≠ 0 := fun hc => hb (val_eq_zero_iff.mpr hc)
  have hle : a.val.toNat * b.val.toNat ≤ hi.toNat :=
    (mul_le_iff_le_div hb').mpr (uint64_le_iff.mp h)
  exact uint64_le_iff.mpr (by rw [toNat_word_mul_of_le hle]; exact hle)

/-- Machine-word checked multiplication: the overflow test is a machine division. -/
def checked_mul_fast (a b : TopBoundedUInt64 hi) : Option (TopBoundedUInt64 hi) :=
  if hb : b.val = 0 then some (minVal hi)
  else if h : a.val ≤ hi / b.val then some (ofWordLe hi (a.val * b.val) (val_mul_le hb h))
  else none

@[csimp] theorem checked_mul_eq_fast : @checked_mul = @checked_mul_fast := by
  funext hi a b
  unfold checked_mul_fast
  split
  · next hb =>
    have hb0 : b.toNat = 0 := val_eq_zero_iff.mp hb
    show ofNat? hi (exactMul a b) = _
    have hr : InRange hi (exactMul a b) := by
      unfold InRange exactMul; rw [hb0]; simp
    rw [ofNat?_of_inRange hr]
    exact congrArg some (ext (by rw [toNat_ofNatLe, toNat_minVal, exactMul, hb0]; simp))
  · next hb =>
    have hb0 : b.toNat ≠ 0 := fun hc => hb (val_eq_zero_iff.mpr hc)
    show ofNat? hi (exactMul a b) = _
    split
    · next h =>
      have hle : a.toNat * b.toNat ≤ hi.toNat := (mul_le_iff_le_div hb0).mpr (uint64_le_iff.mp h)
      have hr : InRange hi (exactMul a b) := hle
      rw [ofNat?_of_inRange hr]
      refine congrArg some (ext ?_)
      simp_all only [ne_eq, toNat_ofWordLe, UInt64.toNat_mul, Nat.reducePow]
      rfl
    · next h =>
      rw [ofNat?_eq_none_iff]
      intro hc
      exact h (uint64_le_iff.mpr ((mul_le_iff_le_div hb0).mp hc))

/-- Machine-word saturating multiplication. -/
def saturating_mul_fast (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi :=
  if hb : b.val = 0 then minVal hi
  else if h : a.val ≤ hi / b.val then ofWordLe hi (a.val * b.val) (val_mul_le hb h)
  else maxVal hi

@[csimp] theorem saturating_mul_eq_fast : @saturating_mul = @saturating_mul_fast := by
  funext hi a b
  unfold saturating_mul_fast
  split
  · next hb =>
    have hb0 : b.toNat = 0 := val_eq_zero_iff.mp hb
    apply ext
    rw [toNat_saturating_mul, toNat_minVal, hb0]
    simp
  · next hb =>
    have hb0 : b.toNat ≠ 0 := fun hc => hb (val_eq_zero_iff.mpr hc)
    split
    · next h =>
      have hle : a.toNat * b.toNat ≤ hi.toNat := (mul_le_iff_le_div hb0).mpr (uint64_le_iff.mp h)
      apply ext
      rw [toNat_saturating_mul, toNat_ofWordLe, toNat_word_mul_of_le hle, toNat_val, toNat_val]
      omega
    · next h =>
      have hgt : hi.toNat < a.toNat * b.toNat := by
        rcases Nat.lt_or_ge hi.toNat (a.toNat * b.toNat) with h' | h'
        · exact h'
        · exact absurd (uint64_le_iff.mpr ((mul_le_iff_le_div hb0).mp h')) h
      apply ext
      rw [toNat_saturating_mul, toNat_maxVal]
      omega

theorem and_le (hp : pow2Period hi = true) (x : UInt64) : x &&& hi ≤ hi := by
  have hlt : (x &&& hi).toNat < period hi := by
    rw [toNat_and_of_pow2Period hp]
    exact Nat.mod_lt _ (period_pos hi)
  have hper : period hi = hi.toNat + 1 := rfl
  exact uint64_le_iff.mpr (by omega)

/-- Machine-word wrapping multiplication.  When the period is a power of two, the exact
product modulo the period is the machine product masked with the bound. -/
def wrapping_mul_fast (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi :=
  if hp : pow2Period hi then ofWordLe hi (a.val * b.val &&& hi) (and_le hp _)
  else ofNatWrap hi (exactMul a b)

@[csimp] theorem wrapping_mul_eq_fast : @wrapping_mul = @wrapping_mul_fast := by
  funext hi a b
  unfold wrapping_mul_fast
  split
  · next hp =>
    apply ext
    rw [toNat_wrapping_mul, toNat_ofWordLe, toNat_and_of_pow2Period hp, UInt64.toNat_mul,
      mod_period_of_pow2Period hp]
    rfl
  · rfl

/-- Machine-word overflowing multiplication. -/
def overflowing_mul_fast (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi × Bool :=
  (wrapping_mul_fast a b, !(b.val == 0) && !(a.val ≤ hi / b.val))

@[csimp] theorem overflowing_mul_eq_fast : @overflowing_mul = @overflowing_mul_fast := by
  funext hi a b
  unfold overflowing_mul_fast
  show (wrapping_mul a b, decide (hi.toNat < exactMul a b)) = _
  have hflag : decide (hi.toNat < exactMul a b)
      = (!(b.val == 0) && !(decide (a.val ≤ hi / b.val))) := by
    by_cases hb : b.val = 0
    · have hb0 : b.toNat = 0 := val_eq_zero_iff.mp hb
      simp [exactMul, hb0, hb]
    · have hb0 : b.toNat ≠ 0 := fun hc => hb (val_eq_zero_iff.mpr hc)
      have hiff : (hi.toNat < a.toNat * b.toNat) ↔ ¬ (a.val ≤ hi / b.val) := by
        rw [← Nat.not_le]
        exact not_congr (Iff.trans (mul_le_iff_le_div hb0) uint64_le_iff.symm)
      have hb' : (b.val == 0) = false := by simp [hb]
      simp only [exactMul, hb', Bool.not_false, Bool.true_and, hiff, decide_not]
  rw [hflag, congrFun (congrFun (congrFun wrapping_mul_eq_fast hi) a) b]

/-! ### Division and remainder -/

theorem val_div_le (a b : TopBoundedUInt64 hi) : a.val / b.val ≤ hi := by
  have hmax := toNat_le a
  exact uint64_le_iff.mpr (by
    rw [UInt64.toNat_div]
    exact Nat.le_trans (Nat.div_le_self _ _) hmax)

theorem val_mod_le (a b : TopBoundedUInt64 hi) : a.val % b.val ≤ hi := by
  have hmax := toNat_le a
  exact uint64_le_iff.mpr (by
    rw [UInt64.toNat_mod]
    exact Nat.le_trans (Nat.mod_le _ _) hmax)

/-- Machine-word division. -/
def div_fast (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi :=
  ofWordLe hi (a.val / b.val) (val_div_le a b)

@[csimp] theorem div_eq_fast : @div = @div_fast := by
  funext hi a b
  apply ext
  rw [toNat_div, div_fast, toNat_ofWordLe, UInt64.toNat_div]
  rfl

/-- Machine-word remainder. -/
def mod_fast (a b : TopBoundedUInt64 hi) : TopBoundedUInt64 hi :=
  ofWordLe hi (a.val % b.val) (val_mod_le a b)

@[csimp] theorem mod_eq_fast : @mod = @mod_fast := by
  funext hi a b
  apply ext
  rw [toNat_mod, mod_fast, toNat_ofWordLe, UInt64.toNat_mod]
  rfl

/-- Machine-word checked division: the zero test is a machine comparison. -/
def checked_div_fast (a b : TopBoundedUInt64 hi) : Option (TopBoundedUInt64 hi) :=
  if b.val = 0 then none else some (div a b)

@[csimp] theorem checked_div_eq_fast : @checked_div = @checked_div_fast := by
  funext hi a b
  unfold checked_div checked_div_fast
  by_cases hb : b.val = 0
  · rw [ite_eq_left hb, ite_eq_left (val_eq_zero_iff.mp hb)]
  · rw [ite_eq_right hb, ite_eq_right (fun hc => hb (val_eq_zero_iff.mpr hc))]

/-- Machine-word checked remainder. -/
def checked_mod_fast (a b : TopBoundedUInt64 hi) : Option (TopBoundedUInt64 hi) :=
  if b.val = 0 then none else some (mod a b)

@[csimp] theorem checked_mod_eq_fast : @checked_mod = @checked_mod_fast := by
  funext hi a b
  unfold checked_mod checked_mod_fast
  by_cases hb : b.val = 0
  · rw [ite_eq_left hb, ite_eq_left (val_eq_zero_iff.mp hb)]
  · rw [ite_eq_right hb, ite_eq_right (fun hc => hb (val_eq_zero_iff.mpr hc))]

end TopBoundedUInt64
