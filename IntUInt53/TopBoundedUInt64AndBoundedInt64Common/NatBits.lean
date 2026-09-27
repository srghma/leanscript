/-!
# Bit counting on `Nat`

The bit-counting operations used by the bounded types, defined and specified
once on `Nat`:

* `NatBits.popCount n` — the number of one bits of `n`;
* `NatBits.ctz n` — the number of trailing zero bits of a nonzero `n`.

The specifications are the usual ones: `popCount n ≤ k` for `n < 2 ^ k`, and
for the count of trailing zeros, the bit at that position is set while every
lower bit is clear.  Only the Lean core library is used.
-/

set_option autoImplicit false

namespace NatBits

/-- The number of one bits of `n`. -/
def popCount (n : Nat) : Nat :=
  if h : n = 0 then 0 else n % 2 + popCount (n / 2)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

@[simp] theorem popCount_zero : popCount 0 = 0 := by rw [popCount]; simp

theorem popCount_of_ne_zero {n : Nat} (h : n ≠ 0) :
    popCount n = n % 2 + popCount (n / 2) := by
  rw [popCount]; simp [h]

/-- A number below `2 ^ k` has at most `k` one bits. -/
theorem popCount_le : ∀ (k n : Nat), n < 2 ^ k → popCount n ≤ k
  | 0, n, h => by
    rw [Nat.pow_zero] at h
    have hz : n = 0 := by omega
    rw [hz, popCount_zero]
    exact Nat.le_refl 0
  | k + 1, n, h => by
    by_cases hn : n = 0
    · rw [hn, popCount_zero]; omega
    · have hdiv : n / 2 < 2 ^ k := by
        have : n < 2 ^ k * 2 := by rw [Nat.pow_succ] at h; omega
        exact Nat.div_lt_of_lt_mul (by omega)
      have := popCount_le k (n / 2) hdiv
      have hmod : n % 2 ≤ 1 := by omega
      rw [popCount_of_ne_zero hn]
      omega

/-- Only zero has no one bits. -/
theorem eq_zero_of_popCount_eq_zero : ∀ (n : Nat), popCount n = 0 → n = 0
  | n, h => by
    by_cases hn : n = 0
    · exact hn
    · exfalso
      rw [popCount_of_ne_zero hn] at h
      have hdiv : popCount (n / 2) = 0 := by omega
      have hd0 : n / 2 = 0 := eq_zero_of_popCount_eq_zero (n / 2) hdiv
      have : n < 2 := Nat.lt_of_div_eq_zero (by decide) hd0
      omega
  termination_by n => n

theorem popCount_eq_zero_iff {n : Nat} : popCount n = 0 ↔ n = 0 :=
  ⟨eq_zero_of_popCount_eq_zero n, fun h => by rw [h, popCount_zero]⟩

/-- The number of trailing zero bits (`0` at `0`). -/
def ctz (n : Nat) : Nat :=
  if h : n = 0 then 0 else if n % 2 = 1 then 0 else ctz (n / 2) + 1
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

@[simp] theorem ctz_zero : ctz 0 = 0 := by rw [ctz]; simp

theorem ctz_of_odd {n : Nat} (h : n % 2 = 1) : ctz n = 0 := by
  rw [ctz]
  have hn : n ≠ 0 := by omega
  simp [hn, h]

theorem ctz_of_even {n : Nat} (h₀ : n ≠ 0) (h : n % 2 = 0) : ctz n = ctz (n / 2) + 1 := by
  rw [ctz]
  simp [h₀, h]

/-- The bit at position `ctz n` is set, for a nonzero `n`. -/
theorem testBit_ctz : ∀ (n : Nat), n ≠ 0 → n.testBit (ctz n) = true
  | n, hn => by
    by_cases h : n % 2 = 1
    · rw [ctz_of_odd h, Nat.testBit_zero]
      simp [h]
    · have h0 : n % 2 = 0 := by omega
      have hd0 : n / 2 ≠ 0 := by
        intro hz
        have : n < 2 := Nat.lt_of_div_eq_zero (by decide) hz
        omega
      have hlt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
      have ih := testBit_ctz (n / 2) hd0
      rw [ctz_of_even hn h0, Nat.testBit_succ]
      exact ih
  termination_by n => n

/-- Every bit below position `ctz n` is clear. -/
theorem testBit_lt_ctz : ∀ (n i : Nat), i < ctz n → n.testBit i = false
  | n, i, hi => by
    by_cases hn : n = 0
    · rw [hn]; simp
    by_cases h : n % 2 = 1
    · rw [ctz_of_odd h] at hi; omega
    · have h0 : n % 2 = 0 := by omega
      have hlt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
      cases i with
      | zero => rw [Nat.testBit_zero]; simp [h0]
      | succ j =>
        rw [ctz_of_even hn h0] at hi
        rw [Nat.testBit_succ]
        exact testBit_lt_ctz (n / 2) j (by omega)
  termination_by n => n

/-! ### Bounded-fuel versions, for computation

The definitions above recurse on the value, which the kernel cannot unfold on a
large literal.  The bounded-fuel versions below agree with them on every number
below `2 ^ k`, and do reduce, so concrete claims can be discharged by `decide`.
-/

/-- The number of one bits, computed in at most `k` steps. -/
def popCountFuel : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => if n = 0 then 0 else n % 2 + popCountFuel k (n / 2)

/-- The number of trailing zeros, computed in at most `k` steps. -/
def ctzFuel : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => if n = 0 then 0 else if n % 2 = 1 then 0 else ctzFuel k (n / 2) + 1

theorem popCountFuel_eq : ∀ (k n : Nat), n < 2 ^ k → popCountFuel k n = popCount n
  | 0, n, h => by
    rw [Nat.pow_zero] at h
    have hz : n = 0 := by omega
    rw [hz, popCount_zero]
    rfl
  | k + 1, n, h => by
    show (if n = 0 then 0 else n % 2 + popCountFuel k (n / 2)) = popCount n
    by_cases hn : n = 0
    · rw [ite_eq_left hn, hn, popCount_zero]
    · have hdiv : n / 2 < 2 ^ k := by
        have : n < 2 ^ k * 2 := by rw [Nat.pow_succ] at h; omega
        exact Nat.div_lt_of_lt_mul (by omega)
      rw [ite_eq_right hn, popCountFuel_eq k (n / 2) hdiv, popCount_of_ne_zero hn]

theorem ctzFuel_eq : ∀ (k n : Nat), n < 2 ^ k → ctzFuel k n = ctz n
  | 0, n, h => by
    rw [Nat.pow_zero] at h
    have hz : n = 0 := by omega
    rw [hz, ctz_zero]
    rfl
  | k + 1, n, h => by
    show (if n = 0 then 0 else if n % 2 = 1 then 0 else ctzFuel k (n / 2) + 1) = ctz n
    by_cases hn : n = 0
    · rw [ite_eq_left hn, hn, ctz_zero]
    · rw [ite_eq_right hn]
      by_cases hodd : n % 2 = 1
      · rw [ite_eq_left hodd, ctz_of_odd hodd]
      · have hdiv : n / 2 < 2 ^ k := by
          have : n < 2 ^ k * 2 := by rw [Nat.pow_succ] at h; omega
          exact Nat.div_lt_of_lt_mul (by omega)
        rw [ite_eq_right hodd, ctzFuel_eq k (n / 2) hdiv, ctz_of_even hn (by omega)]

end NatBits
