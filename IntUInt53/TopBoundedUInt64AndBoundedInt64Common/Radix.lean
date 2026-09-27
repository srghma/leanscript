/-!
# Positional notation on `Nat`

The serialisation and parsing of the bounded types are built on one piece of
`Nat`-level machinery, collected here: writing a natural number in a positional
system with a fixed base and a fixed number of limbs, and reading it back.

* `Radix.digits base k n` is the list of the `k` least significant digits of
  `n` in base `base`, least significant first;
* `Radix.ofDigits base l` reads such a list back.

The main theorem is `Radix.ofDigits_digits`: reading back the `k` digits of a
number below `base ^ k` returns that number.  Everything is exact arithmetic on
`Nat`; only the Lean core library is used.
-/

set_option autoImplicit false

namespace Radix

/-- The `k` least significant digits of `n` in base `base`, least significant first. -/
def digits (base : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, n => (n % base) :: digits base k (n / base)

/-- Read a list of digits in base `base`, least significant first. -/
def ofDigits (base : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => d + base * ofDigits base ds

@[simp] theorem digits_zero (base n : Nat) : digits base 0 n = [] := rfl

@[simp] theorem digits_succ (base k n : Nat) :
    digits base (k + 1) n = (n % base) :: digits base k (n / base) := rfl

@[simp] theorem ofDigits_nil (base : Nat) : ofDigits base [] = 0 := rfl

@[simp] theorem ofDigits_cons (base d : Nat) (ds : List Nat) :
    ofDigits base (d :: ds) = d + base * ofDigits base ds := rfl

/-- The digit list has exactly the requested length. -/
@[simp] theorem length_digits (base : Nat) : ∀ (k n : Nat), (digits base k n).length = k
  | 0, _ => rfl
  | k + 1, n => by rw [digits_succ, List.length_cons, length_digits base k (n / base)]

/-- Every digit is smaller than the base. -/
theorem digit_lt (base : Nat) (hbase : 0 < base) :
    ∀ (k n : Nat), ∀ d ∈ digits base k n, d < base
  | 0, _, _, h => absurd h (by simp)
  | k + 1, n, d, h => by
    rw [digits_succ, List.mem_cons] at h
    rcases h with rfl | h
    · exact Nat.mod_lt _ hbase
    · exact digit_lt base hbase k (n / base) d h

/-- **Reading back what was written**: the `k` digits of a number below
`base ^ k` determine it exactly. -/
theorem ofDigits_digits (base : Nat) (hbase : 0 < base) :
    ∀ (k n : Nat), n < base ^ k → ofDigits base (digits base k n) = n
  | 0, n, h => by
    rw [Nat.pow_zero] at h
    rw [digits_zero, ofDigits_nil]
    omega
  | k + 1, n, h => by
    have hdiv : n / base < base ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm] at h
      exact Nat.div_lt_of_lt_mul h
    rw [digits_succ, ofDigits_cons, ofDigits_digits base hbase k (n / base) hdiv]
    exact Nat.mod_add_div n base

/-- A list of `k` digits in base `base` denotes a number below `base ^ k`. -/
theorem ofDigits_lt (base : Nat) (hbase : 0 < base) :
    ∀ (l : List Nat), (∀ d ∈ l, d < base) → ofDigits base l < base ^ l.length
  | [], _ => by simp
  | d :: ds, h => by
    have hd : d < base := h d (List.mem_cons_self ..)
    have hds : ofDigits base ds < base ^ ds.length :=
      ofDigits_lt base hbase ds (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hstep : base * ofDigits base ds + base ≤ base * base ^ ds.length := by
      have : ofDigits base ds + 1 ≤ base ^ ds.length := hds
      calc base * ofDigits base ds + base = base * (ofDigits base ds + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
        _ ≤ base * base ^ ds.length := Nat.mul_le_mul_left _ this
    rw [ofDigits_cons, List.length_cons, Nat.pow_succ, Nat.mul_comm (base ^ ds.length) base]
    omega

/-- Writing a digit list back out returns the same list. -/
theorem digits_ofDigits (base : Nat) (hbase : 0 < base) :
    ∀ (l : List Nat), (∀ d ∈ l, d < base) → digits base l.length (ofDigits base l) = l
  | [], _ => rfl
  | d :: ds, h => by
    have hd : d < base := h d (List.mem_cons_self ..)
    have hrec : digits base ds.length (ofDigits base ds) = ds :=
      digits_ofDigits base hbase ds (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hmod : (d + base * ofDigits base ds) % base = d := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
    have hdiv : (d + base * ofDigits base ds) / base = ofDigits base ds := by
      rw [Nat.add_mul_div_left _ _ hbase, Nat.div_eq_of_lt hd, Nat.zero_add]
    rw [List.length_cons, ofDigits_cons, digits_succ, hmod, hdiv, hrec]

end Radix
