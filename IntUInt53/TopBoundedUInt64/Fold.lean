import IntUInt53.TopBoundedUInt64.Fast
import IntUInt53.TopBoundedUInt64.Add
import IntUInt53.TopBoundedUInt64.Mul

/-!
# Whole computations: checked sums and dot products

The theorems of the previous modules are about one operation at a time.  This
module is about *whole computations*: a chain of checked additions, and the
checked dot product of two lists.

The main results are

* `checked_sum_eq`: folding `checked_add` over a list gives exactly the checked
  constructor applied to the exact `Nat` sum — so a chain of additions never
  loses anything and never fails spuriously on an intermediate value;
* `checked_sum_isSome_iff`: the chain succeeds **exactly** when the exact total
  is representable, which is the overflow-freedom criterion one wants to check
  before running a computation;
* `checked_sum_of_le`: the usable sufficient condition — `n` summands each at
  most `k` with `n * k ≤ hi` cannot overflow;
* `checked_dot_eq_some_iff` for the dot product.
-/

set_option autoImplicit false

namespace TopBoundedUInt64

variable {hi : UInt64}

/-! ### The exact sum of a list -/

/-- The exact sum of the numbers denoted by a list of values. -/
def sumNat (l : List (TopBoundedUInt64 hi)) : Nat := (l.map toNat).sum

@[simp] theorem sumNat_nil : sumNat ([] : List (TopBoundedUInt64 hi)) = 0 := rfl

@[simp] theorem sumNat_cons (a : TopBoundedUInt64 hi) (l : List (TopBoundedUInt64 hi)) :
    sumNat (a :: l) = a.toNat + sumNat l := rfl

theorem le_sumNat_of_mem {a : TopBoundedUInt64 hi} :
    ∀ {l : List (TopBoundedUInt64 hi)}, a ∈ l → a.toNat ≤ sumNat l
  | b :: l, h => by
    rcases List.mem_cons.mp h with rfl | hmem
    · rw [sumNat_cons]; omega
    · have := le_sumNat_of_mem hmem
      rw [sumNat_cons]; omega

/-- A list of `n` values each at most `k` has sum at most `n * k`. -/
theorem sumNat_le_of_forall_le {k : Nat} :
    ∀ {l : List (TopBoundedUInt64 hi)}, (∀ a ∈ l, a.toNat ≤ k) → sumNat l ≤ l.length * k
  | [], _ => by simp
  | a :: l, h => by
    have hhead : a.toNat ≤ k := h a (List.mem_cons_self ..)
    have htail : sumNat l ≤ l.length * k :=
      sumNat_le_of_forall_le (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have : (a :: l).length * k = k + l.length * k := by
      simp [List.length_cons, Nat.succ_mul, Nat.add_comm]
    rw [sumNat_cons, this]
    omega

/-! ### Chained checked addition -/

/-- The checked constructor applied to a value returns that value. -/
theorem ofNat?_toNat (a : TopBoundedUInt64 hi) : ofNat? hi a.toNat = some a :=
  ofNat?_eq_some_iff.mpr rfl

/-- One step of the chain: add the next value to an `Option` accumulator. -/
def addStep (acc : Option (TopBoundedUInt64 hi)) (x : TopBoundedUInt64 hi) :
    Option (TopBoundedUInt64 hi) :=
  acc.bind (fun a => checked_add a x)

/-- The checked sum of a list: the chain of checked additions, starting at `0`. -/
def checked_sum (l : List (TopBoundedUInt64 hi)) : Option (TopBoundedUInt64 hi) :=
  l.foldl addStep (some (minVal hi))

theorem foldl_addStep_none (l : List (TopBoundedUInt64 hi)) :
    l.foldl addStep none = none := by
  induction l with
  | nil => rfl
  | cons a l ih => simpa [addStep] using ih

/-- Chaining checked additions is the same as checking the exact total once. -/
theorem foldl_addStep_some (a : TopBoundedUInt64 hi) (l : List (TopBoundedUInt64 hi)) :
    l.foldl addStep (some a) = ofNat? hi (a.toNat + sumNat l) := by
  induction l generalizing a with
  | nil => simpa using (ofNat?_toNat a).symm
  | cons x l ih =>
    rw [List.foldl_cons]
    cases hstep : checked_add a x with
    | none =>
      have hover : hi.toNat < a.toNat + x.toNat :=
        addOverflows_iff.mp (checked_add_eq_none_iff.mp hstep)
      have hnone : ofNat? hi (a.toNat + sumNat (x :: l)) = none := by
        rw [ofNat?_eq_none_iff]
        unfold InRange
        rw [sumNat_cons]
        omega
      rw [hnone, show addStep (some a) x = none from by simp [addStep, hstep]]
      exact foldl_addStep_none l
    | some c =>
      have hc : c.toNat = a.toNat + x.toNat := toNat_of_checked_add hstep
      rw [show addStep (some a) x = some c from by simp [addStep, hstep], ih c, hc,
        sumNat_cons]
      congr 1
      omega

/-- **The chain of checked additions is exact**: it succeeds precisely with the
exact total, whenever the exact total is representable. -/
theorem checked_sum_eq (l : List (TopBoundedUInt64 hi)) :
    checked_sum l = ofNat? hi (sumNat l) := by
  unfold checked_sum
  rw [foldl_addStep_some, toNat_minVal, Nat.zero_add]

theorem checked_sum_eq_some_iff {l : List (TopBoundedUInt64 hi)} {c : TopBoundedUInt64 hi} :
    checked_sum l = some c ↔ c.toNat = sumNat l := by
  rw [checked_sum_eq]; exact ofNat?_eq_some_iff

/-- **Overflow freedom**: the whole computation succeeds exactly when the exact
total is in range — no intermediate step can fail on its own. -/
theorem checked_sum_isSome_iff {l : List (TopBoundedUInt64 hi)} :
    (checked_sum l).isSome ↔ sumNat l ≤ hi.toNat := by
  rw [checked_sum_eq]
  unfold ofNat?
  split <;> simp_all

/-- The usable sufficient criterion: `n` summands, each at most `k`, with
`n * k ≤ hi`, cannot overflow. -/
theorem checked_sum_of_le {k : Nat} {l : List (TopBoundedUInt64 hi)}
    (hbound : ∀ a ∈ l, a.toNat ≤ k) (hfit : l.length * k ≤ hi.toNat) :
    ∃ c, checked_sum l = some c ∧ c.toNat = sumNat l := by
  have hle : sumNat l ≤ hi.toNat :=
    Nat.le_trans (sumNat_le_of_forall_le hbound) hfit
  refine ⟨ofNatLe hi (sumNat l) hle, ?_, by rw [toNat_ofNatLe]⟩
  rw [checked_sum_eq]
  exact ofNat?_of_inRange hle

/-! ### The checked dot product -/

/-- The exact dot product of two lists of values, computed in `Nat`. -/
def dotNat : List (TopBoundedUInt64 hi) → List (TopBoundedUInt64 hi) → Nat
  | [], _ => 0
  | _, [] => 0
  | a :: as, b :: bs => a.toNat * b.toNat + dotNat as bs

/-- The checked dot product: `none` exactly when the exact dot product is out
of range.  The products and their sum are formed in `Nat`, so no intermediate
value is ever truncated. -/
def checked_dot (xs ys : List (TopBoundedUInt64 hi)) : Option (TopBoundedUInt64 hi) :=
  ofNat? hi (dotNat xs ys)

theorem checked_dot_eq_some_iff {xs ys : List (TopBoundedUInt64 hi)}
    {c : TopBoundedUInt64 hi} : checked_dot xs ys = some c ↔ c.toNat = dotNat xs ys :=
  ofNat?_eq_some_iff

theorem checked_dot_eq_none_iff {xs ys : List (TopBoundedUInt64 hi)} :
    checked_dot xs ys = none ↔ hi.toNat < dotNat xs ys := by
  unfold checked_dot
  rw [ofNat?_eq_none_iff]
  unfold InRange
  omega

/-- The dot product of two singleton lists is the product of the entries. -/
@[simp] theorem dotNat_singleton (a b : TopBoundedUInt64 hi) :
    dotNat [a] [b] = a.toNat * b.toNat := by
  unfold dotNat dotNat
  omega

end TopBoundedUInt64
