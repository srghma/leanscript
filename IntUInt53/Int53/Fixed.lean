import IntUInt53.Int53.Add
import IntUInt53.Int53.Sub
import IntUInt53.Int53.Mul
import IntUInt53.Int53.Div

/-!
# Exact decimal fixed-point numbers on top of `Int53`

A `Fixed53 scale` is an `Int53` mantissa read as a decimal number with `scale`
digits after the point: the value denoted is `mantissa / 10 ^ scale`.  So
`Fixed53 2` holds amounts in cents, and `(1 : Fixed53 1)` means `0.1`.

Everything here is exact.  Rather than introducing rational numbers, each
specification is stated by clearing denominators — for instance the product
satisfies

```
c.mantissa * 10 ^ scale = a.mantissa * b.mantissa
```

which says precisely that the value of `c` is the product of the values of `a`
and `b`.  Addition and subtraction are the mantissa operations, so they are
exact whenever the mantissa fits; multiplication additionally requires the
product to be divisible by `10 ^ scale`, and `checked_mul` returns `none` when
it is not, rather than rounding.

The point of the layer is the absence of drift: `0.1` added ten times is
exactly `1`, which is `Fixed53.tenths_sum_exact` below and is *false* for
binary floating point.
-/

set_option autoImplicit false

/-- A decimal fixed-point number: an `Int53` mantissa denoting
`mantissa / 10 ^ scale`. -/
structure Fixed53 (scale : Nat) where
  /-- The mantissa; the value denoted is `mantissa / 10 ^ scale`. -/
  mantissa : Int53
deriving DecidableEq, Repr

namespace Fixed53

variable {scale : Nat}

/-- The mantissa as an integer; the value denoted is this divided by `10 ^ scale`. -/
def toMantissaInt (a : Fixed53 scale) : Int := a.mantissa.toInt

theorem ext {a b : Fixed53 scale} (h : a.toMantissaInt = b.toMantissaInt) : a = b := by
  cases a; cases b
  exact congrArg _ (BoundedInt64.ext h)

/-- Build a fixed-point number from a mantissa literal in range. -/
def ofMantissa (scale : Nat) (n : Int) (h₁ : Int53.MIN ≤ n := by decide)
    (h₂ : n ≤ Int53.MAX := by decide) : Fixed53 scale :=
  ⟨Int53.ofInt n h₁ h₂⟩

@[simp] theorem toMantissaInt_ofMantissa (n : Int) (h₁ : Int53.MIN ≤ n) (h₂ : n ≤ Int53.MAX) :
    (ofMantissa scale n h₁ h₂).toMantissaInt = n := by
  unfold ofMantissa toMantissaInt
  rw [Int53.toInt_ofInt]

/-! ### Addition and subtraction -/

/-- Checked addition: `none` exactly when the mantissa sum leaves the range. -/
def checked_add (a b : Fixed53 scale) : Option (Fixed53 scale) :=
  (BoundedInt64.checked_add a.mantissa b.mantissa).map Fixed53.mk

/-- Checked subtraction. -/
def checked_sub (a b : Fixed53 scale) : Option (Fixed53 scale) :=
  (BoundedInt64.checked_sub a.mantissa b.mantissa).map Fixed53.mk

/-- **Addition is exact**: the value of the sum is the sum of the values. -/
theorem toMantissaInt_of_checked_add {a b c : Fixed53 scale} (h : checked_add a b = some c) :
    c.toMantissaInt = a.toMantissaInt + b.toMantissaInt := by
  unfold checked_add at h
  cases hs : BoundedInt64.checked_add a.mantissa b.mantissa with
  | none => rw [hs] at h; exact absurd h (by simp)
  | some d =>
    rw [hs] at h
    have hc : c = ⟨d⟩ := by simpa using h.symm
    rw [hc]
    exact BoundedInt64.toInt_of_checked_add hs

/-- **Subtraction is exact**. -/
theorem toMantissaInt_of_checked_sub {a b c : Fixed53 scale} (h : checked_sub a b = some c) :
    c.toMantissaInt = a.toMantissaInt - b.toMantissaInt := by
  unfold checked_sub at h
  cases hs : BoundedInt64.checked_sub a.mantissa b.mantissa with
  | none => rw [hs] at h; exact absurd h (by simp)
  | some d =>
    rw [hs] at h
    have hc : c = ⟨d⟩ := by simpa using h.symm
    rw [hc]
    exact BoundedInt64.toInt_of_checked_sub hs

/-! ### Multiplication -/

/-- The exact product of the mantissas, before rescaling. -/
def exactProduct (a b : Fixed53 scale) : Int := a.toMantissaInt * b.toMantissaInt

/-- Checked multiplication: `none` unless the exact product of the values is
itself representable at this scale — that is, unless `10 ^ scale` divides the
product of the mantissas and the quotient is in range.  Nothing is ever
rounded. -/
def checked_mul (a b : Fixed53 scale) : Option (Fixed53 scale) :=
  if exactProduct a b % (10 ^ scale : Int) = 0 then
    (Int53.ofInt? (exactProduct a b / (10 ^ scale : Int))).map Fixed53.mk
  else
    none

/-- **Multiplication is exact**: when it succeeds, the value of the result is
exactly the product of the values (the statement with denominators cleared). -/
theorem checked_mul_exact {a b c : Fixed53 scale} (h : checked_mul a b = some c) :
    c.toMantissaInt * (10 ^ scale : Int) = a.toMantissaInt * b.toMantissaInt := by
  unfold checked_mul at h
  split at h
  · next hdvd =>
    cases hs : Int53.ofInt? (exactProduct a b / (10 ^ scale : Int)) with
    | none => rw [hs] at h; exact absurd h (by simp)
    | some d =>
      rw [hs] at h
      have hc : c = ⟨d⟩ := by simpa using h.symm
      have hd : d.toInt = exactProduct a b / (10 ^ scale : Int) :=
        Int53.ofInt?_eq_some_iff.mp hs
      have hmul : exactProduct a b / (10 ^ scale : Int) * (10 ^ scale : Int)
          = exactProduct a b := Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero hdvd)
      rw [hc]
      show d.toInt * (10 ^ scale : Int) = a.toMantissaInt * b.toMantissaInt
      rw [hd, hmul]
      rfl
  · exact absurd h (by simp)

/-- Multiplication reports, rather than rounds, a product that the scale cannot
represent. -/
theorem checked_mul_eq_none_of_not_dvd {a b : Fixed53 scale}
    (h : exactProduct a b % (10 ^ scale : Int) ≠ 0) : checked_mul a b = none := by
  unfold checked_mul
  rw [ite_eq_right h]

/-! ### No drift -/

set_option maxRecDepth 4000 in
/-- Ten tenths are exactly one: starting from `0.0` and adding `0.1` ten times
gives `1.0` on the nose.  In binary floating point the analogous computation
does not give `1`. -/
theorem tenths_sum_exact :
    (List.replicate 10 (ofMantissa 1 1)).foldl
        (fun acc x => acc.bind (fun a => checked_add a x))
        (some (ofMantissa 1 0))
      = some (ofMantissa 1 10) := by
  decide

/-- `0.1 * 0.1 = 0.01` is not representable at one decimal place, and this is
reported rather than rounded. -/
theorem tenth_mul_tenth_not_representable :
    checked_mul (ofMantissa 1 1) (ofMantissa 1 1) = none := by decide

/-- At two decimal places `0.10 * 0.10 = 0.01` is exact. -/
theorem tenth_mul_tenth_at_scale_two :
    checked_mul (ofMantissa 2 10) (ofMantissa 2 10) = some (ofMantissa 2 1) := by decide

/-- `1.25 + 2.50 = 3.75`, exactly, at two decimal places. -/
theorem sum_of_prices :
    checked_add (ofMantissa 2 125) (ofMantissa 2 250) = some (ofMantissa 2 375) := by
  decide

end Fixed53
