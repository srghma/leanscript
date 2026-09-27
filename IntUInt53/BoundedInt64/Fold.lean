import IntUInt53.BoundedInt64.Fast
import IntUInt53.BoundedInt64.Add

/-!
# Whole computations on `BoundedInt64`

The signed counterpart of `TopBoundedUInt64.Fold`, with one genuine
difference.

For an unsigned bounded type every partial sum is at most the total, so a chain
of checked additions succeeds exactly when the exact total is representable.
For a signed range that is **false**: a partial sum can leave the range even
though the total does not, so the chain may fail on a computation whose answer
is perfectly representable.  What remains true — and is what one actually needs
— is *soundness*: whenever the chain succeeds, its result is the exact total.

The counterexample is exhibited on `Int53` in `IntUInt53.Int53.Fold`.
-/

set_option autoImplicit false

namespace BoundedInt64

variable {lo hi : Int64}

/-- The exact sum of the integers denoted by a list of values. -/
def sumInt (l : List (BoundedInt64 lo hi)) : Int := (l.map toInt).sum

@[simp] theorem sumInt_nil : sumInt ([] : List (BoundedInt64 lo hi)) = 0 := rfl

@[simp] theorem sumInt_cons (a : BoundedInt64 lo hi) (l : List (BoundedInt64 lo hi)) :
    sumInt (a :: l) = a.toInt + sumInt l := rfl

/-- One step of the chain: add the next value to an `Option` accumulator. -/
def addStep (acc : Option (BoundedInt64 lo hi)) (x : BoundedInt64 lo hi) :
    Option (BoundedInt64 lo hi) :=
  acc.bind (fun a => checked_add a x)

/-- The checked sum of a nonempty list, starting the chain at its head. -/
def checked_sum (a : BoundedInt64 lo hi) (l : List (BoundedInt64 lo hi)) :
    Option (BoundedInt64 lo hi) :=
  l.foldl addStep (some a)

theorem foldl_addStep_none (l : List (BoundedInt64 lo hi)) :
    l.foldl addStep none = none := by
  induction l with
  | nil => rfl
  | cons a l ih => simpa [addStep] using ih

/-- **Soundness of the chain**: whenever a chain of checked additions succeeds,
its result is the exact total. -/
theorem toInt_of_foldl_addStep {a c : BoundedInt64 lo hi} {l : List (BoundedInt64 lo hi)}
    (h : l.foldl addStep (some a) = some c) : c.toInt = a.toInt + sumInt l := by
  induction l generalizing a with
  | nil =>
    rw [List.foldl_nil] at h
    rw [← Option.some.inj h, sumInt_nil, Int.add_zero]
  | cons x l ih =>
    rw [List.foldl_cons] at h
    cases hstep : checked_add a x with
    | none =>
      rw [show addStep (some a) x = none from by simp [addStep, hstep],
        foldl_addStep_none] at h
      exact absurd h (by simp)
    | some d =>
      rw [show addStep (some a) x = some d from by simp [addStep, hstep]] at h
      have hd : d.toInt = a.toInt + x.toInt := toInt_of_checked_add hstep
      rw [ih h, hd, sumInt_cons]
      omega

/-- Soundness, stated for `checked_sum`. -/
theorem toInt_of_checked_sum {a c : BoundedInt64 lo hi} {l : List (BoundedInt64 lo hi)}
    (h : checked_sum a l = some c) : c.toInt = a.toInt + sumInt l :=
  toInt_of_foldl_addStep h

end BoundedInt64
