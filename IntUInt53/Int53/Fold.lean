import IntUInt53.Int53.Add
import IntUInt53.BoundedInt64.Fold

/-!
# Whole computations on `Int53`

Soundness of a chain of checked additions, specialised to `Int53`, together
with the concrete counterexample announced in `IntUInt53.BoundedInt64.Fold`:
on a signed range the chain is **order dependent**, so it can fail on a
computation whose exact total is representable.

`MAX + MAX + MIN = MAX` is in range, yet adding left to right overflows at the
first step; the same three summands added in the order `MAX + MIN + MAX`
succeed.  Both facts are decided below.
-/

set_option autoImplicit false

open BoundedInt64

namespace Int53

/-- Whenever a chain of checked additions on `Int53` succeeds, its result is
the exact total. -/
theorem toInt_of_checked_sum {a c : Int53} {l : List Int53}
    (h : checked_sum a l = some c) : c.toInt = a.toInt + sumInt l :=
  BoundedInt64.toInt_of_checked_sum h

/-- The exact total of `[MAX, MIN]` starting from `MAX` is `MAX`, which is
representable. -/
theorem sumInt_example : maxVal.toInt + sumInt [maxVal, minVal] = MAX := by decide

/-- Yet the left-to-right chain `MAX + MAX + MIN` fails: the first partial sum
is out of range. -/
theorem checked_sum_fails : checked_sum maxVal [maxVal, minVal] = none := by decide

/-- Reordering the same summands as `MAX + MIN + MAX` makes the chain succeed,
with the exact total. -/
theorem checked_sum_succeeds_reordered :
    checked_sum maxVal [minVal, maxVal] = some maxVal := by decide

end Int53
