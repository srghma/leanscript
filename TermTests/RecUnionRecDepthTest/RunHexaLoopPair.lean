module

public import TermTests.RecUnionRecDepthTest

@[expose] public section

set_option autoImplicit false

/-!
# The `fib` suite over a recursive tagged union: running the terms, part 2

The terms of `TermTests/RecUnionRecDepthTest.lean`, checked by the kernel against their
Lean references at the first ten arguments.  This file: the hexanacci numbers, the
tail-recursive loop and the pair recursion.  The checks are split over two
files so that they build in parallel.
-/

namespace TermTests.RecUnionRecDepth

open LeanScript

example : ∀ n, n < 10 →
    runP hexaTerm (peanoVal n) = Peano.hexa (Peano.ofNat n) := by
  decide +kernel

example : ∀ n, n < 10 →
    runP fibTRTerm (peanoVal n) = Peano.fibTR (Peano.ofNat n) := by
  decide +kernel

example : ∀ n, n < 10 →
    runP fibPairTerm (peanoVal n) = (Peano.fibPair (Peano.ofNat n)).1 := by
  decide +kernel

end TermTests.RecUnionRecDepth
