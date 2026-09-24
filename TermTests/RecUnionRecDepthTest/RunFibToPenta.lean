module

public import TermTests.RecUnionRecDepthTest

@[expose] public section

set_option autoImplicit false

/-!
# The `fib` suite over a recursive tagged union: running the terms, part 1

The terms of `TermTests/RecUnionRecDepthTest.lean`, checked by the kernel against their
Lean references at the first ten arguments.  This file: `fib` and the tribonacci,
tetranacci and pentanacci numbers.  The checks are split over two
files so that they build in parallel.
-/

namespace TermTests.RecUnionRecDepth

open LeanScript

example : ∀ n, n < 10 →
    runP fibTerm (peanoVal n) = Peano.fib (Peano.ofNat n) := by
  decide +kernel

example : ∀ n, n < 10 →
    runP tribTerm (peanoVal n) = Peano.trib (Peano.ofNat n) := by
  decide +kernel

example : ∀ n, n < 10 →
    runP tetraTerm (peanoVal n) = Peano.tetra (Peano.ofNat n) := by
  decide +kernel

example : ∀ n, n < 10 →
    runP pentaTerm (peanoVal n) = Peano.penta (Peano.ofNat n) := by
  decide +kernel

end TermTests.RecUnionRecDepth
