module

public import TermTests.ToTermTest.ForRangeStep
public meta import LeanScript.KernelRfl
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `for h : i in r` over a range: the loop that names the membership proof

A `for h : i in r` in the identity monad hands its body a proof `h : i ∈ r`, most often
to index a list or array without a check (`l[i]`, whose bound `i < l.length` Lean gets
from `h`).  The language erases proofs, so:

* when the body does not read `h`, the loop is `for i in r` (proved:
  `LeanScript.ListLibrary.forIn'_range_eq_forIn`);
* otherwise it is the loop over `[:r.size]` whose body, at `j`, is guarded by
  `if hj : j < r.size`, and reads the index `r.start + j * r.step` with the proof
  `Std.Legacy.Range.mem_start_add_mul_step r hj` (proved:
  `LeanScript.ListLibrary.forIn'_range_eq_forIn_guard`).  The test always holds; it is there
  because a proof is needed, and it costs one comparison per iteration.

Both are then translated as any loop over a range, `break` and `return` included.

Lean's own `for` over a range is defined by well-founded recursion, which the kernel does
not evaluate.  So each program's value is checked twice: the translated program by
`kernel_rfl` against the value written out, and the Lean function by `#guard` (the
compiler) against the same value. -/

namespace TermTests.ToTerm.ForRangeMem

open LeanScript TermTests.NatRecDepth TermTests.StructRec.Split TermTests.ToTerm.ListLibrary
  TermTests.ToTerm.ForBreak

/-! ## The proof unused -/

/-- The proof is named but not read: the loop over `[:n]` itself. -/
def sumMemUnused (n : Nat) : Nat := Id.run do
  let mut s := 0
  for _h : i in [:n] do
    s := s + i
  return s

def sumMemUnused_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term sumMemUnused

example : runAdd sumMemUnused_term 0 = 0 := by kernel_rfl
example : runAdd sumMemUnused_term 5 = 10 := by kernel_rfl
#guard [0, 5].map sumMemUnused == [0, 10]

/-- The same over a range with a start and a step. -/
def sumMemUnusedStep (k n : Nat) : Nat := Id.run do
  let mut s := 0
  for _h : i in [k:n:2] do
    s := s + i
  return s

def sumMemUnusedStep_term : Term sigAdd [] (natT ⇒ natT ⇒ natT) :=
  #leanscript_to_term sumMemUnusedStep

example : runAdd sumMemUnusedStep_term 3 10 = 24 := by kernel_rfl
example : runAdd sumMemUnusedStep_term 10 3 = 0 := by kernel_rfl
#guard [sumMemUnusedStep 3 10, sumMemUnusedStep 10 3] == [24, 0]

/-! ## Indexing a list with the proof -/

/-- The sum of a list, by index: `l[i]` takes its bound from `h : i ∈ [:l.length]`. -/
def sumByIndex (l : List Nat) : Nat := Id.run do
  let mut s := 0
  for h : i in [:l.length] do
    s := s + l[i]
  return s

def sumByIndex_term : Term sigAdd [] (natListT ⇒ natT) := #leanscript_to_term sumByIndex

example : runAdd sumByIndex_term (natList []) = 0 := by kernel_rfl
example : runAdd sumByIndex_term (natList [3, 1, 4, 1, 5]) = 14 := by kernel_rfl
#guard [sumByIndex [], sumByIndex [3, 1, 4, 1, 5]] == [0, 14]

/-- The elements at the even positions, by index: a step, `[0:l.length:2]`. -/
def evenPositions (l : List Nat) : List Nat := Id.run do
  let mut acc := []
  for h : i in [0:l.length:2] do
    acc := acc ++ [l[i]]
  return acc

def evenPositions_term : Term sigAdd [] (natListT ⇒ natListT) :=
  #leanscript_to_term evenPositions

example : readNatList (runAdd evenPositions_term (natList [])) = [] := by kernel_rfl
example : readNatList (runAdd evenPositions_term (natList [7, 8, 9, 10, 11])) = [7, 9, 11] := by
  kernel_rfl
#guard [evenPositions [], evenPositions [7, 8, 9, 10, 11]] == [[], [7, 9, 11]]

/-- A start: the sum of the elements from position `k` on. -/
def sumFromIndex (k : Nat) (l : List Nat) : Nat := Id.run do
  let mut s := 0
  for h : i in [k:l.length] do
    s := s + l[i]
  return s

def sumFromIndex_term : Term sigAdd [] (natT ⇒ natListT ⇒ natT) :=
  #leanscript_to_term sumFromIndex

example : runAdd sumFromIndex_term 2 (natList [3, 1, 4, 1, 5]) = 10 := by kernel_rfl
example : runAdd sumFromIndex_term 7 (natList [3, 1, 4]) = 0 := by kernel_rfl
#guard [sumFromIndex 2 [3, 1, 4, 1, 5], sumFromIndex 7 [3, 1, 4]] == [10, 0]

/-- The adjacent differences that go up, by index from `1`: reads `l[i]` and
    `l[i - 1]`, both bounded by `h`. -/
def risesByIndex (l : List Nat) : Nat := Id.run do
  let mut c := 0
  for h : i in [1:l.length] do
    have : i - 1 < l.length := by have h' : i < l.length := h.upper; omega
    if l[i - 1] < l[i] then c := c + 1
  return c

def risesByIndex_term : Term sigAdd [] (natListT ⇒ natT) := #leanscript_to_term risesByIndex

example : runAdd risesByIndex_term (natList [1, 3, 2, 5, 6]) = 3 := by kernel_rfl
example : runAdd risesByIndex_term (natList [4]) = 0 := by kernel_rfl
#guard [risesByIndex [1, 3, 2, 5, 6], risesByIndex [4]] == [3, 0]

/-- A function that asks for the proof itself. -/
@[inline] def idxOfMem (r : Std.Legacy.Range) (i : Nat) (_h : i ∈ r) : Nat := i

/-- The proof passed on to a function. -/
def sumIdxOfMem (n : Nat) : Nat := Id.run do
  let mut s := 0
  for h : i in [2:n:3] do
    s := s + idxOfMem [2:n:3] i h
  return s

def sumIdxOfMem_term : Term sigAdd [] (natT ⇒ natT) := #leanscript_to_term sumIdxOfMem

example : runAdd sumIdxOfMem_term 12 = 26 := by kernel_rfl
example : runAdd sumIdxOfMem_term 2 = 0 := by kernel_rfl
#guard [sumIdxOfMem 12, sumIdxOfMem 2] == [26, 0]

/-! ## With `break`, `continue` and `return` -/

/-- `break`: the sum of the elements up to the first `0`, by index. -/
def sumUntilZeroByIndex (l : List Nat) : Nat := Id.run do
  let mut s := 0
  for h : i in [:l.length] do
    if l[i] == 0 then break
    s := s + l[i]
  return s

def sumUntilZeroByIndex_term : Term sigAdd [] (natListT ⇒ natT) :=
  #leanscript_to_term sumUntilZeroByIndex

example : runAdd sumUntilZeroByIndex_term (natList [2, 3, 0, 5]) = 5 := by kernel_rfl
example : runAdd sumUntilZeroByIndex_term (natList [2, 3]) = 5 := by kernel_rfl
#guard [sumUntilZeroByIndex [2, 3, 0, 5], sumUntilZeroByIndex [2, 3]] == [5, 5]

/-- `continue`: the sum of the elements other than `7`, at the odd positions. -/
def sumOddPositionsSkip7 (l : List Nat) : Nat := Id.run do
  let mut s := 0
  for h : i in [1:l.length:2] do
    if l[i] == 7 then continue
    s := s + l[i]
  return s

def sumOddPositionsSkip7_term : Term sigAdd [] (natListT ⇒ natT) :=
  #leanscript_to_term sumOddPositionsSkip7

example : runAdd sumOddPositionsSkip7_term (natList [0, 1, 0, 7, 0, 5]) = 6 := by kernel_rfl
#guard sumOddPositionsSkip7 [0, 1, 0, 7, 0, 5] == 6

/-- An early `return` without a `let mut`: the position of the first element above `k`,
    or the length. -/
def findAboveByIndex (k : Nat) (l : List Nat) : Nat := Id.run do
  for h : i in [:l.length] do
    if l[i] > k then return i
  return l.length

def findAboveByIndex_term : Term sigAdd [] (natT ⇒ natListT ⇒ natT) :=
  #leanscript_to_term findAboveByIndex

example : runAdd findAboveByIndex_term 3 (natList [1, 2, 5, 9]) = 2 := by kernel_rfl
example : runAdd findAboveByIndex_term 10 (natList [1, 2, 5]) = 3 := by kernel_rfl
#guard [findAboveByIndex 3 [1, 2, 5, 9], findAboveByIndex 10 [1, 2, 5]] == [2, 3]

/-! ## Nested loops -/

/-- The number of pairs `i < j` with `l[i] < l[j]`, both loops naming their proof; the
    inner range starts at the outer index. -/
def ascendingPairs (l : List Nat) : Nat := Id.run do
  let mut c := 0
  for hi : i in [:l.length] do
    for hj : j in [i + 1:l.length] do
      if l[i] < l[j] then c := c + 1
  return c

def ascendingPairs_term : Term sigAdd [] (natListT ⇒ natT) :=
  #leanscript_to_term ascendingPairs

example : runAdd ascendingPairs_term (natList [3, 1, 2, 4]) = 4 := by kernel_rfl
example : runAdd ascendingPairs_term (natList []) = 0 := by kernel_rfl
#guard [ascendingPairs [3, 1, 2, 4], ascendingPairs []] == [4, 0]

end TermTests.ToTerm.ForRangeMem
