/-!
A value read out of an array *before* an update of that array which the ownership
analysis performs in place. The read has to stay where it is: moving it past the
update would answer with the new element.
-/

/-- `x` is read before the `set!`, and used after it. -/
def test1 (n : Nat) : Nat := Id.run do
  let mut a : Array Nat := Array.replicate 3 (n + 7)
  let x := a[0]!
  a := a.set! 0 99
  return x + a[1]!

/-- The same with a `swap`. -/
def test2 (n : Nat) : Nat := Id.run do
  let mut a : Array Nat := #[n + 1, n + 2, n + 3]
  let x := a[0]!
  a := a.swapIfInBounds 0 2
  return x * 10 + a[0]!

/-- The same with a push, which does not change an element. -/
def test3 (n : Nat) : Nat := Id.run do
  let mut a : Array Nat := #[n + 1]
  let x := a[0]!
  a := a.push 5
  return x + a.size

/-- The array is not read again after the update, so the update is done *in place*;
    the value read before it is used after it. -/
def test4 (n : Nat) : Array Nat × Nat := Id.run do
  let mut a : Array Nat := Array.replicate 3 (n + 7)
  let x := a[0]!
  a := a.set! 0 99
  return (a, x)

/-- The accumulator of a loop, updated in place: the element read before the update
    must be the *old* one. Lean answers `0`; a translation that moved the read past
    the update would answer `10`. -/
def test5 (n : Nat) : Nat := Id.run do
  let mut a : Array Nat := Array.replicate 4 n
  let mut s := 0
  for i in [0:4] do
    let old := a[i]!
    a := a.set! i (i + 1)
    s := s + old
  return s
