/-!
Smaller JavaScript for small functions:

* a field read once is read in place (`p._1`), not taken apart into a `const`;
* `if c then a else b` returning two values is `return c ? a : b;`, and an accumulator
  updated only in one branch is `if (c) { acc = e; }`;
* a function equal to one before it is written as that one (`export const g = f;`), and a
  function that only passes its parameters on to a function of the runtime is that function.

(A closure equal to an exported function is that function, not a copy of it:
`Tests/SnapshotsMy/AppArity.lean`, `Tests/SnapshotsMy/TcoHyper.lean`.)
-/

/-- The fields of a pair, each read once. -/
def swapSum (p : Nat × Nat) (q : Nat × Nat) : Nat × Nat := (p.2 + q.2, p.1 + q.1)

/-- The same function again: written as `swapSum`. -/
def swapSum' (p : Nat × Nat) (q : Nat × Nat) : Nat × Nat := (p.2 + q.2, p.1 + q.1)

/-- A choice between two computed values. -/
def absDiff (a b : Nat) : Nat := if a < b then b - a else a - b

/-- Only passes its parameters on to the runtime's addition. -/
def plus (a b : Nat) : Nat := a + b

/-- The largest of `3 * i % 10` for `i < n`, in a loop that updates its accumulator in one
    branch only. -/
def maxMod (n : Nat) : Nat := Id.run do
  let mut m := 0
  for i in [0:n] do
    let x := (3 * i) % 10
    if m < x then m := x
  return m
