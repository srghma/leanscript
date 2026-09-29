/-!
Versions of local functions (`LeanScript.Term.Ownership`, `Own.lamPlan`). A local function
that is not inlined gets one JavaScript constant per way its calls give up their array
arguments: a call passing an array nothing else refers to calls the version that owns (and
updates in place) that parameter; a call passing an array still used afterwards calls the
version that borrows it (and copies before updating). The result of a call is owned when every
path of the version called answers an array built there, so it can be updated in place too.
-/

/-- One call gives up its array (built here), the other passes the parameter `a`, which the
    caller still holds: two versions of `step`. -/
def test1 (a : Array Nat) (n : Nat) : Array Nat :=
  let step := fun (b : Array Nat) (k : Nat) => (b.push k).push (k + 1)
  step (Array.replicate n 0) n ++ step a n ++ a

/-- Every call gives up its array: only the version owning it is generated. -/
def test2 (n m : Nat) : Array Nat :=
  let step := fun (b : Array Nat) (k : Nat) => (b.push k).set! 0 k
  step (Array.replicate n 0) m ++ step (Array.replicate m 1) n

/-- The answer of a local function builds a new array, so the caller updates it in place. -/
def test3 (n m : Nat) : Array Nat :=
  let mk := fun (k : Nat) => Array.replicate k k
  let a := mk n
  let b := mk m
  (a.push m).append b

/-- A local function with two array parameters, only the first of which is updated: a version
    owning the first one. -/
def test4 (a : Array Nat) (n : Nat) : Array Nat :=
  let f := fun (b c : Array Nat) => (b.push c.size, c.size)
  let x := f (Array.replicate n 0) a
  let y := f a a
  (x.1.append y.1).push (x.2 + y.2) ++ a

/-- A hand-written recursion with an array accumulator: a loop whose accumulator is a function.
    Every closure it builds owns its array argument (an *owning closure*), so each push is done
    in place. -/
private def fill : Nat → Array Nat → Array Nat
  | 0, a => a
  | n + 1, a => fill n (a.push n)

/-- The recursion on an array built here: no copy at all. -/
def test5 (n : Nat) : Array Nat := fill n (Array.replicate n 7)

/-- The recursion on the parameter `a`, which the caller still holds: `a` is copied once, where
    the owning closure is called, and then updated in place (`test6$$mut_0` does not copy). -/
def test6 (a : Array Nat) (n : Nat) : Array Nat := fill n a

/-- The closure the recursion answers is called twice. -/
def test7 (n : Nat) : Array Nat :=
  let g := fill n
  g #[] ++ g #[1]
