/-!
Fusing a `map` into the `filter` that consumes it: the intermediate array is not
built. The condition is that the mapped array is used exactly once — as the argument
of the filter — and that both functions are effect-free.
-/

/-- The shape the proposal is about: `(a.map f).filter g`. -/
def test1 (a : Array Nat) : Array Nat := (a.map (· * 2)).filter (· > 4)

/-- The same with functions the caller supplies. -/
def test2 (a : Array Nat) (f : Nat → Nat) (g : Nat → Bool) : Array Nat :=
  (a.map f).filter g

/-- The intermediate array is used twice, so it has to be built. -/
def test3 (a : Array Nat) : Array Nat × Array Nat :=
  let b := a.map (· * 2)
  (b, b.filter (· > 4))

/-- A `map` on its own. -/
def test4 (a : Array Nat) : Array Nat := a.map (· + 1)

/-- A `filter` on its own. -/
def test5 (a : Array Nat) : Array Nat := a.filter (· > 4)
