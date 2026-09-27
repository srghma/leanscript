/-!
The safe-integer guards a program does not need (`LeanScript.NumRange`).

A Lean `Nat` is a JavaScript number, so a primitive that could leave the exactly
representable range carries a guard and a `BigInt` fallback. Where the operands are
known to be small — the length of an array or of a string, a literal, and what
arithmetic makes of those — the guard can only take one branch, and the other is not
written.

The bitwise operations need the operands to fit in *31* bits, which the length of an
array does not: those keep their guard, as does anything computed from a `Nat` the
program was handed.
-/

/-- The example: half the size of an array. -/
def test1 (a : Array Nat) : Nat := a.size / 2

/-- Arithmetic over two lengths is still small. -/
def test2 (a : Array Nat) (b : Array Nat) : Nat := (a.size + b.size) * 3

/-- Through a binding: an immutable name for a length is as good as the length. -/
def test3 (a : Array Nat) : Nat :=
  let n := a.size
  n >>> 1

/-- The number of characters of a string is at most the number of code units it is
    stored as, which is a length. -/
def test4 (s : String) : Nat := s.length / 3

/-- A `Nat` the program was handed can be any size, so this one keeps its guard and
    its `BigInt` fallback. -/
def test5 (n : Nat) : Nat := n / 2

/-- A bitwise operation needs the operands below `2^31`, which a length is not known
    to be: the guard stays. -/
def test6 (a : Array Nat) : Nat := a.size &&& 7

/-- A length minus an unknown `Nat` is not bounded by anything the domain knows. -/
def test7 (s : String) (i : Nat) : Nat := (s.length - i) / 2
