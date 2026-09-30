/-!
Accesses to arrays under a test of their size, written `a[i]` instead of a call of the runtime
that reads a default out of bounds, and sizes compared as numbers at the `BigInt` preset
(`JsTerm/Lower/Bounds.lean`).

`pat`: a match on array literals (`a.size = k`, then `a[j]` for `j < k`).  `getIf`/`getD`: a
variable index under `i < a.size`.  `getElse`: a variable index in the `else` of
`a.size ≤ i`.  `firstOr`: `a[0]` in the `else` of `a.size = 0`.  `litLt`: literal indices
under `2 < a.size`.  `sizeLt`/`sizeLe`: comparisons of sizes, done on `number`s at the
`faithful` preset.  `sumFuel`/`growRead`: indices and arrays that are the mutable variables of
a loop.  `notKnown`: `a.getD 1 3` under `a.size = 1` is out of bounds (its own test stays).
-/

def pat (a : Array Nat) : Nat :=
  match a with
  | #[] => 100
  | #[x] => x + 1
  | #[_, y] => y * 2
  | #[x, _, z] => x + z
  | _ => 7

def getIf (a : Array Nat) (i : Nat) : Nat :=
  if h : i < a.size then a[i] else 42

def getD (a : Array Nat) (i : Nat) : Nat :=
  a.getD i 11

def getElse (a : Array Nat) (i : Nat) : Nat :=
  if a.size ≤ i then 0 else a[i]!

def firstOr (a : Array Nat) : Nat :=
  if a.size = 0 then 9 else a[0]!

def litLt (a : Array Nat) : Nat :=
  if 2 < a.size then a[0]! + a[2]! else 1

def sizeLt (a b : Array Nat) : Bool :=
  a.size < b.size

def sizeLe (a : Array Nat) : Bool :=
  a.size ≤ 2

def notKnown (a : Array Nat) : Nat :=
  if a.size = 1 then a.getD 1 3 + a[0]! else 0

/-- The index and the accumulator are the mutable variables of a loop: `a[i]` under `i < a.size`
    in the step, before the assignments of the next iteration. -/
def sumFuel (fuel : Nat) (a : Array Nat) (i acc : Nat) : Nat :=
  match fuel with
  | 0 => acc
  | f + 1 => if h : i < a.size then sumFuel f a (i + 1) (acc + a[i]) else acc

/-- The array and the index both change at every iteration. -/
def growRead (fuel : Nat) (a : Array Nat) (i : Nat) : Nat :=
  match fuel with
  | 0 => i + a.size
  | f + 1 => if h : i < a.size then growRead f (a.push a[i]) (i + 2) else growRead f (a.push 1) 0
