/-!
`Array.append` on an array nothing else holds (`LeanScript.Backend.ArrayOwn`). Appending
copies the whole accumulator at every step, so an accumulator loop that builds `n`
entries takes `n²` steps; where the analysis proves that nothing else can see the
array the append is written as `_arrAppend`, which pushes the elements of the right
operand onto the left one and answers with it. Every other append is the array
literal `[...a, ...b]` it was before.
-/

/-- The accumulator loop: the array is the whole state of the loop, so every append
    of it may be done in place. -/
def test1 (xss : List (Array Nat)) : Array Nat := Id.run do
  let mut acc : Array Nat := #[]
  for xs in xss do
    acc := acc ++ xs
  return acc

/-- Both arrays come from outside the program: their caller may still hold them, so
    this append copies. -/
def test2 (a b : Array Nat) : Array Nat := a ++ b

/-- The left operand is read again after the append, so the append copies. -/
def test3 (b : Array Nat) : Array Nat × Array Nat :=
  let a := Array.replicate 3 0
  (a, a ++ b)

/-- Appending to an array *literal*: a literal is a fresh array nothing else can
    hold, and the result is one literal. -/
def test4 (b : Array Nat) : Array Nat := #[1, 2] ++ b

/-- An append inside a loop over a range, with the array built here. -/
def test5 (n : Nat) : Array Nat := Id.run do
  let mut acc : Array Nat := Array.emptyWithCapacity n
  for i in [0:n] do
    acc := acc ++ #[i, i * i]
  return acc
