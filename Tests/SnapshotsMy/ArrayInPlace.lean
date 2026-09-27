/-!
The array updates the backend performs in place (`LeanScript.Backend.ArrayOwn`). An update
of an array nothing else holds becomes the JavaScript that mutates it (`_arrPush`,
`_arrSet`, `_arrPop`, `_arrSwap`); every other update copies the array, as Lean's
persistent `Array` requires. The empty array a function starts from is built once,
while the module is loaded, so a copy of it is made (`_arrClone`) before it is
updated.
-/

/-- A push loop: the array is the whole state of the loop. -/
def test1 (n : Nat) : Array Nat := Id.run do
  let mut a : Array Nat := Array.emptyWithCapacity n
  for i in [0:n] do
    a := a.push (i * i)
  return a

/-- The array a whole program shares is copied once, and then written into. -/
def test2 (xs : List Nat) : Array Nat := Id.run do
  let mut a : Array Nat := Array.replicate 8 0
  for x in xs do
    a := a.set! (x % 8) (a[x % 8]! + 1)
  return a

/-- The array is the function's parameter: its caller may still hold it, so this one
    copies. -/
def test3 (a0 : Array Nat) : Array Nat := Id.run do
  let mut a := a0
  for i in [0:a.size] do
    a := a.set! i (2 * a[i]!)
  return a

/-- The array is read again after the update, so the update copies. -/
def test4 (n : Nat) : Array Nat × Array Nat :=
  let a := Array.replicate 3 n
  (a, a.set! 0 7)

/-- `swap` and `pop` on an array built here. -/
def test5 (n : Nat) : Array Nat := Id.run do
  let mut a : Array Nat := Array.emptyWithCapacity n
  for i in [0:n] do
    a := a.push i
  for i in [0:n / 2] do
    a := a.swapIfInBounds i (n - i - 1)
  return a.pop

/-- A hand-written recursion: every step but the last answers with what the step below
    it answered with, which is what lets the push be done in place. -/
private def buildRec : Nat → Array Nat → Array Nat
  | 0, a => a
  | n + 1, a => buildRec n (a.push n)

/-- The recursion above, on an array built here. (An *exported* function is handed its
    array from outside the program, so the array of `buildRec` is only owned because
    the only caller of it is this one.) -/
def test6 (n : Nat) : Array Nat := buildRec n (Array.emptyWithCapacity n)
