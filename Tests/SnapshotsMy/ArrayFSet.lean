/-!
`Array.set` and `Array.swap`, whose bounds are proved (the externs `lean_array_fset` and
`lean_array_fswap`), and `push` / `pop` on a typed array.  The runtime has an `_immutable`
(copying) and a `_mutable` (in place) function for each of `fset` and `fswap`; neither checks
the bounds.  A typed array cannot grow or shrink, so its `push` / `pop` always copy.
-/

/-- An array built here, which nothing else holds: `set` and `swap` update it in place. -/
def test1 (x : Nat) : Array Nat :=
  let a := #[x, 1, 2].push 3
  let b := a.set 0 7 (by simp [a])
  b.swap 1 2 (by simp [b, a]) (by simp [b, a])

/-- The array is read again after the update, so the update copies. -/
def test2 (x : Nat) : Array Nat × Array Nat :=
  let a := #[x, 1, 2].push 3
  (a, a.set 2 x (by simp [a]))

/-- `set` and `swap` on a typed array (a `Uint8Array` at the `faithful` preset), then a push and
    a pop.  The push and the pop copy, since a typed array cannot grow or shrink (the `set` and
    `swap` copy too here: the in-place pass only updates an array a variable holds). -/
def test3 (x : UInt8) : Array UInt8 :=
  (((#[x, 1, 2].set 2 x).swap 0 2).push 9).pop

/-- The array is the function's parameter: its caller may still hold it, so `set` copies. -/
def test4 (a : Array Nat) : Array Nat :=
  if h : 0 < a.size then a.set 0 5 else a
