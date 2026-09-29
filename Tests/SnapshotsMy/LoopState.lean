/-!
Loops of `Id.run do` whose state is several mutable variables. The state of the loop is a
record (one field per variable), wrapped in the `ForInStep` of the iteration; in the
JavaScript, an accumulator that is always the same constructor is unboxed, and a record
accumulator becomes one variable per field, so each iteration assigns the variables and
allocates nothing.
-/

/-- Two variables, a sum and a count. -/
def sumCount (n : Nat) : Nat × Nat := Id.run do
  let mut s := 0
  let mut c := 0
  for i in [0:n] do
    s := s + i
    c := c + 1
  return (s, c)

/-- Fibonacci, two variables updated together. -/
def fib (n : Nat) : Nat := Id.run do
  let mut a := 0
  let mut b := 1
  for _ in [0:n] do
    (a, b) := (b, a + b)
  return a

/-- Three variables, updated under conditions. -/
def minMaxSum (n : Nat) : Nat × Nat × Nat := Id.run do
  let mut lo := 1000000
  let mut hi := 0
  let mut s := 0
  for i in [0:n] do
    let x := (i * 7) % 11
    if x < lo then lo := x
    if hi < x then hi := x
    s := s + x
  return (lo, hi, s)

/-- A loop that stops early: its `ForInStep` is not always the same constructor. -/
def firstAbove (n k : Nat) : Nat := Id.run do
  let mut r := 0
  for i in [0:n] do
    if k < i * i then
      r := i
      break
  return r

/-- A string and a count built together. -/
def repeatCount (s : String) (n : Nat) : String × Nat := Id.run do
  let mut acc := ""
  let mut len := 0
  for _ in [0:n] do
    acc := acc ++ s
    len := len + s.length
  return (acc, len)
