import Std.Data.HashMap
import Std.Data.HashSet

/-!
The three representations `LakeJs/Backend/HashRepr.lean` gives a hash container, and
the copy it makes of one that is looked at after an operation that answers with a new
container.
-/

/-- String keys: the entries are the properties of a prototype-less object. -/
def test1 (xs : List String) : Nat := Id.run do
  let mut m : Std.HashMap String Nat := {}
  for x in xs do
    m := m.insert x (m.getD x 0 + 1)
  return m.size

/-- Number keys: a `Map`. -/
def test2 (xs : List Nat) : Option Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := {}
  for x in xs do
    m := m.insert x (x * x)
  return m[3]?

/-- Nothing is stored: a `Set`. -/
def test3 (xs : List String) : Nat := Id.run do
  let mut s : Std.HashSet String := {}
  for x in xs do
    s := s.insert x
  return s.size + (if s.contains "a" then 1 else 0)

/-- A map and a set in one function: they start from empty containers of their own. -/
def test4 (xs : List String) : Nat := Id.run do
  let mut m : Std.HashMap String Nat := {}
  for x in xs do
    m := m.insert x 1
  let mut s : Std.HashSet String := {}
  for x in xs do
    s := s.insert (x ++ "!")
  return m.size + s.size

/-- Two containers erased out of one: each works on a copy. -/
def test5 (xs : List String) : Nat := Id.run do
  let mut m : Std.HashMap String Nat := {}
  for x in xs do
    m := m.insert x 1
  let a := m.erase "a"
  let b := m.erase "b"
  return a.size * 100 + b.size

/-- String keys, and the size is never asked for: a plain object, with no number of
    entries to keep up to date. -/
def test7 (xs : List String) (k : String) : Nat := Id.run do
  let mut m : Std.HashMap String Nat := {}
  for x in xs do
    m := m.insert x x.length
  return m.getD k 0

/-- The order the entries come out in is Lean's, which no JavaScript container has:
    this keeps Lean's own implementation. -/
def test6 (xs : List String) : List String := Id.run do
  let mut m : Std.HashMap String Nat := {}
  for x in xs do
    m := m.insert x 1
  return m.toList.map (·.1)
