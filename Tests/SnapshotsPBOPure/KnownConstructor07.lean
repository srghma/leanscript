structure PairBox where
  foo : Int
  bar : Int
deriving Repr

def test (f : Int → Int) (y : Int) : PairBox :=
  let z := f y
  let a := { foo := z, bar := z : PairBox }
  let b := { a with foo := a.foo + 1 }
  { b with bar := b.bar - 2 }
