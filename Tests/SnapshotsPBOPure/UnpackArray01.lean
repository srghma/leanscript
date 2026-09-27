def test (fn1 : String → String → String) (fn2 : Unit → String) : String :=
  let array := #[ "foo", "bar", "baz", fn2 () ]
  fn1 array[0]! array[2]!
