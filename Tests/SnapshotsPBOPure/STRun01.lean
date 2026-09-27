def test1 : Int := Id.run (pure 1)
def test2 : Int := Id.run (pure (1 + 2))
def test3 : Int := Id.run do
  let n := 1
  let m := 2
  pure (n + m)
