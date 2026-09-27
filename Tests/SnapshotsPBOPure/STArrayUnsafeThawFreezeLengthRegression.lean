def test (x : Int) : Array Int := Id.run do
  let mut arr := #[x]
  arr := arr.push 12
  let len := (arr.size : Int)
  arr := arr.push len
  pure arr
