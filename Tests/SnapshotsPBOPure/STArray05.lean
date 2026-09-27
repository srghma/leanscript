def test (x : Bool) : Array Int := Id.run do
  let mut arr := #[]
  if x then
    arr := arr.push 1
  else
    arr := #[2] ++ arr
  pure arr
