def test1 (inp : Array Int) : Array Int := Id.run do
  let mut arr := #[]
  arr := arr.push 1
  let n := (arr.size : Int)
  arr := arr ++ #[1, n]
  arr := arr ++ inp
  arr := arr ++ (#[1, 2, 3] ++ inp)
  arr := arr ++ (inp ++ #[2, 3, 4])
  arr := arr ++ (#[1, 2, 3] ++ inp ++ #[5, 6, 7])
  pure arr

def test2 (inp : Array Int) : Array Int := Id.run do
  let mut arr := #[]
  arr := #[1] ++ arr
  let n := (arr.size : Int)
  arr := #[1, n] ++ arr
  arr := inp ++ arr
  arr := (#[1, 2, 3] ++ inp) ++ arr
  arr := (inp ++ #[2, 3, 4]) ++ arr
  arr := (#[1, 2, 3] ++ inp ++ #[5, 6, 7]) ++ arr
  pure arr
