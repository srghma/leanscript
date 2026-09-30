def test1 : Int → Int
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | n => panic! ("mypanic " ++ toString n)
