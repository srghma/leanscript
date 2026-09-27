def test1 (a b c : Bool) : Int :=
  if a then
    if b then
      1
    else if c then
      2
    else
      3
  else if c then
    2
  else
    3
