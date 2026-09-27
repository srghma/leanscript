-- Fusion03 is idiomatic lean code
-- (this test not present in purescript-backend-optimizer)

def test (arr : Array Int) : Array String :=
  arr
    |>.map (· + 1)
    |>.map toString
    |>.filterMap (fun s => if s.startsWith "1" then some (s.drop 1).toString else none)
    |>.map ("2" ++ ·)
    |>.filter (· != "wat")
    |>.map (· ++ "1")
