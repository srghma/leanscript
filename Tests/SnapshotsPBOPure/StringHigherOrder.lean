def stringValues (op : String → String → α) : List α :=
  [ op "a" "a"
  , op "a" "b"
  , op "b" "a"
  ]

def test1 := stringValues (· == ·)
def test2 := stringValues (· != ·)
def test3 := stringValues (fun a b => decide (decide (a < b)))
def test4 := stringValues (fun a b => decide (decide (a > b)))
def test7 := stringValues (· ++ ·)
