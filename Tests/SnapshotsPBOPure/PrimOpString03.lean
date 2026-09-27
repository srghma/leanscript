def test1 (a : String) : String := "a" ++ "b" ++ a ++ "c" ++ "d"
def test2 (a : String) : String := "a" ++ (("b" ++ a) ++ "c") ++ "d"
def test3 (a : String) : String := "a" ++ ("b" ++ (a ++ "c")) ++ "d"
