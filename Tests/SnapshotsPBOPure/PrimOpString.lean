def test1 (a b : String) : Bool := a == b
def test2 (a b : String) : Bool := a != b
def test3 (a b : String) : Bool := decide (a < b)
def test4 (a b : String) : Bool := decide (a > b)
def test5 (a b : String) : Bool := decide (a <= b)
def test6 (a b : String) : Bool := decide (a >= b)
def test7 (a b : String) : String := a ++ b
