def test1 (a b : Char) : Bool := a == b
def test2 (a b : Char) : Bool := a != b
def test3 (a b : Char) : Bool := a < b
def test4 (a b : Char) : Bool := decide (a > b)
def test5 (a b : Char) : Bool := a <= b
def test6 (a b : Char) : Bool := decide (a >= b)
