structure R where
  foo : Int
  bar : String
  baz : Bool
deriving BEq, Repr

def test1 : Int → Int → Bool := fun a b => a != b
def test2 (a b : Int) : Bool := a != b
def test3 (a : Int) : Bool := 12 != a
def test4 (a : Int) : Bool := a != 12
def test5 : Int → Bool := fun a => 12 != a
def test6 (r : R) : Bool := { foo := 42, bar := "hello", baz := false : R } != r
