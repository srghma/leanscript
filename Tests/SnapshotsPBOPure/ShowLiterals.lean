structure MyRec where
  foo : String
  bar : Bool
deriving Repr

def test1 := toString 42
def test2 := toString 42.0
def test3 := toString true
def test4 := toString "wat"
def test5 := toString 'w'
def test6 := repr ({ foo := "1", bar := true } : MyRec)
def test7 := repr #[1, 2, 3, 4]
