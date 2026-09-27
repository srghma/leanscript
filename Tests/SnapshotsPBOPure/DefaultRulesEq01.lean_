structure Rec where
  a : Int
  b : Int
deriving BEq, Repr

structure Rec2 where
  a : Int
  b : Int
  c : Int
deriving BEq, Repr

def test1 : Bool := { a := 1, b := 2 : Rec } == { a := 1, b := 2 : Rec }
def test2 : Bool := { a := 1, b := 2 : Rec } == { a := 2, b := 2 : Rec }

def test3 : Bool := { a := 1, b := 2, c := 3 : Rec2 } == { a := 1, b := 2, c := 3 : Rec2 }
def test4 : Bool := { a := 1, b := 2, c := 3 : Rec2 } == { a := 1, b := 2, c := 4 : Rec2 }
