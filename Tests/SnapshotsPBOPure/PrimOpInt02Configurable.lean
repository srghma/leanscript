namespace TestUInt64

@[inline] def intValues {α : Type} (op : UInt64 → UInt64 → α) : Array α :=
  #[ op 1 1, op 1 2, op 2 1, op 1 (-2), op (-1) 2, op (-1) (-1) ]

def test1 := intValues (fun a b => a + b)
def test2 := intValues (fun a b => a - b)
def test3 := intValues (fun a b => a == b)
def test4 := intValues (fun a b => a != b)
def test5 := intValues (fun a b => decide (a < b))
def test6 := intValues (fun a b => decide (a > b))
def test7 := intValues (fun a b => decide (a <= b))
def test8 := intValues (fun a b => decide (a >= b))
def test9 := intValues (fun a b => a * b)
def test10 := intValues (fun a b => a / b)
def test11 : Array UInt64 := #[ -1, -(-1) ]

end TestUInt64

namespace TestUSize

@[inline] def intValues {α : Type} (op : USize → USize → α) : Array α :=
  #[ op 1 1, op 1 2, op 2 1, op 1 (-2), op (-1) 2, op (-1) (-1) ]

def test1 := intValues (fun a b => a + b)
def test2 := intValues (fun a b => a - b)
def test3 := intValues (fun a b => a == b)
def test4 := intValues (fun a b => a != b)
def test5 := intValues (fun a b => decide (a < b))
def test6 := intValues (fun a b => decide (a > b))
def test7 := intValues (fun a b => decide (a <= b))
def test8 := intValues (fun a b => decide (a >= b))
def test9 := intValues (fun a b => a * b)
def test10 := intValues (fun a b => a / b)
def test11 : Array USize := #[ -1, -(-1) ]

end TestUSize

namespace TestNat

@[inline] def intValues {α : Type} (op : Nat → Nat → α) : Array α :=
  #[ op 1 1, op 1 2, op 2 1, op 1 0, op 0 2, op 0 0 ]

def test1 := intValues (fun a b => a + b)
def test2 := intValues (fun a b => a - b)
def test3 := intValues (fun a b => a == b)
def test4 := intValues (fun a b => a != b)
def test5 := intValues (fun a b => decide (a < b))
def test6 := intValues (fun a b => decide (a > b))
def test7 := intValues (fun a b => decide (a <= b))
def test8 := intValues (fun a b => decide (a >= b))
def test9 := intValues (fun a b => a * b)
def test10 := intValues (fun a b => a / b)
-- def test11 : Array Nat := #[ -1, -(-1) ] -- Nat does not support negation

end TestNat

-------------------------------------------

namespace TestInt64

@[inline] def intValues {α : Type} (op : Int64 → Int64 → α) : Array α :=
  #[ op 1 1, op 1 2, op 2 1, op 1 (-2), op (-1) 2, op (-1) (-1) ]

def test1 := intValues (fun a b => a + b)
def test2 := intValues (fun a b => a - b)
def test3 := intValues (fun a b => a == b)
def test4 := intValues (fun a b => a != b)
def test5 := intValues (fun a b => decide (a < b))
def test6 := intValues (fun a b => decide (a > b))
def test7 := intValues (fun a b => decide (a <= b))
def test8 := intValues (fun a b => decide (a >= b))
def test9 := intValues (fun a b => a * b)
def test10 := intValues (fun a b => a / b)
def test11 : Array Int64 := #[ -1, -(-1) ]

end TestInt64

namespace TestISize

@[inline] def intValues {α : Type} (op : ISize → ISize → α) : Array α :=
  #[ op 1 1, op 1 2, op 2 1, op 1 (-2), op (-1) 2, op (-1) (-1) ]

def test1 := intValues (fun a b => a + b)
def test2 := intValues (fun a b => a - b)
def test3 := intValues (fun a b => a == b)
def test4 := intValues (fun a b => a != b)
def test5 := intValues (fun a b => decide (a < b))
def test6 := intValues (fun a b => decide (a > b))
def test7 := intValues (fun a b => decide (a <= b))
def test8 := intValues (fun a b => decide (a >= b))
def test9 := intValues (fun a b => a * b)
def test10 := intValues (fun a b => a / b)
def test11 : Array ISize := #[ -1, -(-1) ]

end TestISize

namespace TestInt

@[inline] def intValues {α : Type} (op : Int → Int → α) : Array α :=
  #[ op 1 1, op 1 2, op 2 1, op 1 (-2), op (-1) 2, op (-1) (-1) ]

def test1 := intValues (fun a b => a + b)
def test2 := intValues (fun a b => a - b)
def test3 := intValues (fun a b => a == b)
def test4 := intValues (fun a b => a != b)
def test5 := intValues (fun a b => decide (a < b))
def test6 := intValues (fun a b => decide (a > b))
def test7 := intValues (fun a b => decide (a <= b))
def test8 := intValues (fun a b => decide (a >= b))
def test9 := intValues (fun a b => a * b)
def test10 := intValues (fun a b => a / b)
def test11 : Array Int := #[ -1, -(-1) ]

end TestInt
