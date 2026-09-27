namespace TestUInt8

@[inline] def intValues {α : Type} (op : UInt8 → UInt8 → α) : Array α :=
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
def test11 : Array UInt8 := #[ -1, -(-1) ]

end TestUInt8

namespace TestUInt16

@[inline] def intValues {α : Type} (op : UInt16 → UInt16 → α) : Array α :=
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
def test11 : Array UInt16 := #[ -1, -(-1) ]

end TestUInt16

namespace TestUInt32

@[inline] def intValues {α : Type} (op : UInt32 → UInt32 → α) : Array α :=
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
def test11 : Array UInt32 := #[ -1, -(-1) ]

end TestUInt32

-------------------------------------------

namespace TestInt8

@[inline] def intValues {α : Type} (op : Int8 → Int8 → α) : Array α :=
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
def test11 : Array Int8 := #[ -1, -(-1) ]

end TestInt8

namespace TestInt16

@[inline] def intValues {α : Type} (op : Int16 → Int16 → α) : Array α :=
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
def test11 : Array Int16 := #[ -1, -(-1) ]

end TestInt16

namespace TestInt32

@[inline] def intValues {α : Type} (op : Int32 → Int32 → α) : Array α :=
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
def test11 : Array Int32 := #[ -1, -(-1) ]

end TestInt32
