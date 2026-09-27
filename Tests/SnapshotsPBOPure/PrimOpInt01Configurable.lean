namespace TestUInt64

def add (a b : UInt64) : UInt64 := a + b
def sub (a b : UInt64) : UInt64 := a - b
def eq  (a b : UInt64) : Bool := a == b
def ne  (a b : UInt64) : Bool := a != b
def lt  (a b : UInt64) : Bool := a < b
def gt  (a b : UInt64) : Bool := a > b
def le  (a b : UInt64) : Bool := a <= b
def ge  (a b : UInt64) : Bool := a >= b
def mul (a b : UInt64) : UInt64 := a * b
def div (a b : UInt64) : UInt64 := a / b
def neg (a : UInt64) : UInt64 := -a

end TestUInt64

namespace TestUSize

def add (a b : USize) : USize := a + b
def sub (a b : USize) : USize := a - b
def eq  (a b : USize) : Bool := a == b
def ne  (a b : USize) : Bool := a != b
def lt  (a b : USize) : Bool := a < b
def gt  (a b : USize) : Bool := a > b
def le  (a b : USize) : Bool := a <= b
def ge  (a b : USize) : Bool := a >= b
def mul (a b : USize) : USize := a * b
def div (a b : USize) : USize := a / b
def neg (a : USize) : USize := -a

end TestUSize

namespace TestNat

def add (a b : Nat) : Nat := a + b
def sub (a b : Nat) : Nat := a - b
def eq  (a b : Nat) : Bool := a == b
def ne  (a b : Nat) : Bool := a != b
def lt  (a b : Nat) : Bool := a < b
def gt  (a b : Nat) : Bool := a > b
def le  (a b : Nat) : Bool := a <= b
def ge  (a b : Nat) : Bool := a >= b
def mul (a b : Nat) : Nat := a * b
def div (a b : Nat) : Nat := a / b
-- def neg (a : Nat) : Nat := -a -- Nat does not support negation

end TestNat

-------------------------------------------

namespace TestInt64

def add (a b : Int64) : Int64 := a + b
def sub (a b : Int64) : Int64 := a - b
def eq  (a b : Int64) : Bool := a == b
def ne  (a b : Int64) : Bool := a != b
def lt  (a b : Int64) : Bool := a < b
def gt  (a b : Int64) : Bool := a > b
def le  (a b : Int64) : Bool := a <= b
def ge  (a b : Int64) : Bool := a >= b
def mul (a b : Int64) : Int64 := a * b
def div (a b : Int64) : Int64 := a / b
def neg (a : Int64) : Int64 := -a

end TestInt64

namespace TestISize

def add (a b : ISize) : ISize := a + b
def sub (a b : ISize) : ISize := a - b
def eq  (a b : ISize) : Bool := a == b
def ne  (a b : ISize) : Bool := a != b
def lt  (a b : ISize) : Bool := a < b
def gt  (a b : ISize) : Bool := a > b
def le  (a b : ISize) : Bool := a <= b
def ge  (a b : ISize) : Bool := a >= b
def mul (a b : ISize) : ISize := a * b
def div (a b : ISize) : ISize := a / b
def neg (a : ISize) : ISize := -a

end TestISize

namespace TestInt

def add (a b : Int) : Int := a + b
def sub (a b : Int) : Int := a - b
def eq  (a b : Int) : Bool := a == b
def ne  (a b : Int) : Bool := a != b
def lt  (a b : Int) : Bool := a < b
def gt  (a b : Int) : Bool := a > b
def le  (a b : Int) : Bool := a <= b
def ge  (a b : Int) : Bool := a >= b
def mul (a b : Int) : Int := a * b
def div (a b : Int) : Int := a / b
def neg (a : Int) : Int := -a

end TestInt
