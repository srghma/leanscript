namespace TestUInt64

def land (a b : UInt64) : UInt64 := a &&& b
def lor  (a b : UInt64) : UInt64 := a ||| b
def shiftLeft (a b : UInt64) : UInt64 := a <<< b
def shiftRight (a b : UInt64) : UInt64 := a >>> b
def xor (a b : UInt64) : UInt64 := a ^^^ b
def complement (a : UInt64) : UInt64 := ~~~a

end TestUInt64

namespace TestUSize

def land (a b : USize) : USize := a &&& b
def lor  (a b : USize) : USize := a ||| b
def shiftLeft (a b : USize) : USize := a <<< b
def shiftRight (a b : USize) : USize := a >>> b
def xor (a b : USize) : USize := a ^^^ b
def complement (a : USize) : USize := ~~~a

end TestUSize

namespace TestNat

def land (a b : Nat) : Nat := a &&& b
def lor  (a b : Nat) : Nat := a ||| b
def shiftLeft (a b : Nat) : Nat := a <<< b
def shiftRight (a b : Nat) : Nat := a >>> b
def xor (a b : Nat) : Nat := a ^^^ b
-- def complement (a : Nat) : Nat := ~~~a

end TestNat

-------------------------------------------

namespace TestInt64

def land (a b : Int64) : Int64 := a &&& b
def lor  (a b : Int64) : Int64 := a ||| b
def shiftLeft (a b : Int64) : Int64 := a <<< b
def shiftRight (a b : Int64) : Int64 := a >>> b
def xor (a b : Int64) : Int64 := a ^^^ b
def complement (a : Int64) : Int64 := ~~~a

end TestInt64

namespace TestISize

def land (a b : ISize) : ISize := a &&& b
def lor  (a b : ISize) : ISize := a ||| b
def shiftLeft (a b : ISize) : ISize := a <<< b
def shiftRight (a b : ISize) : ISize := a >>> b
def xor (a b : ISize) : ISize := a ^^^ b
def complement (a : ISize) : ISize := ~~~a

end TestISize

namespace TestInt

-- Import `import Mathlib.Data.Int.Bitwise` to have them

-- def land (a b : Int) : Int := a &&& b
-- def lor  (a b : Int) : Int := a ||| b
-- def shiftLeft (a b : Int) : Int := a <<< b
-- def shiftRight (a b : Int) : Int := a >>> b
-- def xor (a b : Int) : Int := a ^^^ b
def complement (a : Int) : Int := ~~~a

end TestInt
