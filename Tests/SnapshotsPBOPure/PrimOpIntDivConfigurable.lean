@[inline] def test [BEq α] [HDiv α α α] (divNoInline : α -> α -> α) (a b : α) (expectedResult : α) : Bool :=
  a / b == divNoInline a b && a / b == expectedResult

namespace TestUInt64

@[noinline] def divNoInline (a b : UInt64) : UInt64 := a / b

def test1_0_shouldBeTrue := test divNoInline 1 0 0
def test3_2_shouldBeTrue := test divNoInline 3 2 1
def test3m2_shouldBeTrue := test divNoInline 3 (-2) 0

end TestUInt64

namespace TestUSize

@[noinline] def divNoInline (a b : USize) : USize := a / b

def test1_0_shouldBeTrue := test divNoInline 1 0 0
def test3_2_shouldBeTrue := test divNoInline 3 2 1
def test3m2_shouldBeTrue := test divNoInline 3 (-2) 0

end TestUSize

namespace TestNat

@[noinline] def divNoInline (a b : Nat) : Nat := a / b

def test1_0_shouldBeTrue := test divNoInline 1 0 0
def test3_2_shouldBeTrue := test divNoInline 3 2 1
-- def test3m2_shouldBeTrue := test divNoInline 3 (-2) ... -- Nat does not support negation

end TestNat

-------------------------------------------

namespace TestInt64

@[noinline] def divNoInline (a b : Int64) : Int64 := a / b

def test1_0_shouldBeTrue := test divNoInline 1 0 0
def test3_2_shouldBeTrue := test divNoInline 3 2 1
def test3m2_shouldBeTrue := test divNoInline 3 (-2) (-1)

end TestInt64

namespace TestISize

@[noinline] def divNoInline (a b : ISize) : ISize := a / b

def test1_0_shouldBeTrue := test divNoInline 1 0 0
def test3_2_shouldBeTrue := test divNoInline 3 2 1
def test3m2_shouldBeTrue := test divNoInline 3 (-2) (-1)

end TestISize

namespace TestInt

@[noinline] def divNoInline (a b : Int) : Int := a / b

def test1_0_shouldBeTrue := test divNoInline 1 0 0
def test3_2_shouldBeTrue := test divNoInline 3 2 1
def test3m2_shouldBeTrue := test divNoInline 3 (-2) (-1)

end TestInt
