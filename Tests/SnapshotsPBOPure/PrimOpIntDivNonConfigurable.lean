@[inline] private def test [BEq α] [HDiv α α α] (divNoInline : α -> α -> α) (a b : α) (expectedResult : α) : Bool :=
  a / b == divNoInline a b && a / b == expectedResult

namespace TestUInt8

@[noinline] private def divNoInline (a b : UInt8) : UInt8 := a / b

def test1_0__shouldBeTrue := test divNoInline 1 0 0
def test3_2__shouldBeTrue := test divNoInline 3 2 1
def test3m2__shouldBeTrue := test divNoInline 3 (-2) 0

end TestUInt8

namespace TestUInt16

@[noinline] def divNoInline (a b : UInt16) : UInt16 := a / b

def test1_0__shouldBeTrue := test divNoInline 1 0 0
def test3_2__shouldBeTrue := test divNoInline 3 2 1
def test3m2__shouldBeTrue := test divNoInline 3 (-2) 0

end TestUInt16

namespace TestUInt32

@[noinline] def divNoInline (a b : UInt32) : UInt32 := a / b

def test1_0_shouldBeTrue := test divNoInline 1 0 0
def test3_2_shouldBeTrue := test divNoInline 3 2 1
def test3m2_shouldBeTrue := test divNoInline 3 (-2) 0

end TestUInt32

-------------------------------------------

namespace TestInt8

@[noinline] def divNoInline (a b : Int8) : Int8 := a / b

def test1_0_shouldBeTrue := test divNoInline 1 0 0
def test3_2_shouldBeTrue := test divNoInline 3 2 1
def test3m2_shouldBeTrue := test divNoInline 3 (-2) (-1)

end TestInt8

namespace TestInt16

@[noinline] def divNoInline (a b : Int16) : Int16 := a / b

def test1_0_shouldBeTrue := test divNoInline 1 0 0
def test3_2_shouldBeTrue := test divNoInline 3 2 1
def test3m2_shouldBeTrue := test divNoInline 3 (-2) (-1)

end TestInt16

namespace TestInt32

@[noinline] def divNoInline (a b : Int32) : Int32 := a / b

def test1_0_shouldBeTrue := test divNoInline 1 0 0
def test3_2_shouldBeTrue := test divNoInline 3 2 1
def test3m2_shouldBeTrue := test divNoInline 3 (-2) (-1)

end TestInt32
