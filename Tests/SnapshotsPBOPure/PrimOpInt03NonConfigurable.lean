namespace TestUInt8

def test1 : UInt8 := 200 + 200
def test2 : UInt8 := 50 - 200
def test3 : UInt8 := 20 * 20
def test4 (a : UInt8) : UInt8 := 200 + a + 200

end TestUInt8

namespace TestUInt16

def test1 : UInt16 := 50000 + 50000
def test2 : UInt16 := 10000 - 50000
def test3 : UInt16 := 1000 * 1000
def test4 (a : UInt16) : UInt16 := 50000 + a + 50000

end TestUInt16

namespace TestUInt32

def test1 : UInt32 := 3000000000 + 3000000000
def test2 : UInt32 := 1000000000 - 3000000000
def test3 : UInt32 := 2000000000 * 2000000000
def test4 (a : UInt32) : UInt32 := 3000000000 + a + 3000000000

end TestUInt32

-------------------------------------------

namespace TestInt8

def test1 : Int8 := 100 + 100
def test2 : Int8 := -100 - 100
def test3 : Int8 := 20 * 20
def test4 (a : Int8) : Int8 := 100 + a + 100

end TestInt8

namespace TestInt16

def test1 : Int16 := 20000 + 20000
def test2 : Int16 := -20000 - 20000
def test3 : Int16 := 1000 * 1000
def test4 (a : Int16) : Int16 := 20000 + a + 20000

end TestInt16

namespace TestInt32 -- same as purescript

def test1 : Int32 := 2000000000 + 2000000000
def test2 : Int32 := -2000000000 - 2000000000

-- XXX:
-- Should be `Math.imul(a, b) | 0` instead of purescript's `(a * b) | 0`
-- Because:
--   (2000000001 * 2000000001) | 0;       // Returns: -1946474496 (Wrong due to float precision loss)
--   Math.imul(2000000001, 2000000001);   // Returns: -1946474495 (Correct 32-bit overflow result)

def test3 : Int32 := 2000000001 * 2000000001
def test4 (a : Int32) : Int32 := 2000000000 + a + 2000000000

end TestInt32
