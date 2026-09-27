namespace TestUInt8

def land (a b : UInt8) : UInt8 := a &&& b
def lor  (a b : UInt8) : UInt8 := a ||| b
def shiftLeft (a b : UInt8) : UInt8 := a <<< b
def shiftRight (a b : UInt8) : UInt8 := a >>> b
def xor (a b : UInt8) : UInt8 := a ^^^ b
def complement (a : UInt8) : UInt8 := ~~~a

end TestUInt8

namespace TestUInt16

def land (a b : UInt16) : UInt16 := a &&& b
def lor  (a b : UInt16) : UInt16 := a ||| b
def shiftLeft (a b : UInt16) : UInt16 := a <<< b
def shiftRight (a b : UInt16) : UInt16 := a >>> b
def xor (a b : UInt16) : UInt16 := a ^^^ b
def complement (a : UInt16) : UInt16 := ~~~a

end TestUInt16

namespace TestUInt32

def land (a b : UInt32) : UInt32 := a &&& b
def lor  (a b : UInt32) : UInt32 := a ||| b
def shiftLeft (a b : UInt32) : UInt32 := a <<< b
def shiftRight (a b : UInt32) : UInt32 := a >>> b
def xor (a b : UInt32) : UInt32 := a ^^^ b
def complement (a : UInt32) : UInt32 := ~~~a

end TestUInt32

-------------------------------------------

namespace TestInt8

def land (a b : Int8) : Int8 := a &&& b
def lor  (a b : Int8) : Int8 := a ||| b
def shiftLeft (a b : Int8) : Int8 := a <<< b
def shiftRight (a b : Int8) : Int8 := a >>> b
def xor (a b : Int8) : Int8 := a ^^^ b
def complement (a : Int8) : Int8 := ~~~a

end TestInt8

namespace TestInt16

def land (a b : Int16) : Int16 := a &&& b
def lor  (a b : Int16) : Int16 := a ||| b
def shiftLeft (a b : Int16) : Int16 := a <<< b
def shiftRight (a b : Int16) : Int16 := a >>> b
def xor (a b : Int16) : Int16 := a ^^^ b
def complement (a : Int16) : Int16 := ~~~a

end TestInt16

namespace TestInt32

def land (a b : Int32) : Int32 := a &&& b
def lor  (a b : Int32) : Int32 := a ||| b
def shiftLeft (a b : Int32) : Int32 := a <<< b
def shiftRight (a b : Int32) : Int32 := a >>> b
def xor (a b : Int32) : Int32 := a ^^^ b
def complement (a : Int32) : Int32 := ~~~a

end TestInt32
