-- Definitions without parameters are exported as constants (`export const x = value;`,
-- `JsFun.isConst`), a body that is not a single expression as an arrow called on the spot;
-- the fixed-width integers are sample types of the checks (`--check`), edges of the range
-- included.
def maxMinusOne : Int32 := Int32.maxValue - 1
def minPlusOne : Int32 := Int32.minValue + 1
def byteMax : UInt8 := 255
def wrapped : UInt8 := byteMax + 1
def pair : Nat × String := (3, "three")
def small : Array Nat := #[1, 2, 3]
def someList : List String := ["a", "b"]
def sumTo (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:n] do
    s := s + i
  return s
def succ32 (x : Int32) : Int32 := x + 1
def neg16 (x : Int16) : Int16 := -x
def addU8 (x y : UInt8) : UInt8 := x + y
def mulU32 (x : UInt32) : UInt32 := x * 3
def subI8 (x y : Int8) : Int8 := x - y
def addU64 (x : UInt64) : UInt64 := x + 7
def divI64 (x : Int64) : Int64 := x / 2
