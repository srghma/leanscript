/-
Variants of `Tests/SnapshotsPBOPure/PrimOpBitVec01Configurable.lean`: the operations of
`BitVec w` at every width of a fixed-width unsigned integer (8, 16, 32, 64), chains of them,
the bitwise ones, `%`, and comparisons inside an `if`.  At these widths a bit vector is the
integer (`UInt32.ofBitVec`), so each operation is the integer's: written inline where the
integer's is (`(a + b) >>> 0`, `BigInt.asUintN(64, a * b)`), a call of the runtime otherwise.
-/

namespace BV8

def add (a b : BitVec 8) : BitVec 8 := a + b
def sub (a b : BitVec 8) : BitVec 8 := a - b
def mul (a b : BitVec 8) : BitVec 8 := a * b
def neg (a : BitVec 8) : BitVec 8 := -a
def land (a b : BitVec 8) : BitVec 8 := a &&& b
def lor (a b : BitVec 8) : BitVec 8 := a ||| b
def xor (a b : BitVec 8) : BitVec 8 := a ^^^ b
def compl (a : BitVec 8) : BitVec 8 := ~~~a
def mod (a b : BitVec 8) : BitVec 8 := a % b

end BV8

namespace BV16

def add (a b : BitVec 16) : BitVec 16 := a + b
def mulAdd (a b c : BitVec 16) : BitVec 16 := a * b + c
def compl (a : BitVec 16) : BitVec 16 := ~~~a
def lt (a b : BitVec 16) : Bool := a < b

end BV16

namespace BV32

def mulAdd (a b c : BitVec 32) : BitVec 32 := a * b + c
def land (a b : BitVec 32) : BitVec 32 := a &&& b
def lor (a b : BitVec 32) : BitVec 32 := a ||| b
def xor (a b : BitVec 32) : BitVec 32 := a ^^^ b
def compl (a : BitVec 32) : BitVec 32 := ~~~a
def mod (a b : BitVec 32) : BitVec 32 := a % b
def max (a b : BitVec 32) : BitVec 32 := if a < b then b else a
def sumSq (a b : BitVec 32) : BitVec 32 := a * a + b * b
def addOne (a : BitVec 32) : BitVec 32 := a + 1

end BV32

namespace BV64

def mulAdd (a b c : BitVec 64) : BitVec 64 := a * b + c
def land (a b : BitVec 64) : BitVec 64 := a &&& b
def lor (a b : BitVec 64) : BitVec 64 := a ||| b
def xor (a b : BitVec 64) : BitVec 64 := a ^^^ b
def compl (a : BitVec 64) : BitVec 64 := ~~~a
def mod (a b : BitVec 64) : BitVec 64 := a % b
def min (a b : BitVec 64) : BitVec 64 := if a ≤ b then a else b
def isZero (a : BitVec 64) : Bool := a == 0

end BV64
