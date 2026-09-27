/-
The bitwise operations of `BitVec w` for the widths a knob decides.

The companion of `PrimOpBitVec01Configurable.lean`: the operations whose answer is a
bit pattern rather than a sum, at the two widths (32 and 64) whose representation
`bitvecRepr` decides.
-/

namespace TestBitVec32

def land (a b : BitVec 32) : BitVec 32 := a &&& b
def lor (a b : BitVec 32) : BitVec 32 := a ||| b
def xor (a b : BitVec 32) : BitVec 32 := a ^^^ b
def shiftLeft (a b : BitVec 32) : BitVec 32 := a <<< b
def shiftRight (a b : BitVec 32) : BitVec 32 := a >>> b
def complement (a : BitVec 32) : BitVec 32 := ~~~a

end TestBitVec32

namespace TestBitVec64

def land (a b : BitVec 64) : BitVec 64 := a &&& b
def lor (a b : BitVec 64) : BitVec 64 := a ||| b
def xor (a b : BitVec 64) : BitVec 64 := a ^^^ b
def shiftLeft (a b : BitVec 64) : BitVec 64 := a <<< b
def shiftRight (a b : BitVec 64) : BitVec 64 := a >>> b
def complement (a : BitVec 64) : BitVec 64 := ~~~a

end TestBitVec64
