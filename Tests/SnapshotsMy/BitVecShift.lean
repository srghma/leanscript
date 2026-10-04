/-
Shifts of `BitVec w` at the widths of the fixed-width integers: by a bit vector of the same
width (`0` from the width on), by a literal, by a natural number, and by a bit vector of
another width.
-/

namespace BitVecShift

def shl8 (a b : BitVec 8) : BitVec 8 := a <<< b
def shr8 (a b : BitVec 8) : BitVec 8 := a >>> b
def shl16 (a b : BitVec 16) : BitVec 16 := a <<< b
def shr16 (a b : BitVec 16) : BitVec 16 := a >>> b
def shl32 (a b : BitVec 32) : BitVec 32 := a <<< b
def shr32 (a b : BitVec 32) : BitVec 32 := a >>> b
def shl64 (a b : BitVec 64) : BitVec 64 := a <<< b
def shr64 (a b : BitVec 64) : BitVec 64 := a >>> b

def shl32Lit (a : BitVec 32) : BitVec 32 := a <<< 3
def shr32Lit (a : BitVec 32) : BitVec 32 := a >>> 7
def shl32Big (a : BitVec 32) : BitVec 32 := a <<< 40
def shl64Lit (a : BitVec 64) : BitVec 64 := a <<< 3
def shr64Lit (a : BitVec 64) : BitVec 64 := a >>> 60

def shl32Nat (a : BitVec 32) (n : Nat) : BitVec 32 := a <<< n
def shr64Nat (a : BitVec 64) (n : Nat) : BitVec 64 := a >>> n

def shr32By8 (a : BitVec 32) (b : BitVec 8) : BitVec 32 := a >>> b
def shl64By32 (a : BitVec 64) (b : BitVec 32) : BitVec 64 := a <<< b

def toNat32 (a : BitVec 32) : Nat := a.toNat
def rotl32 (a : BitVec 32) (k : BitVec 32) : BitVec 32 := (a <<< k) ||| (a >>> (32 - k))

end BitVecShift
