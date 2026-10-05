-- `USize` and `ISize` beyond the operators of `PrimOpInt01Configurable`: literals,
-- conversions, bitwise operations, remainders, comparisons in conditions, a loop.

def usizeLit (a : USize) : USize := a * 3 + 7
def usizeToNat (a : USize) : Nat := a.toNat + 1
def usizeOfNat (n : Nat) : USize := USize.ofNat n * 2
def natToUSize (n : Nat) : USize := n.toUSize
def usizeBits (a b : USize) : USize := (a &&& b) ||| (a ^^^ b)
def usizeNot (a : USize) : USize := ~~~a
def usizeMod (a b : USize) : USize := a % b
def usizeToUInt64 (a : USize) : UInt64 := a.toUInt64 + 1
def uint64ToUSize (x : UInt64) : USize := x.toUSize + 1
def uint32ToUSize (x : UInt32) : USize := x.toUSize
def usizeToUInt32 (a : USize) : UInt32 := a.toUInt32
def usizeToUInt8 (a : USize) : UInt8 := a.toUInt8
def usizeMax (a b : USize) : USize := if a < b then b else a
def usizeClamp (a : USize) : USize := if a ≤ 10 then a else 10

def isizeLit (a : ISize) : ISize := a * -3 + 7
def isizeToInt (a : ISize) : Int := a.toInt - 1
def isizeOfInt (i : Int) : ISize := ISize.ofInt i
def isizeMod (a b : ISize) : ISize := a % b
def isizeBits (a b : ISize) : ISize := (a &&& b) ||| (a ^^^ ~~~b)
def isizeToInt64 (a : ISize) : Int64 := a.toInt64 - 1
def int64ToISize (x : Int64) : ISize := x.toISize + 1
def isizeSign (a : ISize) : Int := if a < 0 then -1 else if a == 0 then 0 else 1
def isizeAbsDiff (a b : ISize) : ISize := if a ≤ b then b - a else a - b

/-- The sum `acc + (n-1) + … + 0`, in `USize`. -/
def usizeSumTo (n : Nat) (acc : USize) : USize :=
  match n with
  | 0 => acc
  | k + 1 => usizeSumTo k (acc + k.toUSize)

/-- `acc - (n-1) - … - 0`, in `ISize`. -/
def isizeSubTo (n : Nat) (acc : ISize) : ISize :=
  match n with
  | 0 => acc
  | k + 1 => isizeSubTo k (acc - ISize.ofNat k)
