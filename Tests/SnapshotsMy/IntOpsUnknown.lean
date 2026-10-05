/-! Variations of `Tests/SnapshotsPBOPure/PrimOpInt02NonConfigurable.lean`: `intValues` applied to
operations that read an unknown `c`, so that they are not folded to literals.  The optimiser
drops the units (`x - 0`, `x / 1`, `x * 1`, `x + 0`), cancels `-(-x)`, writes `x * -1` and
`0 - x` as `-x` and `x - k` as `x + (-k)` (folded with the literals around it); the conversion
to JavaScript writes an addition of a negative literal as a subtraction (`x + 255` at `UInt8`
is `(x - 1) & 255`). -/

namespace TestUInt8

@[inline] def intValues {α : Type} (op : UInt8 → UInt8 → α) : Array α :=
  #[ op 1 1, op 1 2, op 2 1, op 1 (-2), op (-1) 2, op (-1) (-1) ]

def t1 (c : UInt8) := intValues (fun a b => a + b + c)
def t2 (c : UInt8) := intValues (fun a b => decide (a * c < b))
def t3 (c : UInt8) := intValues (fun a b => a / c - b)
def t4 (c : UInt8) := intValues (fun a b => c - (a - b))
def t5 (c : UInt8) := intValues (fun a b => (c - a) - b)
def t6 (c : UInt8) := #[c - 0, c / 1, c * 1, c + 0, -(-c), 0 - c, c * 255, c - 1 + 1]

end TestUInt8

namespace TestInt8

@[inline] def intValues {α : Type} (op : Int8 → Int8 → α) : Array α :=
  #[ op 1 1, op 1 2, op 2 1, op 1 (-2), op (-1) 2, op (-1) (-1) ]

def t1 (c : Int8) := intValues (fun a b => a + b + c)
def t2 (c : Int8) := intValues (fun a b => decide (a * c < b))
def t3 (c : Int8) := intValues (fun a b => a / c - b)
def t4 (c : Int8) := intValues (fun a b => (c - a) - b)
def t5 (c : Int8) := #[c - 0, c / 1, c * 1, c + 0, -(-c), 0 - c, c * (-1), c - 1 + 1, c + c * (-1)]

end TestInt8

namespace TestInt32

def t1 (c : Int32) := #[c + 1 + 2, c * 2 * 3, -(-c), c - 0, c * 1, c + 0, 0 - c, c - 5, c * (-1)]
def t2 (c : Int32) (d : Int32) := #[c - d - 1, (c - 1) - (d - 2), -(-(c - d))]

end TestInt32

namespace TestUInt32

def t1 (c : UInt32) := #[c + 1 + 2, c * 2 * 3, -(-c), c - 0, c * 1, c + 0, 0 - c, c / 1, c - 5]
def t2 (c : UInt32) := #[c == c, c != c, decide (c < c), decide (c ≤ c), decide (c + 1 > c)]

end TestUInt32

namespace TestInt

def t1 (c : Int) := #[c - 0, c / 1, -(-c), 0 - c, c * (-1), c - 3, c - 3 + 3, c + (-3)]

end TestInt

namespace TestNat

def t1 (c : Nat) := #[c - 0, c / 1, c * 1, c + 0]

end TestNat
