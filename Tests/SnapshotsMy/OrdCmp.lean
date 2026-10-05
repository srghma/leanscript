-- Comparisons that Lean's externs only express with `<` and `≤`: `a > b` is `b < a`, `a ≥ b` on
-- `String`/`Char` is `!(a < b)`, …  Written with the operator that reads best when that keeps
-- the answer (`JsTerm/Lower/OrdCmp.lean`).

def natGt (a b : Nat) : Bool := decide (a > b)
def natGe (a b : Nat) : Bool := decide (a ≥ b)
def natNotLt (a b : Nat) : Bool := !(decide (a < b))
def natNotLe (a b : Nat) : Bool := !(decide (a ≤ b))
def intGt (a b : Int) : Bool := decide (a > b)
def intGe (a b : Int) : Bool := decide (a ≥ b)
def uint8Gt (a b : UInt8) : Bool := decide (a > b)
def uint32Ge (a b : UInt32) : Bool := decide (a ≥ b)
def strGt (a b : String) : Bool := decide (a > b)
def strLe (a b : String) : Bool := decide (a ≤ b)
def strGe (a b : String) : Bool := decide (a ≥ b)
def charLt (a b : Char) : Bool := decide (a < b)
def charGe (a b : Char) : Bool := decide (a ≥ b)
def charIsLower (c : Char) : Bool := decide ('a' ≤ c) && decide (c ≤ 'z')
def charIfGt (a b : Char) (x y : Nat) : Nat := if a > b then x else y
-- a computed operand keeps its place: computed first, as in Lean
def natGtComputed (a b : Nat) : Bool := decide (a > b + 1)
def natNotLtComputed (a b : Nat) : Bool := !(decide (a + 1 < b))
-- floats: the operands may be swapped (`a > b`), but `!(a < b)` is not `a >= b` (`NaN`)
def floatGt (a b : Float) : Bool := decide (a > b)
def floatNotLt (a b : Float) : Bool := !(decide (a < b))
