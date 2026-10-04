/-! Comparisons of booleans (`JsTerm/Lower/BoolCmp.lean`): `==`, `!=`, `<`, `>`, `≤`, `≥` on
`Bool` reach the conversion as conditionals of booleans, written as JavaScript comparisons
(`a === b`, `a < b`, …) when that keeps what is computed and in which order. -/

/-- Operands that are not variables: `===` keeps both computed, in order. -/
def eqCmp (x y : Nat) (b : Bool) : Bool := (x < y) == b

/-- `!=` of a computed condition. -/
def neCmp (x y : Nat) (b : Bool) : Bool := (x == y) != b

/-- `<` of a computed condition keeps its conditional (`y` is only read when the condition is
    false; and `x < 5 < b` would be hard to read). -/
def ltComputed (x : Nat) (b : Bool) : Bool := decide (x < 5) < b

/-- `≤` of a computed condition keeps its conditional too. -/
def leComputed (x : Nat) (b : Bool) : Bool := decide (x < 5) ≤ b

/-- The negations: `!(a < b)` is `a >= b`, `!(a == b)` is `a !== b`, … -/
def notLt (a b : Bool) : Bool := !(a < b)
def notLe (a b : Bool) : Bool := !(a ≤ b)
def notGt (a b : Bool) : Bool := !(a > b)
def notGe (a b : Bool) : Bool := !(a ≥ b)
def notEq (a b : Bool) : Bool := !(a == b)
def notNe (a b : Bool) : Bool := !(a != b)

/-- A comparison used as a condition. -/
def ifEq (a b : Bool) (x y : Nat) : Nat := if a == b then x else y

/-- `decide (a = b)` (`Bool.decEq`) is `===` too. -/
def decideEq (a b : Bool) : Bool := decide (a = b)

/-- Three parameters: the comparison of the first and the last. -/
def ltFar (a _b c : Bool) : Bool := c > a
