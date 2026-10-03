/-! Accesses to arrays whose bounds are known from a test against a literal: each is a plain
`a[i]` in JavaScript, not a call of the runtime that checks the bounds again. -/

def array : Array Int := #[1, 2, 3]

/-- `xs[i]?` once `xs` is inlined: `i < 3 ? { tag: 1, _1: [1, 2, 3][i] } : { tag: 0 }`. -/
def getOpt (i : Nat) : Option Int := array[i]?

def getD (i : Nat) : Int := #[10, 20, 30][i]?.getD 0

def getLe (i : Nat) : Int := if i ≤ 2 then #[10, 20, 30][i]! else 0

def getGe (i : Nat) : Int := if 3 ≤ i then 0 else #[10, 20, 30][i]!

/-- The test does not prove the bounds (`3 < 4`): the access checks them. -/
def getUnproved (i : Nat) : Int := if i < 4 then #[10, 20, 30][i]! else 0

def getSized (a : Array Int) (i : Nat) : Int :=
  if a.size = 5 then (if i < 5 then a[i]! else 1) else 2

/-- The test does not prove the bounds (`5 < 6`): the access checks them. -/
def getSizedUnproved (a : Array Int) (i : Nat) : Int :=
  if a.size = 5 then (if i < 6 then a[i]! else 1) else 2
