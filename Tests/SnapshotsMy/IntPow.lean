-- Powers: `x ^ n` of `Int`s and `Nat`s (`Int.pow`, `Nat.pow`), and products of one unknown,
-- which the optimiser writes as powers (`x ** 3n` in JavaScript).

def powLit (x : Int) : Int := x ^ 3

def powVar (x : Int) (n : Nat) : Int := x ^ n

def powNeg (x : Int) : Int := (-x) ^ 3

def negPow (x : Int) : Int := -(x ^ 3)

def powPow (x : Int) : Int := (x ^ 2) ^ 3

def powTimes (x : Int) : Int := x ^ 2 * x * x

def cube (x : Int) : Int := x * x * x

def square (x : Int) : Int := x * x

def twoVars (x y : Int) : Int := x * y * x * y * x * 2

def natCube (x : Nat) : Nat := x * x * x * 7

def natPow (x n : Nat) : Nat := x ^ n * x

def powSum (x : Int) : Int := x * x * x + x * x * x
