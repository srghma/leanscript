-- Float literals, and the exact unit identities the optimiser uses (`Neu.floatUnit`):
-- `x * 1.0`, `1.0 * x`, `x / 1.0`, `x - 0.0` are `x` (for every float, -0.0 and NaN included).
def mulOne (x : Float) : Float := x * 1.0
def oneMul (x : Float) : Float := 1.0 * x
def divOne (x : Float) : Float := x / 1.0
def subZero (x : Float) : Float := x - 0.0
-- not units: kept (`x + 0.0` is `+0.0` at `x = -0.0`)
def addZero (x : Float) : Float := x + 0.0
def zeroAdd (x : Float) : Float := 0.0 + x
def mulTwo (x : Float) : Float := x * 2.0
def subZeroLeft (x : Float) : Float := 0.0 - x
def addNegZero (x : Float) : Float := x + 1.5 - 1.5
def lits (x : Float) : Float := x * 2.5e-3 + 1e21 - 0.1
def closed (x : Float) : Float := x + (1.5 + 1.0) * 2.0
-- Float32
def mulOne32 (x : Float32) : Float32 := x * 1.0
def divOne32 (x : Float32) : Float32 := x / 1.0
def addLit32 (x : Float32) : Float32 := x + 0.1
-- refused: NaN and -0.0 are not values of the language's floats
def negZero (x : Float) : Float := x * -0.0
def nanLit (x : Float) : Float := x + 0.0 / 0.0
