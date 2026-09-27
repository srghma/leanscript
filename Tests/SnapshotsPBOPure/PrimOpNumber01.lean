namespace TestFloat
def test1 (a b : Float) : Float := a + b
def test2 (a b : Float) : Float := a - b
def test3 (a b : Float) : Bool := a == b
def test4 (a b : Float) : Bool := a != b
def test5 (a b : Float) : Bool := decide (a < b)
def test6 (a b : Float) : Bool := decide (a > b)
def test7 (a b : Float) : Bool := decide (a <= b)
def test8 (a b : Float) : Bool := decide (a >= b)
def test9 (a b : Float) : Float := a * b
def test10 (a b : Float) : Float := a / b
def test11 (a : Float) : Float := -a
def test12 (a b c : Float) : Float := a - (b - c)
def test13 (a b c : Float) : Float := a / (b / c)
end TestFloat

namespace TestFloat32
def test1 (a b : Float32) : Float32 := a + b
def test2 (a b : Float32) : Float32 := a - b
def test3 (a b : Float32) : Bool := a == b
def test4 (a b : Float32) : Bool := a != b
def test5 (a b : Float32) : Bool := decide (a < b)
def test6 (a b : Float32) : Bool := decide (a > b)
def test7 (a b : Float32) : Bool := decide (a <= b)
def test8 (a b : Float32) : Bool := decide (a >= b)
def test9 (a b : Float32) : Float32 := a * b
def test10 (a b : Float32) : Float32 := a / b
def test11 (a : Float32) : Float32 := -a
def test12 (a b c : Float32) : Float32 := a - (b - c)
def test13 (a b c : Float32) : Float32 := a / (b / c)
end TestFloat32
