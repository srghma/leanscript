def test1 (x : Float) : Float :=
  1.0 + (((((2.0 + x) + x) + x) + x) + 3.0) + 4.0

def test2 (x : Float) : Float :=
  1.0 + (2.0 + (x + (x + (x + (x + 3.0))))) + 4.0

def test3 (x : Float) : Float :=
  1.0 + (2.0 + (x + (x + (x + (x + 3.0))))) + 4.0 + (((((5.0 + x) + x) + x) + x) + 6.0) + 7.0

def test4 (x : Float) : Float :=
  1.0 * (((((2.0 * x) * x) * x) * x) * 3.0) * 4.0

def test5 (x : Float) : Float :=
  1.0 * (2.0 * (x * (x * (x * (x * 3.0))))) * 4.0

def test6 (x : Float) : Float :=
  1.0 * (2.0 * (x * (x * (x * (x * 3.0))))) * 4.0 * (((((5.0 * x) * x) * x) * x) * 6.0) * 7.0
