def test1 (a : Float) : Float := a + (a + (a + a))
def test2 (a : Float) : Float := ((a + a) + a) + a
def test3 (a : Float) : Float := a + (a + (a - a))
def test4 (a : Float) : Float := ((a - a) + a) + a
def test5 (a : Float) : Float := (a - a) + (a + a)
