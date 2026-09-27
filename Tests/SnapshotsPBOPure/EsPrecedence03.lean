def test1 (a b : UInt32) : UInt32 := (a >>> b) >>> b
def test2 (a b : UInt32) : UInt32 := a >>> (b >>> b)
