@[inline] def array : Array Int := #[1, 2, 3] -- need to inline?

def test1 : Option Int := array[0]?
def test2 : Option Int := array[1]?
def test3 : Option Int := array[2]?
def test4 : Option Int := array[3]?
