-- TODO: uncurried function is just function that takes x \x y \x z
def test1 (f : Int → Int → Int → Int) (g : Int → Int) : Int := f (g 1) 2 3
def test2 (f : Int → Int → Int → Int) (g : Int → Int) (i : Int) : Int := f (g 1) 2 i
def test3 (f : Int → Int → Int → Int) (g : Int → Int) (i j : Int) : Int := f (g 1) i j
def test4 (f : Int → Int → Int → Int) (i j k : Int) : Int := f i j k
