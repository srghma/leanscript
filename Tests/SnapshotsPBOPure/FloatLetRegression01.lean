structure FloatLetResult where
  b  : Int
  c1 : Int
  c2 : Int

structure WrapY where
  y : FloatLetResult

structure WrapX where
  x : WrapY

def test (f : Int → Int) : FloatLetResult :=
  ( let b := f 1
    ( let c := f 2
      ({ x := { y := { b := b, c1 := c, c2 := c } } } : WrapX)
    ).x
  ).y
