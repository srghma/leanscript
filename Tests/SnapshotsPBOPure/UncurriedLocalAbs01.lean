-- @js_export: sum, test
def test (x y : Int) : Int :=
  let fn a b :=
    #[ x, a, b, a, b, a, b, a, b, a, b, a, b, a, b, a, b, a, b ].foldl (fun s i => s + i) 0
  fn x y + fn y x
