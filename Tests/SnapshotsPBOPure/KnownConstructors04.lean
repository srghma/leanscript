def test1 (x : Int) : Array String :=
  let a := if x > 42 then some "Hello" else none
  #[ a.get! ++ ", World", a.get! ++ ", Universe" ]

def test2 (f : String → String → String) (x : Int) : String :=
  let a := if x > 42 then some "Hello" else none
  f (a.get! ++ ", World") (a.get! ++ ", Universe")

def test3 (x : Int) : Bool :=
  let a := if x > 42 then some true else none
  a.get! && !(a.get!)
