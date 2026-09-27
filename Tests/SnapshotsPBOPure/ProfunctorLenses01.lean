private structure RecBaz where
  baz : Int
deriving Repr

private structure RecFooBaz where
  foo : Int
  bar : RecBaz
deriving Repr

private structure RecFooBar where
  foo : Int
  bar : Int
deriving Repr

private def view_foo (a : RecFooBaz) : Int := a.foo
private def over_bar (f : Int → Int) (a : RecFooBar) : RecFooBar := { a with bar := f a.bar }
private def over_bar_baz (f : Int → Int) (a : RecFooBaz) : RecFooBaz := { a with bar := { a.bar with baz := f a.bar.baz } }

def test1 := view_foo
def test2 (a : RecFooBaz) := a.foo

def test3 := over_bar (fun i => i + 1)
def test4 (a : RecFooBar) := { a with bar := a.bar + 1 }

def test5 := over_bar_baz (fun i => i + 1)
def test6 (a : RecFooBaz) := { a with bar := { a.bar with baz := a.bar.baz + 1 } }

def test7 (a : RecFooBar) :=
  let a' := { a with foo := a.foo + 1 }
  { a' with bar := a'.bar + 42 }

def test8 (a : RecFooBar) :=
  let a' := { a with foo := a.foo + 1 }
  { a' with bar := a'.bar + 42 }
