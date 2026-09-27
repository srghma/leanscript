structure R where
  foo : String
  bar : Array String
deriving Repr

namespace Inline

@[inline] def appendR (a b : R) : R :=
  { foo := a.foo ++ b.foo, bar := a.bar ++ b.bar }

def test1 : R → R → R := appendR
def test2 (a b : R) : R := appendR a b
def test3 : R → R := appendR {
  foo := "hello",
  bar := #["hello"]
}
def test4 : R := appendR {
  foo := "hello",
  bar := #["hello"]
} {
  foo := ", World!",
  bar := #["World!"]
}

end Inline

namespace Noinline

@[noinline] def appendR (a b : R) : R :=
  { foo := a.foo ++ b.foo, bar := a.bar ++ b.bar }

def test1 : R → R → R := appendR
def test2 (a b : R) : R := appendR a b -- Eta-reduction
def test3 : R → R := appendR {
  foo := "hello",
  bar := #["hello"]
}
def test4 : R := appendR {
  foo := "hello",
  bar := #["hello"]
} {
  foo := ", World!",
  bar := #["World!"]
}

end Noinline

namespace AlwaysInline

@[always_inline] def appendR (a b : R) : R :=
  {
    foo := a.foo ++ b.foo,
    bar := a.bar ++ b.bar
  }

def test1 : R → R → R := appendR
def test2 (a b : R) : R := appendR a b
def test3 : R → R := appendR {
  foo := "hello",
  bar := #["hello"]
}
def test4 : R := appendR {
  foo := "hello",
  bar := #["hello"]
} {
  foo := ", World!",
  bar := #["World!"]
}

end AlwaysInline

namespace InlineIfReduceInline

@[inline_if_reduce] def appendR (a b : R) : R :=
  {
    foo := a.foo ++ b.foo,
    bar := a.bar ++ b.bar
  }

def test1 : R → R → R := appendR
def test2 (a b : R) : R := appendR a b
def test3 : R → R := appendR {
  foo := "hello",
  bar := #["hello"]
}
def test4 : R := appendR {
  foo := "hello",
  bar := #["hello"]
} {
  foo := ", World!",
  bar := #["World!"]
}

end InlineIfReduceInline
