abbrev F := Int → String

-- Pointwise Semigroup (Append) instance for functions: (f ++ g) x = f x ++ g x
instance {α β : Type} [Append β] : Append (α → β) where
  append f g := fun x => f x ++ g x

-- test1 :: F -> F -> Int -> String
-- test1 f g = f <> g
def test1 (f g : F) : Int → String :=
  f ++ g

-- test2 :: F -> F -> Int -> String
-- test2 f g = f <> g <> f <> g
def test2 (f g : F) : Int → String :=
  f ++ g ++ f ++ g

-- Verification:
-- def f (x : Int) : String := s!"[{x}]"
-- def g (x : Int) : String := s!"({x})"

-- #eval test1 f g 5  -- "[5](5)"
-- #eval test2 f g 5  -- "[5](5)[5](5)"
