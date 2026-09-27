abbrev F := Unit → Int → Int

-- f and g should be evaluated only once because of Common Subexpression Elimination (CSE)
-- TODO: make this optimization configurable?
def test1 (f g : F) : Int → Int :=
  f () ∘ g ()

def test2 (f g : F) : Int → Int :=
  g () ∘ (f () ∘ g ())

def test3 (f g : F) : Int → Int :=
  (f () ∘ g ()) ∘ (f () ∘ g ())

def test4 (f g : F) : Int → Int :=
  ((g () ∘ f ()) ∘ g ()) ∘ (f () ∘ g ())
