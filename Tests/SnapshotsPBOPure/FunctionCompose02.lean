abbrev F := Int → Int

def test1 (f g : F) : F :=
  f ∘ g

def test2 (f g : F) : F :=
  g ∘ (f ∘ g)

def test3 (f g : F) : F :=
  (f ∘ g) ∘ (f ∘ g)

def test4 (f g : F) : F :=
  ((g ∘ f) ∘ g) ∘ (f ∘ g)
