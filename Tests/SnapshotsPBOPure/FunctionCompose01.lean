def f (_ : String) : String := "a"
def g (_ : String) : String := "b"

def test1 := f ∘ g
def test2 := g ∘ (f ∘ g)
def test3 := (f ∘ g) ∘ (f ∘ g)
def test4 := ((g ∘ f) ∘ g) ∘ (f ∘ g)
