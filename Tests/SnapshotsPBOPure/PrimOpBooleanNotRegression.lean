def test {α : Type} (comp : α → α → Ordering) (a b : α) : Bool :=
  comp a b != Ordering.eq
