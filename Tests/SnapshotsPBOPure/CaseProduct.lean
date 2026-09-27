structure Product3 (α β γ : Type) where
  a : α
  b : β
  c : γ

def test1 : Product3 Nat Nat Nat → String
  | ⟨1, 2, 3⟩ => "1"
  | ⟨_, 4, _⟩ => "2"
  | ⟨4, 5, 6⟩ => "3"
  | _ => "catch"
