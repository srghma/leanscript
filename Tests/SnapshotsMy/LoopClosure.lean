private def apply3 (f : Nat → Nat) : Nat := f 1 + f 2 + f 3

def test1 (k : Nat) (n : Nat) : Nat := Id.run do
  let mut s := 0
  for _ in [0:n] do
    s := s + apply3 (fun x => x + k)
  return s

def test2 (k : Nat) (xss : List (List Nat)) : List (List Nat) :=
  xss.map (fun xs => xs.map (fun x => x + k))
