inductive SumType
  | L (n : Nat)
  | R (n : Nat)

def test1 (v : SumType) : String :=
  match v with
  | .L 1 => "1"
  | .L 2 => "2"
  | .L _ => "3"
  | .R _ => "4"
