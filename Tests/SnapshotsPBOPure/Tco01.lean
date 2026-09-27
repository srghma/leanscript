def test (n : Nat) : Nat :=
  match n with
  | 0 => n
  | n + 1 => test n
