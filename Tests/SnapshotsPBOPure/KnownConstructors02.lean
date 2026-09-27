def test (a : Except Int Int) : Int :=
  match some a with
  | some (Except.error b) => b
  | some (Except.ok c) => c
  | none => 42
