def test (x : Int) : String :=
  let a := if x > 42 then some "Hello" else none
  match a with
  | some str => str ++ ", World!"
  | none => ""
