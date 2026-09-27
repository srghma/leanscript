def test1 (x : String) : String :=
  match x with
  | "foo" => "1"
  | "bar" => "2"
  | "" => "3"
  | _ => "catch"
