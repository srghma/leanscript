def test1 : Array Nat → String
  | #[] => "0"
  | #[1] => "1"
  | #[_] => "any1"
  | #[_, 2] => "2"
  | #[_, _, _] => "3"
  | _ => "catch"
