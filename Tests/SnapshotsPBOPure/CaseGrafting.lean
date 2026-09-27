def test1 : Bool → Bool → Bool → Int
  | _, false, true => 1
  | false, true, _ => 2
  | _, _, false => 3
  | _, _, true => 4
