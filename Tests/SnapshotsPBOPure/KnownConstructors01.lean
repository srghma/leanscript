def test1 : String :=
  (some "c").map (fun _ => "b") |>.getD "a"
