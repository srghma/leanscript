def test1 (f : Float) : String :=
  if f == 1.0 then "1"
  else if f == 2.0 then "2"
  else if f == 3.0 then "3"
  else "catch"

-- TODO: enable when on latest lean version
-- def test2 : Float → String
--   | 1.0 => "1"
--   | 2.0 => "2"
--   | 3.0 => "3"
--   | _ => "catch"
