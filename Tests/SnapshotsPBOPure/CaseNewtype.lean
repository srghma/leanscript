structure NewTypeInt where
  val : Int

def test1 (v : NewTypeInt) : String :=
  match v.val with
  | 1 => "1"
  | 2 => "2"
  | 3 => "3"
  | _ => "catch"

def test2 : NewTypeInt → String
  | ⟨1⟩ => "1"
  | ⟨2⟩ => "2"
  | ⟨3⟩ => "3"
  | _ => "catch"
