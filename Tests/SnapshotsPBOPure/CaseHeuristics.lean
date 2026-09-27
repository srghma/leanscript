inductive Column where
  | zero
  | one (n : Int)
  | two (a : Int) (b : Int)

def testP : Int → Int → Int → Int
  | 1, 2, 1 => 1
  | 1, 2, 2 => 2
  | _, 2, 3 => 3
  | 1, _, 4 => 4
  | _, _, _ => 5

def testPB : Column → Column → Int
  | .one 1, .one 1 => 1
  | .two 2 3, .two 2 3 => 2
  | _, .zero => 3
  | _, _ => 4

def testPBA : Column → Column → Int
  | .one 1, .one 1 => 1
  | .one 2, .one 2 => 2
  | .two 1 _, .two _ _ => 3
  | _, _ => 4

def testPBAN : Column → Column → Int
  | .one 1, .one 1 => 1
  | .one 2, .one 2 => 2
  | .two _ _, .two _ _ => 3
  | _, _ => 4
