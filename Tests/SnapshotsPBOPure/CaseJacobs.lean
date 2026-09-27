inductive Expr where
  | add (a : Expr) (b : Expr)
  | mul (a : Expr) (b : Expr)
  | succ (a : Expr)
  | zero


def renderExpr : Expr → String
  | .add a b => "Add(" ++ renderExpr a ++ " " ++ renderExpr b ++ ")"
  | .mul a b => "Mul(" ++ renderExpr a ++ " " ++ renderExpr b ++ ")"
  | .succ a => "Succ(" ++ renderExpr a ++ ")"
  | .zero => "Zero"

instance : ToString Expr where
  toString a := renderExpr a -- will be inlined

-- #print instToStringExpr

def test1 : Expr → String
  | .add .zero .zero => "e1"
  | .mul .zero x => "e2: " ++ toString x -- though toString is used - will use renderExpr anyway, tnx to optimization
  | .add (.succ x) y => "e3: " ++ toString x ++ " " ++ toString y
  | .mul x .zero => "e4: " ++ toString x
  | .mul (.add x y) z => "e5: " ++ toString x ++ " " ++ toString y ++ " " ++ toString z
  | .add x .zero => "e6: " ++ toString x
  | x => "e7: " ++ toString x
