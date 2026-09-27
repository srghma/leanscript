def stringValues {α : Type} (op : String → String → α) : Array α :=
  #[ op "a" "a", op "a" "b", op "b" "a" ]

def test1 := stringValues (fun a b => a == b)
def test2 := stringValues (fun a b => a != b)
def test3 := stringValues (fun a b => decide (a < b))
def test4 := stringValues (fun a b => decide (a > b))
def test5 := stringValues (fun a b => decide (a <= b))
def test6 := stringValues (fun a b => decide (a >= b))
def test7 := stringValues (fun a b => a ++ b)
