@[inline] def boolValues (op : Bool → Bool → Bool) : Array Bool :=
  #[ op true true, op true false, op false true, op false false ]

def test1 := boolValues (fun a b => a && b)
def test2 := boolValues (fun a b => a || b)
def test3 := boolValues (fun a b => a == b)
def test4 := boolValues (fun a b => a != b)
def test5 := boolValues (· < ·)
def test6 := boolValues (fun a b => (a > b))
def test7 := boolValues (fun a b => decide (a <= b))
def test8 := boolValues (fun a b => a >= b)
def test9 := #[ !true, !false ]
