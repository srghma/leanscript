def test1 (arr : Array String) : Array String :=
  let x := #["a"]
  let y := #["b"]
  let z := #["c"]
  let w := #["d"]
  x ++ (y ++ (arr ++ (arr ++ (arr ++ (arr ++ z))))) ++ w

def test2 (arr : Array String) : Array String :=
  let x := #["a"]
  let y := #["b"]
  let z := #["c"]
  let w := #["d"]
  x ++ (y ++ arr ++ arr ++ arr ++ arr ++ z) ++ w

def test3 (arr : Array String) : Array String :=
  #["a"] ++ (#["b"] ++ (arr ++ (arr ++ (arr ++ (arr ++ #["c"]))))) ++ #["d"] ++ (#["e"] ++ arr ++ arr ++ arr ++ arr ++ #["f"]) ++ #["g"]
