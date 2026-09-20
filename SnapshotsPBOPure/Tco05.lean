def span (p : Int → Bool) (arr : Array Int) : Option Nat :=
  let rec go (i : Nat) : Option Nat :=
    if h : i < arr.size then
      let x := arr[i]
      if p x then go (i + 1) else some i
    else
      none
  go 0
