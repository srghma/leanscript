-- String append chains (`StrApp.normNeu`): regrouped from the left, empty literals dropped,
-- neighbouring literals merged.
def rightNested (x y : String) : String := x ++ ("a" ++ (y ++ ("b" ++ "c")))
def emptyLeft (x : String) : String := "" ++ x
def emptyRight (x : String) : String := x ++ ""
def emptyMiddle (x y : String) : String := x ++ ("" ++ y) ++ ""
def twoVars (x y : String) : String := (x ++ "-") ++ ((y ++ "-") ++ (x ++ "-" ++ y))
def closedPart (x : String) : String := ("a" ++ "b") ++ x ++ ("c" ++ ("d" ++ "e"))
def insideCall (x : String) : Nat := ("a" ++ (x ++ "b")).length
def ofCall (x y : String) : String := "[" ++ (String.push (x ++ "a") (Char.ofNat 98) ++ ("|" ++ y)) ++ "]"
def unicode (x : String) : String := "é" ++ (x ++ "ü") ++ "€"
