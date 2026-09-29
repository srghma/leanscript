namespace ArrStd
def tMap (a : Array Nat) : Array Nat := a.map (· + 1)
def tFilter (a : Array Nat) : Array Nat := a.filter (· % 2 == 0)
def tRev (a : Array String) : Array String := a.reverse
def tExtract (a : Array Nat) (i j : Nat) : Array Nat := a.extract i j
def tAny (a : Array Nat) : Bool := a.any (· > 3)
def tAll (a : Array Nat) : Bool := a.all (· > 3)
def tContains (a : Array Nat) (x : Nat) : Bool := a.contains x
def tFind (a : Array Nat) : Option Nat := a.find? (· > 2)
def tFindIdx (a : Array Nat) : Option Nat := a.findIdx? (· > 2)
def tIdxOf (a : Array String) (s : String) : Option Nat := a.idxOf? s
def tErase (a : Array Nat) (i : Nat) : Array Nat := a.eraseIdxIfInBounds i
def tInsert (a : Array Nat) (i : Nat) (x : Nat) : Array Nat := a.insertIdxIfInBounds i x
def tSort (a : Array Nat) : Array Nat := a.qsort (· < ·)
def tFoldr (a : Array Nat) : Nat := a.foldr (fun x acc => x + 2 * acc) 0
def tZip (a : Array Nat) (b : Array String) : Array (Nat × String) := a.zip b
def tZipWith (a b : Array Nat) : Array Nat := Array.zipWith (· * ·) a b
def tFlatMap (a : Array Nat) : Array Nat := a.flatMap (fun x => #[x, x])
def tFlatten (a : Array (Array Nat)) : Array Nat := a.flatten
def tBack (a : Array Nat) : Option Nat := a.back?
def tCount (a : Array Nat) : Nat := a.countP (· > 1)
def tTake (a : Array Nat) (n : Nat) : Array Nat := a.take n
def tU8 (a : Array UInt8) : Array UInt8 := (a.map (· + 1)).filter (· > 3) |>.reverse
end ArrStd
