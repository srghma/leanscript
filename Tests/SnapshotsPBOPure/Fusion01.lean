-- Fusion01 is Fold-based (Push / Backward / foldr)
-- → In Lean std, this corresponds directly to Array.foldr!

-- 1. Church-encoded Fold (Rank-2 structure instead of newtype)
structure Fold (α : Type) where
  run : {r : Type} → (α → r → r) → r → r

-- 2. Stream combinators
@[inline]
def mapF (f : α → β) (fold : Fold α) : Fold β where
  run cons nil := fold.run (fun a acc => cons (f a) acc) nil

@[inline]
def filterMapF (f : α → Option β) (fold : Fold α) : Fold β where
  run cons nil :=
    flip fold.run nil fun a acc =>
      match f a with
      | some b => cons b acc
      | none   => acc

@[inline]
def filterF (p : α → Bool) (fold : Fold α) : Fold α :=
  filterMapF (fun a => if p a then some a else none) fold

-- 3. Array conversions using Lean's std Array and List
@[inline]
def fromArray (arr : Array α) : Fold α where
  run cons nil := arr.foldr cons nil

@[inline]
def toArray (fold : Fold α) : Array α :=
  (fold.run List.cons []).toArray

-- @[inline] export overArray
@[inline]
def overArray (f : Fold α → Fold β) (arr : Array α) : Array β :=
  toArray (f (fromArray arr))

-- 4. Helper for stripPrefix using std String functions
@[inline]
def dropPrefix1 (s : String) : Option String :=
  if s.startsWith "1" then some (s.drop 1).toString else none

-- 5. The fused pipeline
def test (arr : Array Int) : Array String :=
  flip overArray arr fun fold =>
    fold
      |> mapF (· + 1)
      |> mapF toString
      |> filterMapF dropPrefix1
      |> mapF ("2" ++ ·)
      |> filterF (· != "wat")
      |> mapF (· ++ "1")
