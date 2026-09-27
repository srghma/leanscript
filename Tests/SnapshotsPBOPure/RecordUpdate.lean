structure Rec where
  a : Int
  b : Int
  c : Int

def test1 (fn : Unit → Rec) (val : Int) : Int :=
  let rec1 := fn ()
  let rec2 := { rec1 with a := val, c := val + 1 }
  if rec2.a == 42 then
    rec2.c
  else
    rec1.c

def test7 (f : Int → Int) (y : Int) : Rec :=
  let z := f y
  let a : Rec := { a := z, b := z, c := z }
  let b := { a with a := a.a + 1 }
  let c := { b with b := b.b - 2 }
  c

deriving instance Repr for Rec
