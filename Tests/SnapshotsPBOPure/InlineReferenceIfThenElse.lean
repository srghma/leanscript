structure RecC where
  c : Bool

structure RecB where
  b : RecC

structure RecA where
  a : RecB
  d : Int

def fn (_r : α) : Int := 0

def test1 : Int :=
  let rec1 : RecA := { a := { b := { c := true } }, d := fn () }
  if rec1.a.b.c then 42 else fn rec1

def extern1 : RecA :=
  { a := { b := { c := true } }, d := fn () }

def test2 : Int :=
  if extern1.a.b.c then 42 else 99
