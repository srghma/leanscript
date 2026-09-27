def fn {α : Type} (_ : α) : Float := 0.0

structure SubRec2 where
  c : Float

structure SubRec1 where
  b : SubRec2

structure Rec where
  a : SubRec1
  d : Float
  e : Float

@[inline]
def localTest (f : Rec → Float) : Float :=
  let r : Rec := { a := { b := { c := 99.0 } }, d := fn (), e := 11.0 }
  let res := f r
  res

def test1 : Float := localTest (fun rec => rec.a.b.c + rec.e)
def test2 : Float := localTest (fun rec => rec.a.b.c - rec.e)
def test3 : Float := localTest (fun rec => rec.a.b.c * rec.e)
def test4 : Float := localTest (fun rec => rec.a.b.c / rec.e)

def extern : Rec := { a := { b := { c := 99.0 } }, d := fn (), e := 11.0 }

@[inline]
def externTest (f : Rec → Float) : Float :=
  f extern

def test5 : Float := externTest (fun rec => rec.a.b.c + rec.e)
def test6 : Float := externTest (fun rec => rec.a.b.c - rec.e)
def test7 : Float := externTest (fun rec => rec.a.b.c * rec.e)
def test8 : Float := externTest (fun rec => rec.a.b.c / rec.e)
