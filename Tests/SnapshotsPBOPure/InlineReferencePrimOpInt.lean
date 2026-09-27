def fn {α : Type} (_ : α) : Int := 0

structure SubRec2 where
  c : Int

structure SubRec1 where
  b : SubRec2

structure Rec where
  a : SubRec1
  d : Int
  e : Int

@[inline]
def localTest (f : Rec → Int) : Int :=
  let r : Rec := { a := { b := { c := 99 } }, d := fn (), e := 11 }
  let res := f r
  if res != -2147483648 then res -- bottom in PS Int is -2^31
  else fn r

def test1 : Int := localTest (fun rec => rec.a.b.c + rec.e)
def test2 : Int := localTest (fun rec => rec.a.b.c - rec.e)
def test3 : Int := localTest (fun rec => rec.a.b.c * rec.e)
def test4 : Int := localTest (fun rec => rec.a.b.c / rec.e)

def extern : Rec := { a := { b := { c := 99 } }, d := fn (), e := 11 }

@[inline]
def externTest (f : Rec → Int) : Int :=
  let res := f extern
  if res != -2147483648 then res
  else -2147483648

def test5 : Int := externTest (fun rec => rec.a.b.c + rec.e)
def test6 : Int := externTest (fun rec => rec.a.b.c - rec.e)
def test7 : Int := externTest (fun rec => rec.a.b.c * rec.e)
def test8 : Int := externTest (fun rec => rec.a.b.c / rec.e)
