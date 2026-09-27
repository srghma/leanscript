def fn {α : Type} (_ : α) : Int := 0

structure SubRec2 where
  c : Bool

structure SubRec1 where
  b : SubRec2

structure Rec where
  a : SubRec1
  d : Int
  e : Bool
  f : Bool

def test1 : Int :=
  let r : Rec := { a := { b := { c := true } }, d := fn (), e := true, f := false }
  if r.a.b.c && r.e then 42 else fn r

def test2 : Int :=
  let r : Rec := { a := { b := { c := true } }, d := fn (), e := true, f := false }
  if r.f || r.a.b.c then 42 else fn r

def test3 : Int :=
  let r : Rec := { a := { b := { c := true } }, d := fn (), e := true, f := false }
  if !r.a.b.c then fn r else 42

def extern1 : Rec := { a := { b := { c := true } }, d := fn (), e := true, f := false }

def test4 : Int :=
  if extern1.a.b.c && extern1.e then 42 else 99

def test5 : Int :=
  if extern1.f || extern1.a.b.c then 42 else 99

def test6 : Int :=
  if !extern1.a.b.c then 99 else 42
