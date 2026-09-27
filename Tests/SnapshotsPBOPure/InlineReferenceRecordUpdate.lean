-- @js_export: extern, fn$p, test1, test2
structure Rec where
  a : Int
  b : Int
  c : Int

def test1 (fn : Unit → Rec) : Int :=
  let rec1 := fn ()
  let rec2 := { rec1 with a := 42, b := (fn ()).b }
  if rec2.a == 42 then rec2.c else (fn ()).c

def fn_prime (_ : Unit) : Rec :=
  { a := 1, b := 2, c := 3 }

def extern1 : Rec :=
  { fn_prime () with a := 42 }

def test2 : Int :=
  if extern1.a == 42 then extern1.c else 0
