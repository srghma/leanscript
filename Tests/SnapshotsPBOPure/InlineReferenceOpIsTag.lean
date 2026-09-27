inductive MyList (α : Type) where
  | Cons : α → MyList α → MyList α
  | Nil  : MyList α
  deriving Repr

structure RecC where
  c : MyList Int

structure RecB where
  b : RecC

structure RecA where
  a : RecB

structure RecD where
  d : RecA
  e : MyList Int

def test1 (fn : Unit → MyList Int) : MyList Int :=
  let list := MyList.Cons 1 (fn ())
  match list with
  | MyList.Cons _ _ => MyList.Cons 0 list
  | _ => MyList.Nil

def test2 (fn : Unit → MyList Int) : MyList Int :=
  let rec1 : RecA := { a := { b := { c := MyList.Cons 1 (fn ()) } } }
  match rec1.a.b.c with
  | MyList.Cons _ _ => MyList.Cons 0 rec1.a.b.c
  | _ => fn ()

def test3 (fn : Unit → MyList Int) : MyList Int :=
  let rec1 : RecA := { a := { b := { c := MyList.Cons 1 (fn ()) } } }
  let rec2 : RecD := { d := rec1, e := fn () }
  match rec2.d.a.b.c with
  | MyList.Cons _ _ => MyList.Cons 0 rec2.d.a.b.c
  | _ => fn ()

def fn_prime (_ : Unit) : MyList Int := MyList.Nil

def extern1 : MyList Int := MyList.Cons 1 (fn_prime ())
def extern2 : RecA := { a := { b := { c := MyList.Cons 1 (fn_prime ()) } } }
def extern3 : RecD := { d := extern2, e := fn_prime () }

def test4 : MyList Int :=
  match extern1 with
  | MyList.Cons _ _ => MyList.Cons 0 extern1
  | _ => MyList.Nil

def test5 : MyList Int :=
  match extern2.a.b.c with
  | MyList.Cons _ _ => MyList.Cons 0 extern2.a.b.c
  | _ => MyList.Nil

def test6 : MyList Int :=
  match extern3.d.a.b.c with
  | MyList.Cons _ _ => MyList.Cons 0 extern3.d.a.b.c
  | _ => MyList.Nil
