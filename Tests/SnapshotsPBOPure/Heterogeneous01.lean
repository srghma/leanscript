private structure R1 where
  a : Int
  b : String × Float
  c : Bool
-- deriving Repr

private structure Fns where
  a : Int → Int
  b : Float → String × Float
  c : Bool → Bool

private structure Args where
  a : Int
  b : Float
  c : Bool

@[inline] private def zipRecord (fns : Fns) (args : Args) : R1 :=
  {
    a := fns.a args.a,
    b := fns.b args.b,
    c := fns.c args.c
  }

def test1 : R1 :=
  let fns : Fns := {
    a := fun i => i + 1,
    b := fun f => ("bar", f),
    c := fun b => !b
  }
  let args : Args := {
    a := 12,
    b := 42.0,
    c := true
  }
  zipRecord fns args

def test2 (args : Args) : R1 :=
  let fns : Fns := {
    a := fun i => i + 1,
    b := fun f => ("bar", f),
    c := fun b => !b
  }
  zipRecord fns args
