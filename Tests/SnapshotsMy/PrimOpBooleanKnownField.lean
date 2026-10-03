/-! Variants of `Tests/SnapshotsPBOPure/InlineReferencePrimOpBoolean.lean` where the record, or
the operands of `&&`, `||` and `!`, are parameters, so the conditions are not decided while Lean
is turned into `Term`: what is left to the optimiser (`Term.knownTests`, with `Neu.factsOf` and
`Neu.condSimp`). -/

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

/-- The record is built from parameters, its tested fields are known. -/
def test7 (x : Int) (g : Bool) : Int :=
  let r : Rec := { a := { b := { c := true } }, d := x, e := true, f := g }
  if r.a.b.c && r.e then r.d else fn r

/-- `false || g` is `g`. -/
def test8 (x : Int) (g : Bool) : Int :=
  let r : Rec := { a := { b := { c := g } }, d := x, e := true, f := false }
  if r.f || r.a.b.c then 42 else fn r

/-- The record is a parameter: `r.a.b.c && r.e ? 42 : 0`, one conditional. -/
def test9 (r : Rec) : Int :=
  if r.a.b.c && r.e then 42 else fn r

/-- `r.f || r.a.b.c ? 42 : r.d`. -/
def test10 (r : Rec) : Int :=
  if r.f || r.a.b.c then 42 else r.d

/-- `!r.a.b.c` is `r.a.b.c` with the arms swapped. -/
def test11 (r : Rec) : Int :=
  if !r.a.b.c then fn r else 42

/-- Inside `if c && d`, `c` is known true. -/
def test12 (c d : Bool) (x : Int) : Int :=
  if c && d then (if c then x else 1) else 2

/-- Inside the `else` of `if c || d`, `c` is known false. -/
def test13 (c d : Bool) (x : Int) : Int :=
  if c || d then 1 else (if c then x else 2)

/-- Inside the `else` of `if !c`, `c` is known true. -/
def test14 (c : Bool) (x : Int) : Int :=
  if !c then 1 else (if c then x else 2)

/-- `c && false` is `false`. -/
def test15 (c : Bool) (x : Int) : Int :=
  if c && false then x else 7

/-- `c || true` is `true`. -/
def test16 (c : Bool) (x : Int) : Int :=
  if c || true then x else 7

/-- `c && c` is `c`. -/
def test17 (c : Bool) : Bool := c && c

/-- `!c || c` is `true`. -/
def test18 (c : Bool) : Bool := !c || c

/-- `if c then 7 else 7` is `7`. -/
def test19 (c : Bool) (x : Int) : Int := if c then 7 else 7

/-- The fields of `r` known in both arms of a test of `r.a.b.c && r.e`. -/
def test20 (r : Rec) : Int :=
  if r.a.b.c && r.e then (if r.e then r.d else 0) else (if r.a.b.c then 1 else 2)

/-- Plain operators stay operators. -/
def test21 (c d : Bool) : Bool := c && d

def test22 (c d : Bool) : Bool := c || !d
