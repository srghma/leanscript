/-! Variants of `Tests/SnapshotsPBOPure/InlineReferenceIfThenElse.lean` where the record is
built from parameters, so the condition is not decided while Lean is turned into `Term`. -/

structure RecC where
  c : Bool

structure RecB where
  b : RecC

structure RecA where
  a : RecB
  d : Int

def fn (_r : α) : Int := 0

/-- The condition is a known field of a record whose other field is a parameter. -/
def test3 (x : Int) : Int :=
  let rec1 : RecA := { a := { b := { c := true } }, d := x }
  if rec1.a.b.c then 42 else fn rec1

/-- The condition is a parameter; the branches read the record. -/
def test4 (c : Bool) (x : Int) : Int :=
  let rec1 : RecA := { a := { b := { c := c } }, d := x }
  if rec1.a.b.c then rec1.d + 1 else fn rec1

/-- A global function building the record. -/
def extern2 (x : Int) : RecA :=
  { a := { b := { c := true } }, d := x }

def test5 (x : Int) : Int :=
  if (extern2 x).a.b.c then (extern2 x).d else 99

/-- The record is a parameter. -/
def test6 (r : RecA) : Int :=
  if r.a.b.c then r.d else fn r

/-- Nested if-then-else on the same known field. -/
def test7 (c : Bool) (x : Int) : Int :=
  let rec1 : RecA := { a := { b := { c := c } }, d := x }
  if rec1.a.b.c then (if rec1.a.b.c then x else 0) else (if rec1.a.b.c then 1 else x + 2)

/-- The same field of a record parameter tested twice. -/
def test8 (r : RecA) : Int :=
  if r.a.b.c then (if r.a.b.c then r.d else 0) else 1

/-- A negated condition: inside `if !c`, `c` is known too. -/
def test9 (c : Bool) (x : Int) : Int :=
  if !c then (if c then 1 else x) else (if c then x + 1 else 2)

/-- The inner test is under a `let` of a computation. -/
def test10 (c : Bool) (x : Int) : Int :=
  if c then
    let y := x * x
    if c then y + 1 else y
  else 0
