structure Rec where
  a : Int
  b : Int
  c : Int

/-- The updated field is known: the test is decided, the result is a field of the parameter. -/
def updKnown (r : Rec) : Int :=
  let r2 := { r with a := 42 }
  if r2.a == 42 then r2.c else r.b

/-- Reading a field that was not updated reads the original record. -/
def updOther (r : Rec) : Int :=
  ({ r with a := 1 }).b

/-- The updated record itself. -/
def updRet (r : Rec) : Rec :=
  { r with a := 42 }

/-- Two updates in a row. -/
def updChain (r : Rec) (x : Int) : Rec :=
  let r1 := { r with a := x }
  { r1 with b := r1.a + 1 }

/-- The call is only needed in one branch. -/
def updLazy (fn : Unit → Rec) (v : Int) : Int :=
  let rec1 := fn ()
  let rec2 := { rec1 with a := v, c := v + 1 }
  if rec2.a == 42 then rec2.c else rec1.c

/-- Updating every field forgets the original. -/
def updAll (r : Rec) (x : Int) : Rec :=
  { r with a := x, b := x, c := x }

/-- An update in a loop. -/
def updLoop (r : Rec) : Nat → Rec
  | 0 => r
  | n + 1 => updLoop { r with a := r.a + 1, c := r.c * 2 } n

/-- An update that depends on a condition. -/
def updCond (r : Rec) (b : Bool) : Int :=
  let r2 := if b then { r with a := 1 } else { r with a := 2 }
  r2.a + r2.b

/-- Both branches build the same record. -/
def updSameBranches (r : Rec) (x : Int) : Rec :=
  if x < 0 then { r with a := 0 } else { r with a := 0 }
