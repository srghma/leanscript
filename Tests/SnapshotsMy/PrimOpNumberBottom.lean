/-! Variants of `Tests/SnapshotsPBOPure/InlineReferencePrimOpNumber.lean`.

`InlineReferencePrimOpNumber.lean` leaves out the test against `bottom` of the PureScript original
(`InlineReferencePrimOpNumber.purs`): `if res /= bottom then res else fn rec` in `localTest` and
`if res /= bottom then res else bottom` in `externTest`, where `bottom :: Number` is `-Infinity`.
This file puts it back, as `InlineReferencePrimOpInt.lean` does for `Int`.

* `if x != k then x else k` (and the other ways of writing it) is `x` for a `Float` literal `k`
  that is not a zero (`-Infinity`, `5.0`, …): `x == k` holds only when `x` has the bits of `k`
  (`Neu.condIsElse`, `Neu.eqView?`), for every float, `NaN` and `-0.0` included.
* Against a zero it stays: `-0.0 == 0.0`, so `if x == 0.0 then 0.0 else x` is not `x` on `-0.0`. -/

def fn {α : Type} (_ : α) : Float := 0.0

structure SubRec2 where
  c : Float

structure SubRec1 where
  b : SubRec2

structure Rec where
  a : SubRec1
  d : Float
  e : Float

/-- `bottom :: Number` of PureScript. -/
def bottom : Float := -(1.0 / 0.0)

@[inline]
def localTest (f : Rec → Float) : Float :=
  let r : Rec := { a := { b := { c := 99.0 } }, d := fn (), e := 11.0 }
  let res := f r
  if res != -(1.0 / 0.0) then res
  else fn r

def test1 : Float := localTest (fun rec => rec.a.b.c + rec.e)
def test2 : Float := localTest (fun rec => rec.a.b.c - rec.e)
def test3 : Float := localTest (fun rec => rec.a.b.c * rec.e)
def test4 : Float := localTest (fun rec => rec.a.b.c / rec.e)

def extern : Rec := { a := { b := { c := 99.0 } }, d := fn (), e := 11.0 }

@[inline]
def externTest (f : Rec → Float) : Float :=
  let res := f extern
  if res != -(1.0 / 0.0) then res
  else -(1.0 / 0.0)

def test5 : Float := externTest (fun rec => rec.a.b.c + rec.e)
def test6 : Float := externTest (fun rec => rec.a.b.c - rec.e)
def test7 : Float := externTest (fun rec => rec.a.b.c * rec.e)
def test8 : Float := externTest (fun rec => rec.a.b.c / rec.e)

def selNegInf (x : Float) : Float := if x == -(1.0 / 0.0) then -(1.0 / 0.0) else x
def selPosInf (x : Float) : Float := if x != 1.0 / 0.0 then x else 1.0 / 0.0
def selFive (x : Float) : Float := if x == 5.0 then 5.0 else x
def selFiveFlip (x : Float) : Float := if 5.0 == x then x else 5.0
def selNegHalf (x : Float) : Float := if x != -0.5 then x else -0.5
def selCall (f : Float → Float) (x : Float) : Float :=
  let r := f x
  if r != 2.5 then r else 2.5

/-- Against a zero: stays a conditional (`-0.0 == 0.0`). -/
def keepZero (x : Float) : Float := if x == 0.0 then 0.0 else x
/-- Not the same value: stays a conditional. -/
def keepOther (x : Float) : Float := if x == 5.0 then 6.0 else x
/-- Two unknowns: stays a conditional (either may be a zero). -/
def keepVars (x y : Float) : Float := if x == y then y else x
