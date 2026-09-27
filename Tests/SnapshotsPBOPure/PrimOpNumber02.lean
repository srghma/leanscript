-- Generic inlined test helpers comparing inlined operations against non-inlined functions
@[inline] def testAdd [BEq α] [HAdd α α α] (noInline : α → α → α) (a b expected : α) : Bool :=
  a + b == noInline a b && a + b == expected

@[inline] def testSub [BEq α] [HSub α α α] (noInline : α → α → α) (a b expected : α) : Bool :=
  a - b == noInline a b && a - b == expected

@[inline] def testEq [BEq α] (noInline : α → α → Bool) (a b : α) (expected : Bool) : Bool :=
  (a == b) == noInline a b && (a == b) == expected

@[inline] def testNe [BEq α] (noInline : α → α → Bool) (a b : α) (expected : Bool) : Bool :=
  (a != b) == noInline a b && (a != b) == expected

@[inline] def testLt [LT α] [DecidableRel (· < · : α → α → Prop)] (noInline : α → α → Bool) (a b : α) (expected : Bool) : Bool :=
  decide (a < b) == noInline a b && decide (a < b) == expected

@[inline] def testGt [LT α] [DecidableRel (· > · : α → α → Prop)] (noInline : α → α → Bool) (a b : α) (expected : Bool) : Bool :=
  decide (a > b) == noInline a b && decide (a > b) == expected

@[inline] def testLe [LE α] [DecidableRel (· ≤ · : α → α → Prop)] (noInline : α → α → Bool) (a b : α) (expected : Bool) : Bool :=
  decide (a <= b) == noInline a b && decide (a <= b) == expected

@[inline] def testGe [LE α] [DecidableRel (· ≥ · : α → α → Prop)] (noInline : α → α → Bool) (a b : α) (expected : Bool) : Bool :=
  decide (a >= b) == noInline a b && decide (a >= b) == expected

@[inline] def testMul [BEq α] [HMul α α α] (noInline : α → α → α) (a b expected : α) : Bool :=
  a * b == noInline a b && a * b == expected

@[inline] def testDiv [BEq α] [HDiv α α α] (noInline : α → α → α) (a b expected : α) : Bool :=
  a / b == noInline a b && a / b == expected

@[inline] def testNeg [BEq α] [Neg α] (noInline : α → α) (a expected : α) : Bool :=
  -a == noInline a && -a == expected

-------------------------------------------
-- TestFloat (standard 64-bit float values)
-------------------------------------------

namespace TestFloat

def nan : Float := 0.0 / 0.0

def numValues {α : Type} (op : Float → Float → α) : Array α :=
  #[ op 1.5 1.0, op 1.5 2.0, op 2.5 1.0, op 1.5 (-2.0), op (-1.5) 2.0, op (-1.5) (-1.0), op 1.0 nan ]

def test1 := numValues (fun a b => a + b)
def test2 := numValues (fun a b => a - b)
def test3 := numValues (fun a b => a == b)
def test4 := numValues (fun a b => a != b)
def test5 := numValues (fun a b => decide (a < b))
def test6 := numValues (fun a b => decide (a > b))
def test7 := numValues (fun a b => decide (a <= b))
def test8 := numValues (fun a b => decide (a >= b))
def test9 := numValues (fun a b => a * b)
def test10 := numValues (fun a b => a / b)
def test11 : Array Float := #[ -1.5, -(-1.5) ]

end TestFloat

-------------------------------------------
-- TestFloat32 (inlined vs non-inlined tests)
-------------------------------------------

namespace TestFloat32

@[inline] def nan : Float32 := 0.0 / 0.0

@[inline] def numValues {α : Type} (op : Float32 → Float32 → α) : Array α :=
  #[ op 1.5 1.0, op 1.5 2.0, op 2.5 1.0, op 1.5 (-2.0), op (-1.5) 2.0, op (-1.5) (-1.0), op 1.0 nan ]

def test1 := numValues (fun a b => a + b)
def test2 := numValues (fun a b => a - b)
def test3 := numValues (fun a b => a == b)
def test4 := numValues (fun a b => a != b)
def test5 := numValues (fun a b => decide (a < b))
def test6 := numValues (fun a b => decide (a > b))
def test7 := numValues (fun a b => decide (a <= b))
def test8 := numValues (fun a b => decide (a >= b))
def test9 := numValues (fun a b => a * b)
def test10 := numValues (fun a b => a / b)
def test11 : Array Float32 := #[ -1.5, -(-1.5) ]

@[noinline] def addNoInline (a b : Float32) : Float32 := a + b
@[noinline] def subNoInline (a b : Float32) : Float32 := a - b
@[noinline] def eqNoInline  (a b : Float32) : Bool    := a == b
@[noinline] def neNoInline  (a b : Float32) : Bool    := a != b
@[noinline] def ltNoInline  (a b : Float32) : Bool    := decide (a < b)
@[noinline] def gtNoInline  (a b : Float32) : Bool    := decide (a > b)
@[noinline] def leNoInline  (a b : Float32) : Bool    := decide (a <= b)
@[noinline] def geNoInline  (a b : Float32) : Bool    := decide (a >= b)
@[noinline] def mulNoInline (a b : Float32) : Float32 := a * b
@[noinline] def divNoInline (a b : Float32) : Float32 := a / b
@[noinline] def negNoInline (a : Float32)   : Float32 := -a

def test1__shouldBeTrue := test1 == numValues addNoInline
def test2__shouldBeTrue := test2 == numValues subNoInline
def test3__shouldBeTrue := test3
def test4__shouldBeTrue := test4
def test5__shouldBeTrue := test5
def test6__shouldBeTrue := test6
def test7__shouldBeTrue := test7
def test8__shouldBeTrue := test8
def test9__shouldBeTrue := test9
def test10__shouldBeTrue := test10

end TestFloat32
