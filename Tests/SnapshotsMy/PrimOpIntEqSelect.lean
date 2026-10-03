/-! Variants of `Tests/SnapshotsPBOPure/InlineReferencePrimOpInt.lean`.

* `if x != k then x else k` (and the other ways of writing it) is `x`, whatever `x` is: when the
  test holds the two arms are equal (`Neu.condIsElse`, `Neu.eqView?`).  Only for the equalities
  of `Int`, `Nat`, `String` and the fixed-width integers: the equality of `Float` is not the
  equality of the values (`0.0 == -0.0`), so `if x == 0.0 then 0.0 else x` stays.
* A record constant read in the body of a function after it: the function reads the constant
  (`f(extern)`), as purescript-backend-optimizer writes it, instead of building the record again
  (`shareConstValues`, `JsExpr.isFrozen`).  An array is never shared so: a function may update
  in place an array it owns. -/

def selInt (x : Int) : Int := if x != -2147483648 then x else -2147483648
def selIntEq (x : Int) : Int := if x == 5 then 5 else x
def selIntFlip (x : Int) : Int := if 5 == x then x else 5
def selIntVars (x y : Int) : Int := if x == y then y else x
def selNat (n : Nat) : Nat := if n = 3 then 3 else n
def selString (s : String) : String := if s == "a" then "a" else s
def selUInt8 (x : UInt8) : UInt8 := if x == 7 then 7 else x
def selInt32 (x : Int32) : Int32 := if x != 0 then x else 0
def selCall (f : Int → Int) (x : Int) : Int :=
  let r := f x
  if r != 0 then r else 0

/-- Not the same value: stays a conditional. -/
def keepOther (x : Int) : Int := if x == 5 then 6 else x
/-- The equality of `Float` is not that of the values: stays a conditional. -/
def keepFloat (x : Float) : Float := if x == 0.0 then 0.0 else x

structure Pt where
  x : Int
  y : Int

def origin : Pt := { x := 3, y := 4 }

def applyOrigin (f : Pt → Int) : Int := f { x := 3, y := 4 }
def originSum (k : Int) : Int := (fun (p : Pt) => p.x * k + p.y) { x := 3, y := 4 }

def arr : Array Int := #[1, 2, 3]

/-- An array is never shared with a constant inside a function. -/
def applyArr (f : Array Int → Int) : Int := f #[1, 2, 3]
