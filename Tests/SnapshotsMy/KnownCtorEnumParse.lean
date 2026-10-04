/-!
Variants of `Tests/SnapshotsPBOPure/KnownConstructors05.lean`: an enumeration parsed from a
string into an `Option`, then taken apart by a `match`.
-/

inductive Color where | Red | Green | Blue | Black
  deriving Inhabited

def parseColor : String → Option Color
  | "red" => some .Red
  | "green" => some .Green
  | "blue" => some .Blue
  | "black" => some .Black
  | _ => none

/-- A wildcard arm covers several constructors and `none`. -/
def wildcard (a : String) : Int :=
  match parseColor a with
  | some .Red => 1
  | _ => 0

/-- Two constructors share an arm. -/
def sharedArm (a : String) : Int :=
  match parseColor a with
  | some .Red | some .Green => 1
  | some .Blue => 2
  | _ => 0

/-- The arms call a function. -/
def armsCall (f : Int → Int) (a : String) : Int :=
  match parseColor a with
  | some .Red => f 1
  | some .Green => f 2
  | some .Blue => f 3
  | some .Black => f 4
  | none => 0

/-- The result feeds more code (a join point after the `match`). -/
def thenMore (f : Int → Int) (a : String) : Int :=
  let n := match parseColor a with
    | some .Red => 1
    | some .Green => 2
    | some .Blue => 3
    | some .Black => 4
    | none => 0
  f (n + 10)

def Color.code : Color → Int
  | .Red => 1 | .Green => 2 | .Blue => 3 | .Black => 4

/-- `Option.map` and `getD`. -/
def mapGetD (a : String) : Int :=
  ((parseColor a).map Color.code).getD 0

/-- `getD` of the enumeration itself. -/
def getDEnum (a : String) : Color :=
  (parseColor a).getD .Black

/-- `isSome`. -/
def isColor (a : String) : Bool :=
  (parseColor a).isSome

/-- Parsed twice, two different strings. -/
def two (a b : String) : Int :=
  match parseColor a, parseColor b with
  | some .Red, some .Red => 1
  | some _, some _ => 2
  | _, _ => 0

/-- A `match` with an arm returning a string payload. -/
def describe (a : String) : String :=
  match parseColor a with
  | some .Red => "warm"
  | some .Black => "dark"
  | some _ => "cool"
  | none => a ++ "?"

/-- Codes of `n` strings summed in a `for` loop. -/
def sumCodes (f : Nat → String) (n : Nat) : Int := Id.run do
  let mut s := 0
  for i in [0:n] do
    match parseColor (f i) with
    | some c => s := s + c.code
    | none => pure ()
  return s

/-- A `for` loop that stops at the first string that is not a color. -/
def firstBad (f : Nat → String) (n : Nat) : Nat := Id.run do
  let mut r := n
  for i in [0:n] do
    match parseColor (f i) with
    | some _ => pure ()
    | none => r := i; break
  return r

/-- A natural-number match of several literals. -/
def natSwitch (n : Nat) : String :=
  match n with
  | 0 => "zero"
  | 1 => "one"
  | 2 => "two"
  | _ => "many"
