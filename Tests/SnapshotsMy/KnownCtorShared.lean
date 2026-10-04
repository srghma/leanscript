/-!
Variants of `Tests/SnapshotsPBOPure/KnownConstructors04.lean`: a constructor chosen by a test,
named once, and then taken apart **several times**.
-/

/-- The payload is an argument; two `getD`s with different defaults. -/
def twoDefaults (x : Int) (s : String) : Array String :=
  let a := if x > 42 then some s else none
  #[a.getD "none" ++ "!", a.getD "?"]

/-- Two `match`es whose arms call a function. -/
def twoMatchCalls (f : String → String) (x : Int) : String :=
  let a := if x > 42 then some "Hello" else none
  let p := match a with
    | some v => f v
    | none => "empty"
  let q := match a with
    | some v => v ++ "!"
    | none => f "none"
  p ++ q

/-- Three uses. -/
def threeUses (x : Int) : Array String :=
  let a := if x > 42 then some "Hello" else none
  #[a.get! ++ "1", a.get! ++ "2", a.get! ++ "3"]

/-- Two tests choosing the constructor. -/
def nestedChoice (x : Int) : Array Int :=
  let a := if x > 42 then some 1 else if x < 0 then some 2 else none
  #[a.getD 0 + 10, a.getD 5 * 3]

/-- `Except`, taken apart twice. -/
def exceptTwice (x : Int) : String :=
  let e : Except String Int := if x > 0 then .ok x else .error "neg"
  let s := match e with
    | .ok v => toString v
    | .error m => m
  let n := match e with
    | .ok v => v
    | .error _ => 0
  s ++ toString (n + 1)

/-- A boolean payload read twice (`test3` of the original, with `||`). -/
def boolTwice (x : Int) : Bool :=
  let a := if x > 42 then some true else none
  a.get! || !(a.getD false)

/-- The option is also returned: it must still be built, once. -/
def alsoReturned (x : Int) : Option String × String :=
  let a := if x > 42 then some "Hello" else none
  (a, a.getD "" ++ "!")

/-- Each use under a different test. -/
def underTests (x y : Int) : String :=
  let a := if x > 42 then some "Hello" else none
  if y > 0 then a.getD "" ++ ", World" else a.getD "" ++ ", Universe"
