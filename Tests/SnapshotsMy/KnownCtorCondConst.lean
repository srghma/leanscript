/-!
Variants of `test4` in `Tests/SnapshotsPBOPure/KnownConstructors.lean`: a value chosen by a test
between two constants, named once, then used **several times** as an operand of operations whose
other operands are constants (each use folds into a conditional of two constants).
-/

/-- `test4` itself: two appends, passed to an unknown function. -/
def twoAppends (f : String → String → String) (x : Int) : String :=
  let a := if x > 42 then some "Hello" else some "Default"
  match a with
  | some s => f (s ++ ", World") (s ++ ", Universe")
  | none => ""

/-- Integer arithmetic on the chosen value. -/
def intOps (f : Int → Int → Int) (x : Int) : Int :=
  let n := if x > 42 then 10 else 20
  f (n + 1) (n * 3)

/-- Three uses, one of them a comparison. -/
def threeUses (x : Int) : Array String :=
  let s := if x > 0 then "pos" else "neg"
  #[s ++ "!", "<" ++ s, if s == "pos" then "yes" else "no"]

/-- Uses in both arms of a later test. -/
def usesInArms (f : String → String) (x y : Int) : String :=
  let s := if x > 0 then "a" else "b"
  if y > 0 then f (s ++ "1") else f (s ++ "2")

/-- Also used directly: kept as one shared value. -/
def alsoDirect (f : String → String → String) (x : Int) : String :=
  let s := if x > 0 then "a" else "b"
  f s (s ++ "!")

/-- The chosen value is a natural number. -/
def natOps (f : Nat → Nat → Nat) (x : Nat) : Nat :=
  let n := if x > 5 then 7 else 9
  f (n + 2) (n - 1)
