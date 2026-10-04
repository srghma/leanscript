/-!
Variants of `Tests/SnapshotsPBOPure/KnownConstructors06.lean` (the `Repr` instance that
`deriving Repr` writes for an enumeration): a `match` on an enumeration whose arms compute the
same expression, except for one literal.  The arms are written once, in a join point that the
`match` jumps to with the literal (`Term.factorWalk`, `LeanScript/Term/Optimize/FactorArms.lean`).
-/

inductive Color where | Red | Green | Blue | Black
  deriving Repr, Inhabited

/-- The name in a pair: the pair is built once. -/
def label (c : Color) (n : Nat) : String × Nat :=
  match c with
  | .Red => ("red", n + 1)
  | .Green => ("green", n + 1)
  | .Blue => ("blue", n + 1)
  | .Black => ("black", n + 1)

/-- The name in a string append. -/
def wrap (c : Color) (s : String) : String :=
  match c with
  | .Red => "<" ++ "red" ++ s ++ ">"
  | .Green => "<" ++ "green" ++ s ++ ">"
  | .Blue => "<" ++ "blue" ++ s ++ ">"
  | .Black => "<" ++ "black" ++ s ++ ">"

/-- The name twice in each arm. -/
def twice (c : Color) (s : String) : String × String :=
  match c with
  | .Red => ("red", "red" ++ s)
  | .Green => ("green", "green" ++ s)
  | .Blue => ("blue", "blue" ++ s)
  | .Black => ("black", "black" ++ s)

/-- As `Repr.addAppParen`: a test inside each arm, the name in both of its arms. -/
def paren (c : Color) (prec : Nat) : String × Nat :=
  match c with
  | .Red => if prec ≥ 1024 then ("(red)", if prec ≥ 1024 then 1 else 2) else ("red", if prec ≥ 1024 then 1 else 2)
  | .Green => if prec ≥ 1024 then ("(green)", if prec ≥ 1024 then 1 else 2) else ("green", if prec ≥ 1024 then 1 else 2)
  | .Blue => if prec ≥ 1024 then ("(blue)", if prec ≥ 1024 then 1 else 2) else ("blue", if prec ≥ 1024 then 1 else 2)
  | .Black => if prec ≥ 1024 then ("(black)", if prec ≥ 1024 then 1 else 2) else ("black", if prec ≥ 1024 then 1 else 2)

/-- Two literals differ in each arm: the arms are kept. -/
def twoLits (c : Color) (n : Nat) : String × Nat × Nat :=
  match c with
  | .Red => ("red", 1, n * 3)
  | .Green => ("green", 2, n * 3)
  | .Blue => ("blue", 3, n * 3)
  | .Black => ("black", 4, n * 3)

/-- A number differs, the same string in every arm. -/
def codeOf (c : Color) (s : String) : Nat × String × String :=
  match c with
  | .Red => (10, s ++ "!", "color")
  | .Green => (20, s ++ "!", "color")
  | .Blue => (30, s ++ "!", "color")
  | .Black => (40, s ++ "!", "color")

/-- One arm has another shape: the arms are kept. -/
def oneOther (c : Color) (n : Nat) : String × Nat :=
  match c with
  | .Red => ("red", n + 1)
  | .Green => ("green", n + 1)
  | .Blue => ("blue", n + 2)
  | .Black => ("black", n + 1)

/-- Only the literal: the arms are kept (a join point would not be shorter). -/
def nameOf (c : Color) : String :=
  match c with
  | .Red => "red"
  | .Green => "green"
  | .Blue => "blue"
  | .Black => "black"

/-- A wildcard arm: still one literal per constructor. -/
def wildcard (c : Color) (n : Nat) : String × Nat :=
  match c with
  | .Red => ("red", n * n)
  | _ => ("other", n * n)

/-- A boolean literal. -/
def isRed (c : Color) (n : Int) : Bool × Int :=
  match c with
  | .Red => (true, n - 7)
  | .Green => (false, n - 7)
  | .Blue => (false, n - 7)
  | .Black => (false, n - 7)

/-- The `Repr` instance, written to a string. -/
def reprString (c : Color) (prec : Nat) : String :=
  Std.Format.pretty (reprPrec c prec)
