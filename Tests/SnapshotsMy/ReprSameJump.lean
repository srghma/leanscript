/-! Variants of `Tests/SnapshotsPBOPure/KnownConstructor07.lean`: the derived `Repr` instances, whose
`Repr Int` tests the sign of each field and reads the field again in both arms. -/

structure Triple where
  a : Int
  b : Int
  c : Int
deriving Repr

structure Mixed where
  n : Nat
  i : Int
  s : String
deriving Repr

structure Nested where
  inner : Triple
  k : Int
deriving Repr

/-- `Repr Int` on its own: both arms of the sign test give the same text. -/
def fmtInt (x : Int) : Std.Format := repr x

/-- The derived instance of a structure of three `Int`s, as a string. -/
def showTriple (t : Triple) : String := toString (repr t)

/-- Nested derived instances. -/
def showNested (n : Nested) : String := toString (repr n)

/-- A structure with fields of other types. -/
def showMixed (m : Mixed) : String := toString (repr m)

/-- Both arms jump with the same value, read again from the record in each arm. -/
def sameArg (g : Int → Int) (t : Triple) (c : Bool) : Int :=
  let v := if c then t.a + t.b else t.a + t.b
  g v

/-- Not the same argument: the test stays. -/
def otherArg (g : Int → Int) (t : Triple) (c : Bool) : Int :=
  let v := if c then t.a else t.b
  g v
