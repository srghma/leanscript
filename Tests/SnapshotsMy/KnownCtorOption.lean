/-!
Variants of `Tests/SnapshotsPBOPure/KnownConstructors01.lean` where the constructor is known but
its payload or the mapped function is not known at compile time.
-/

/-- The payload is a parameter. -/
def mapConstArg (x : String) : String :=
  (some x).map (fun _ => "b") |>.getD "a"

/-- The mapped function is a parameter. -/
def mapFnArg (f : String → String) : String :=
  (some "c").map f |>.getD "a"

/-- Both unknown. -/
def mapBoth (f : String → String) (x : String) : String :=
  (some x).map f |>.getD "a"

/-- `none`: the function is never called. -/
def mapNone (f : String → String) : String :=
  (none : Option String).map f |>.getD "a"

/-- The constructor is chosen by a test. -/
def mapIf (b : Bool) (f : String → String) (x : String) : String :=
  (if b then some x else none).map f |>.getD "a"

/-- Two maps in a row. -/
def mapTwice (f g : String → String) (x : String) : String :=
  ((some x).map f |>.map g).getD "a"

/-- A bind on a known constructor. -/
def bindKnown (f : String → Option String) (x : String) : String :=
  ((some x).bind f).getD "a"

/-- `Except` instead of `Option`. -/
def exceptKnown (f : Nat → Nat) (x : Nat) : Nat :=
  match (Except.ok x : Except String Nat).map f with
  | .ok v => v
  | .error _ => 0

/-- A helper that builds the constructor, used through a function boundary. -/
@[noinline] def wrapSome (x : Nat) : Option Nat := some (x + 1)

def viaHelper (x : Nat) : Nat := (wrapSome x).getD 0

/-- A local helper, inlined. -/
private def wrap (x : Nat) : Option Nat := if x > 10 then some x else none

def viaPrivate (x : Nat) : Nat := ((wrap x).map (· * 2)).getD 7

/-- A known constructor in a loop accumulator. -/
def loopOpt (n : Nat) : Nat := Id.run do
  let mut acc : Option Nat := some 0
  for i in [0:n] do
    acc := acc.map (· + i)
  return acc.getD 0

/-- Two mutable variables: the state is a record, not a `ForInStep` around one. -/
def loopPair (n : Nat) : Nat × Nat := Id.run do
  let mut s := 0
  let mut c := 0
  for i in [0:n] do
    s := s + i
    c := c + 1
  return (s, c)

/-- A loop with `break`: its state is not always `yield`, so it is kept. -/
def loopBreak (n k : Nat) : Nat := Id.run do
  let mut r := 0
  for i in [0:n] do
    if k < i then
      r := i
      break
  return r

/-- Nested loops: both states are always `yield`. -/
def loopNested (n : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:n] do
    for j in [0:i] do
      acc := acc + j
  return acc
