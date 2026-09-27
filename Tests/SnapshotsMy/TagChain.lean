/-!
Chains of constructor tests (`LeanScript.KnownTests`).

A pattern match compiles to a chain of tests, and the last alternative of one match
needs no test of its own. What a *nested* match on the same value leaves behind is a
test the chain above it has already settled: the constructor was ruled out on the way
here, or every other constructor of the type was, and the schema says a value carries
one of them. Such a test is not written, and neither is the branch under it.
-/

inductive Colour where
  | red | green | blue
  deriving Inhabited

/-- The inner match asks for `red` again, which the outer one has ruled out: the
    branch under it is unreachable. A constructor that carries nothing is a number,
    so the tests here are `x === 0`, and what settles the second one is that a value
    is not two different numbers. -/
def test1 (c : Colour) (n : Nat) : Nat :=
  match c with
  | .red => n
  | _ => match c with
         | .red => 0
         | .green => n + 1
         | .blue => n + 2

inductive Shape where
  | dot
  | circle (r : Nat)
  | rect (w h : Nat)

/-- The same, on a type whose constructors carry fields and are therefore tagged
    objects: the test the inner match repeats is `x.tag === "Shape$dot"`. -/
def test2 (s : Shape) (n : Nat) : Nat :=
  match s with
  | .dot => n
  | _ => match s with
         | .dot => 0
         | .circle r => r + n
         | .rect w h => w + h + n

/-- A match inside the branch of another one that asks for a constructor the branch
    has already excluded. -/
def test3 (s : Shape) : Nat :=
  match s with
  | .dot => 0
  | .circle r => match s with
                 | .rect w _ => w
                 | _ => r
  | .rect w h => w + h

/-- An ordinary exhaustive match, which was already one test short of the number of
    constructors: the last alternative is the fall-through of the chain. -/
def test4 : List Nat → String
  | []          => "empty"
  | [x]         => s!"one {x}"
  | _ :: _ :: _ => "many"
