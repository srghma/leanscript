/-!
Variants of `Tests/SnapshotsPBOPure/KnownConstructors03.lean`: a constructor chosen by a test
(or a `match`) and then taken apart right away ("case of case").
-/

/-- The original, but the continuation reads the payload twice. -/
def twiceUse (x : Int) : String :=
  let a := if x > 42 then some "Hello" else none
  match a with
  | some str => str ++ str
  | none => ""

/-- The payload is not a literal. -/
def payloadArg (x : Int) (s : String) : String :=
  let a := if x > 42 then some s else none
  match a with
  | some str => str ++ ", World!"
  | none => ""

/-- Three arms producing the option, two of them `some`. -/
def threeArms (x : Int) (s t : String) : String :=
  let a := if x > 42 then some s else if x < 0 then some t else none
  match a with
  | some str => str ++ ", World!"
  | none => ""

/-- A big continuation shared by two `some` arms (it must not be copied). -/
def bigShared (x : Int) (s t : String) (f : String → String) : String :=
  let a := if x > 42 then some s else if x < 0 then some t else none
  match a with
  | some str => f (f (f (str ++ ", World!")))
  | none => ""

/-- The option comes from a `match` on a `Nat`. -/
def fromMatch (n : Nat) : Nat :=
  let a : Option Nat := match n with
    | 0 => none
    | 1 => some 10
    | k + 2 => some k
  match a with
  | some v => v + 1
  | none => 0

/-- `Except` chosen by a test, then taken apart. -/
def exceptIf (x : Int) : Int :=
  let r : Except String Int := if x > 0 then .ok x else .error "neg"
  match r with
  | .ok v => v * 2
  | .error _ => -1

/-- `Option` do-notation: two binds on options chosen by tests. -/
def doChain (x y : Int) : Int :=
  let r : Option Int := do
    let a ← if x > 0 then some x else none
    let b ← if y > 0 then some y else none
    pure (a + b)
  r.getD 0

/-- A private helper returning an option, inlined. -/
private def safeDiv (a b : Int) : Option Int := if b == 0 then none else some (a / b)

def viaSafeDiv (a b : Int) : Int :=
  match safeDiv a b with
  | some q => q + 1
  | none => 0

/-- Two private helpers chained. -/
def safeDivTwice (a b c : Int) : Int :=
  match safeDiv a b with
  | some q => match safeDiv q c with
    | some r => r
    | none => -2
  | none => -1

/-- A `Bool` chosen by a test, then tested again. -/
def boolTwice (x : Int) : String :=
  let b := if x > 42 then true else false
  if b then "big" else "small"

/-- A pair of options. -/
def pairOpt (x : Int) : Int :=
  let p : Option Int × Option Int := if x > 0 then (some x, none) else (none, some (-x))
  match p with
  | (some a, _) => a
  | (_, some b) => b
  | _ => 0

/-- The known constructor is used after an unrelated call. -/
def afterCall (f : Int → Int) (x : Int) : Int :=
  let a := if f x > 0 then some (f x) else none
  match a with
  | some v => v
  | none => 0

/-- `Except` do-notation: two checks, then the sum. -/
def exceptChain (x y : Int) : Except String Int := do
  let a ← if x > 0 then pure x else throw "x"
  let b ← if y > 0 then pure y else throw "y"
  pure (a + b)

/-- The same, taken apart right away. -/
def exceptChainGet (x y : Int) : Int :=
  match exceptChain x y with
  | .ok v => v
  | .error _ => 0

/-- `<|>` on options chosen by tests. -/
def orElseIf (x : Int) : Int :=
  ((if x > 10 then some x else none) <|> (if x < -10 then some (-x) else none)).getD 0

/-- `if let` on an option chosen by a test. -/
def ifLet (x : Int) (s : String) : String :=
  if let some v := (if x > 0 then some s else none) then v ++ "!" else "?"

/-- `isSome` of an option chosen by a test. -/
def isSomeIf (x : Int) : Bool :=
  (if x > 0 then some x else none).isSome

/-- The option is used twice. -/
def usedTwice (x : Int) : Int :=
  let a := if x > 0 then some x else none
  a.getD 0 + (a.map (· * 2)).getD 1

/-- A `Bool × Int` pair chosen by a test, then tested. -/
def pairBool (x : Int) : Int :=
  let (ok, v) := if x > 0 then (true, x) else (false, 0)
  if ok then v * 3 else -1
