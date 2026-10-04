/-! Variants of `Tests/SnapshotsPBOPure/KnownConstructors02.lean`: a `match` on a known
constructor (`some a`) whose payload is an unknown sum, and arms that read the same field. -/

/-- The original. -/
def knownSome (a : Except Int Int) : Int :=
  match some a with
  | some (Except.error b) => b
  | some (Except.ok c) => c
  | none => 42

/-- The same field, but the arms do different things with it. -/
def knownSomeDiff (a : Except Int Int) : Int :=
  match some a with
  | some (Except.error b) => b + 1
  | some (Except.ok c) => c
  | none => 42

/-- The same computation on the field in each arm. -/
def knownSomeSameOp (a : Except Int Int) : Int :=
  match some a with
  | some (Except.error b) => b * 2
  | some (Except.ok c) => c * 2
  | none => 42

/-- Two known constructors. -/
def knownPair (a : Except Int Int) (b : Option Int) : Int :=
  match (some a, b) with
  | (some (Except.error x), some y) => x + y
  | (some (Except.ok x), some y) => x + y
  | (_, none) => 0
  | (none, _) => 1

/-- `Sum` instead of `Except`. -/
def knownSum (a : Sum String String) : String :=
  match some a with
  | some (Sum.inl b) => b
  | some (Sum.inr c) => c
  | none => ""

inductive Three where
  | one (x : Nat)
  | two (x : Nat) (y : String)
  | three (x : Nat) (y : Nat)

/-- Three constructors, every arm returning the first field. -/
def threeFirst (t : Three) : Nat :=
  match some t with
  | some (.one x) => x
  | some (.two x _) => x
  | some (.three x _) => x
  | none => 0

/-- Three constructors, different fields: no merge possible. -/
def threeMixed (t : Three) : Nat :=
  match t with
  | .one x => x
  | .two x _ => x
  | .three _ y => y

/-- A known `Except.ok` around an unknown value. -/
def knownOk (x : Int) : Int :=
  match (Except.ok x : Except Int Int) with
  | .error b => b
  | .ok c => c + 1

/-- A known constructor passed through a helper that is inlined. -/
@[inline] private def wrapSome (a : Except Int Int) : Option (Except Int Int) := some a

def knownViaHelper (a : Except Int Int) : Int :=
  match wrapSome a with
  | some (Except.error b) => b
  | some (Except.ok c) => c
  | none => 42

/-- Nested known constructors. -/
def knownNested (a : Except Int Int) : Int :=
  match some (some a) with
  | some (some (Except.error b)) => b
  | some (some (Except.ok c)) => c
  | _ => 42

/-- The arms use the field, then a shared continuation. -/
def knownThenAdd (a : Except Int Int) (k : Int) : Int :=
  let v := match some a with
    | some (Except.error b) => b
    | some (Except.ok c) => c
    | none => 42
  v + k

/-- The field, then an unknown function: the call is written once. -/
def callAfter (f : Int → Int) (a : Except Int Int) : Int :=
  let v := match a with
    | .error b => b
    | .ok c => c
  f v + 1

/-- A loop whose state is rebuilt by a `match` on itself each step. -/
def countDown (n : Nat) (a : Except Int Int) : Int :=
  match n with
  | 0 => match a with | .error b => b | .ok c => c
  | n + 1 => countDown n (match a with | .error b => .ok (b + 1) | .ok c => .error (c - 1))
