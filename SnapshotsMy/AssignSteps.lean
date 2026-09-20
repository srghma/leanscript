/-!
The step of a loop the backend makes out of a tail call: the assignments are written
one after another, and a value that is *in the way* — one that a later assignment's
target still has to be read for — is bound to a `const` first
(`LakeJs.Backend.Analysis.assignStep`, `assignWithTemps`). No iteration builds the
array a destructuring assignment `[a, b] = [b, a]` would.
-/

/-- The parameters are permuted: the step needs one temporary. -/
def test1 (fuel a b : Nat) : Nat :=
  match fuel with
  | 0 => a
  | fuel + 1 => if b == 0 then a else test1 fuel b (a % b)

/-- A three-way rotation: two of the three values are in the way. -/
def test2 (fuel a b c : Nat) : Nat :=
  match fuel with
  | 0 => a * 100 + b * 10 + c
  | fuel + 1 => test2 fuel b c (a + 1)

/-- The values are calls, so they may not be reordered; they are bound in the order
    the call evaluates them in and the variables are assigned afterwards. -/
def test3 (fuel a b : Nat) : Nat :=
  match fuel with
  | 0 => a * 1000 + b
  | fuel + 1 => test3 fuel (Nat.gcd b (a + 7)) (Nat.gcd a (b + 3))

/-- Nothing is in the way here: every assignment can be written where it stands. -/
def test4 (fuel a b : Nat) : Nat :=
  match fuel with
  | 0 => a + b
  | fuel + 1 => test4 fuel (a + 1) (b + 2)
