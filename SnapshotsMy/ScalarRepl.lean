/-!
Scalar replacement of a constructor a helper is only ever handed
(`LakeJs.Backend.ScalarRepl`): a parameter every caller builds for the call and that
the callee only projects becomes that constructor's *fields*, so nothing is allocated
at the call and nothing is loaded out of it in the loop. What is left is then finished
by the parameter plan (`LakeJs.Backend.ParamElim`): a field nothing reads goes, and one
every caller passes the same literal in becomes that literal.

The cases that must *not* be split are here too: a value the callee answers with, one
that is handed on to something the analysis cannot see through, and a parameter whose
callers do not agree on one constructor.
-/

/-- A counted loop: the `Std.Range` is built at the call and only projected in the
    loop, so the loop takes its fields — and its step is `1`. -/
def test1 (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:n] do
    s := s + i
  return s

/-- Two loops, one inside the other. -/
def test2 (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:n] do
    for j in [0:i] do
      s := s + j
  return s

/-- A helper that only takes its argument apart: the pair is not built. -/
@[noinline] private def dist (p : Nat × Nat) : Nat :=
  if p.1 < p.2 then p.2 - p.1 else p.1 - p.2

def test3 (a b : Nat) : Nat := dist (a, b) + dist (b, a + 1)

/-- A helper that answers *with* what it is given: the pair escapes, so it stays a
    pair. -/
@[noinline] private def bigger (p : Nat × Nat) : Nat × Nat :=
  if p.1 < p.2 then p else (p.2, p.1)

def test4 (a b : Nat) : Nat × Nat := bigger (a, b)

/-- A helper whose callers do not agree on one constructor: it is handed a `some` at
    one call site and a `none` at another, so its parameter stays what it is. -/
@[noinline] private def sumOpt (o : Option (Nat × Nat)) : Nat :=
  match o with
  | some (a, b) => a + b
  | none => 0

def test5 (a b : Nat) : Nat := sumOpt (some (a, b)) + sumOpt none

/-- A recursion that carries a structure it only reads: the fields travel through the
    recursive call instead of the object. -/
private structure Bounds where
  lo : Nat
  hi : Nat

@[noinline] private def clampSum (b : Bounds) : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => clampSum b n (acc + (if n < b.lo then b.lo else if b.hi < n then b.hi else n))

def test6 (n : Nat) : Nat := clampSum ⟨n % 3, n % 7 + 3⟩ n 0
