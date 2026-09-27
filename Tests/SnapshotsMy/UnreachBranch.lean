/-!
A function whose `match` Lean can see is exhaustive only because of a proof: the
compiler's LCNF for it has a branch marked `.unreach`.  It is here so that the backend's
handling of such a branch is exercised by `lake test`: the branch carries no value, so
it is *dropped* rather than printed as a `throw` — every expression the backend emits is
a pure value.
-/

/-- Three cases, and the fourth is impossible because `n < 3`. -/
def small (n : Nat) (h : n < 3) : Nat :=
  match n, h with
  | 0, _ => 10
  | 1, _ => 20
  | 2, _ => 30

/-- The head of a list the caller proved non-empty: the `nil` branch is unreachable. -/
def headOf (xs : List Nat) (h : xs ≠ []) : Nat :=
  match xs, h with
  | x :: _, _ => x

/-- A use of both, so neither is dead. -/
def test (n : Nat) : Nat :=
  if h : n < 3 then small n h + headOf [n] (by simp) else 0
