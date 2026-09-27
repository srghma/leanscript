import Std.Data.HashMap

/-!
An `Option` that need not be an object (`LeanScript/Backend/OptionRepr.lean`).

`test1`–`test4` are `Option`s the analysis can account for everywhere they go: they are
built, answered with, taken apart and looked up, and nothing stores one or hands one
out. `some x` is therefore `x` itself, `none` is the runtime sentinel `_none`, and the
match is a comparison against it — no object is built and no tag is compared.

`test5` and `test6` are the fallback, in the same file: an `Option` that is stored in
an array is one the analysis cannot follow, so it keeps the object representation, and
the two representations stand side by side without being confused.
-/

/-- The first entry larger than the bound: built here, taken apart at the call. -/
private def firstBig (xs : List Nat) (bound : Nat) : Option Nat := xs.find? (· > bound)

def test1 (xs : List Nat) (bound : Nat) : Nat := (firstBig xs bound).getD 0

def test2 (xs : List Nat) (bound : Nat) : String :=
  match firstBig xs bound with
  | some n => "found " ++ toString n
  | none => "none"

/-- A lookup, whose JavaScript the backend writes itself. -/
def test3 (m : Std.HashMap String Nat) (k : String) : Nat := (m[k]?).getD 0

/-- Payloads that JavaScript considers falsy are still told apart from `none`. -/
def test4 (b : Bool) : String :=
  match (if b then some 0 else none) with
  | some n => toString n
  | none => "none"

/-- An `Option` stored in an array is one the analysis cannot follow: it stays an
    object, and so does everything its value flows to. -/
def test5 (n : Nat) : Array (Option Nat) := #[some n, none]

def test6 (n : Nat) (i : Nat) : Nat :=
  match (test5 n)[i]? with
  | some (some k) => k
  | some none => 1
  | none => 2
