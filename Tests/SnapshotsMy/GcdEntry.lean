-- @js_export: Nat.gcd, gcd2, run
prelude
import Init.Data.Nat.Gcd
import Init.System.IO

/-!
A snapshot input whose recursion is `Nat.gcd`: Lean proves it terminating by
well-founded recursion, and its recursive call is a tail call, so the backend has to
compile it to a `while` loop rather than to a recursive JavaScript function.

`main` below is commented out on purpose. A `Term` is pure — every sub-expression is a
value, so an optimiser may reorder, duplicate or drop it — and `IO.println` is none of
those things: it cannot be reordered. The backend therefore has no way to compile an IO
entry point, and refuses one (`SnapshotsMy/IoEntry.lean` is the snapshot that checks the
refusal). What is left here is the pure part, which does compile.
-/

def gcd2 (a b : Nat) : Nat := Nat.gcd a b

def run : Nat := gcd2 48 18

-- `main` is an IO action, which the backend refuses; see the note above.
-- def main : IO Unit := IO.println run
