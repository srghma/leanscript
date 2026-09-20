prelude
import Init.Data.Nat.Gcd
import Init.System.IO

def gcd2 (a b : Nat) : Nat := Nat.gcd a b

def run : Nat := gcd2 48 18

-- `main` is an IO action, which the backend refuses; see the note above.
-- def main : IO Unit := IO.println run
