prelude
import Init.Data.Nat.Gcd

/-!
A snapshot input whose `main` is **not** an entry point: `Nat` is not one of the types
Lake accepts for `main`, so asking for a program out of this module has to fail rather
than emit a file that runs `main` and prints nothing.

Lean itself rejects a `main` of the wrong type as soon as it compiles one, which is
why `main` is `noncomputable` here: that is what lets the module exist at all, and it
leaves the check to the JavaScript backend, which is what this input is for.

The declaration `run` is here for the same reason: naming *it* as the entry point
instead of `main` is not something the compiler can be asked to do, because a program
always runs `main`, exactly as one built by `lake` does.
-/

def gcd2 (a b : Nat) : Nat := Nat.gcd a b

def run : Nat := gcd2 48 18

noncomputable def main : Nat := run
