/-!
A program made of the loops whose compiled shape the backend's *parameter elimination*
and loop rewriting are about.

`for m in messages do IO.println m` compiles, through `List.forIn'.loop`, to a
tail-recursive function of four parameters: the state token of `IO` (erased at every
call), the list, the `Unit` the loop accumulates, and the `Unit` the body answers with.
Only the list carries anything, so the emitted function takes only the list, answers
with one shared constant, and is a `while` over the list rather than a `while (true)`
that tests and `continue`s.

`countUp` is the same thing written by hand: a tail-recursive function with a parameter
nothing reads and one that never changes.

`scripts/test-programs.sh` runs the generated program under Node and requires it to
print exactly what Lean prints, so what the snapshot pins is an *optimization*, not a
change of meaning.
-/

def messages : List String := ["one", "two", "three"]

def printAll : IO Unit := do
  for m in messages do
    IO.println m

def countUp (unused : String) (step n acc : Nat) : Nat :=
  match n with
  | 0 => acc
  | n + 1 => countUp unused step n (acc + step)

def main : IO Unit := do
  printAll
  IO.println (toString (countUp "ignored" 2 5 0))
  for m in messages do
    IO.println (m ++ "!")
