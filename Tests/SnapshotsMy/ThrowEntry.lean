/-!
A program that *fails*. It first prints how Lean describes a few `IO.Error`s, and then
throws one that nothing catches.

Lean reports an uncaught error on standard error as `uncaught exception: <message>`,
the message being `IO.Error.toString` of it, and exits with status 1. The generated
program has to do the same — which is what `scripts/test-programs.sh` checks, by
running this program under Node and comparing both of its output streams and its exit
status with Lean's own.
-/

def errors : List IO.Error :=
  [ IO.userError "something went wrong",
    IO.Error.otherError 7 "Bad thing",
    IO.Error.noFileOrDirectory "data.txt" 2 "open failed",
    IO.Error.invalidArgument (some "read") 22 "Not a number",
    IO.Error.unexpectedEof ]

def main : IO Unit := do
  for e in errors do
    IO.println (toString e)
  throw (IO.userError s!"boom {1 + 1}")
