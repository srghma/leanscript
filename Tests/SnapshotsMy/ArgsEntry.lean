prelude
import Init.Data.List.Basic
import Init.Data.String.Basic
import Init.System.IO

/-!
A snapshot input for the other shape of entry point Lake accepts:
`main : List String → IO UInt32`. The generated file passes the command line
arguments in and takes the exit code out, exactly as a compiled Lean program does —
so `node out.mjs a b` prints `2: a, b` and exits with status `2`.
-/

def describeArgs (args : List String) : String :=
  toString args.length ++ ": " ++ String.intercalate ", " args

def main (args : List String) : IO UInt32 := do
  IO.println (describeArgs args)
  return UInt32.ofNat (min args.length 125)
