/-!
A snapshot input for a `main` that turns the command line arguments into an `Array`
and works with that only. The `List String` the entry point is given is built by
`_argv()` and taken apart again by `List.toArray`, so neither is needed: the generated
program passes the arguments as the array they already are (`_argvArray()`).
-/

def main (args : List String) : IO UInt32 := do
  let argsA := args.toArray
  IO.println s!"{argsA.size} argument(s)"
  for a in argsA do
    IO.println a
  return UInt32.ofNat (min argsA.size 125)
