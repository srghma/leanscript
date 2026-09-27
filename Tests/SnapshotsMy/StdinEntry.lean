/-!
A program that *reads*: it echoes the lines of standard input, numbered, and then
reports how many there were. Used by `scripts/test-programs.sh`, which runs it under
Node with the same input Lean is given and requires the two outputs to be equal.

`IO.getStdin` is a standard stream the backend knows, so `stdin.getLine` compiles to
the runtime's `_readLine()` with no stream object built; end of file is the empty
string, exactly as in Lean.
-/

partial def echoLines (stdin : IO.FS.Stream) (n : Nat) : IO Nat := do
  let line ← stdin.getLine
  if line.isEmpty then
    return n
  else
    IO.println s!"{n + 1}: {line.trimAsciiEnd.toString}"
    echoLines stdin (n + 1)

def main : IO Unit := do
  let stdin ← IO.getStdin
  let n ← echoLines stdin 0
  IO.println s!"{n} line(s)"
