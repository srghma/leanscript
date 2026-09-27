/-!
A program whose *writes* are what the compiled form is about
(`LeanScript/EffectPasses.lean`).

Adjacent writes of the same standard stream are one write in the generated code:
`IO.println "one"; IO.println "two"; IO.println "three"` is a single
`console.log("one\ntwo\nthree")` — one write to the file descriptor instead of three.

Three things must stop the merging, and each of them appears below:

* a write of the **other** stream in between (merging across it would change how the
  two outputs interleave);
* an **action** in between — here a mutable reference that is updated between two
  writes;
* a text whose computation may itself **do** something.

A *read* between two writes does not stop it: nothing this language can do observes
what has been written, so putting the first write off until the second one is the same
program (`delayStreamWrite`), and the two are still one write.

`scripts/test-programs.sh` runs the generated program under Node and requires its
standard output *and* its standard error to be byte for byte what Lean itself prints,
so what the snapshot pins is an optimization and not a change of meaning.
-/

def literalRun : IO Unit := do
  IO.println "one"
  IO.println "two"
  IO.println "three"

def interleaved : IO Unit := do
  IO.println "out 1"
  IO.eprintln "err 1"
  IO.println "out 2"

def aroundAnAction (r : IO.Ref Nat) : IO Unit := do
  IO.println "before"
  r.modify (· + 1)
  IO.println (toString (← r.get))
  IO.println "after"

def main : IO Unit := do
  literalRun
  interleaved
  let r ← IO.mkRef 41
  aroundAnAction r
  IO.print "no"
  IO.print "newline"
  IO.println "!"
