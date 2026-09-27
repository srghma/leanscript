/-!
A program whose `main` is full of *effects*, used by `scripts/test-programs.sh`: the
JavaScript it compiles to is run under Node and required to print exactly what Lean
itself prints, on stdout as well as on stderr.

Effects are the part of a program a compiler must not treat like a value. An
`IO.Ref.modify` in a loop produces `Unit`, which nothing reads, so a translation that
drops bindings whose result is unused silently deletes the whole loop; an action whose
result is used once must not be moved to the place of that use, since that changes the
order the effects happen in. Each block below pins one such case down.
-/

/-- Sums `0 + 1 + ⋯ + 4` in a reference. Every `modify` returns `Unit`, so the loop is
    only observable through the reference: the result of the actions is never read. -/
def sumInRef : IO Nat := do
  let r ← IO.mkRef (0 : Nat)
  for i in [0:5] do r.modify (· + i)
  r.get

/-- Two actions whose results *are* used, but in the opposite order to the one they run
    in: the value of the first is printed after the second one has run. -/
def orderOfEffects (log : IO.Ref (Array String)) : IO String := do
  let a ← (do log.modify (·.push "first"); pure "a")
  let b ← (do log.modify (·.push "second"); pure "b")
  pure s!"{b}{a}"

/-- Throws when its argument is large, and reports the message it catches. -/
def guardSmall (n : Nat) : IO String :=
  try
    if n > 3 then throw (IO.userError s!"boom {n}") else pure s!"small {n}"
  catch e => pure s!"caught: {e}"

def main : IO Unit := do
  let n ← sumInRef
  IO.println s!"ref = {n}"

  let log ← IO.mkRef (#[] : Array String)
  IO.println (← orderOfEffects log)
  IO.println s!"log = {← log.get}"

  IO.println (← guardSmall n)
  IO.println (← guardSmall 1)

  -- an action run only for its effect, with its result explicitly thrown away
  discard <| guardSmall 9
  let _ ← log.swap #[]
  IO.println s!"log after swap = {← log.get}"

  -- a reference holding a structured value, updated through `modifyGet`
  let acc ← IO.mkRef ([] : List Nat)
  for i in [1:4] do
    let len ← acc.modifyGet fun xs => (xs.length, i :: xs)
    IO.println s!"length before push {i} = {len}"
  IO.println (toString (← acc.get))

  IO.eprintln "to stderr"
  IO.println (toString [1, 2, 3])
