/-!
Specializing a declaration to what a call site knows.

`describe` is an ordinary pure function of three arguments. At a call site that passes
a *literal* label, or a `none` for its last argument, the tests inside it are decided
and the string it builds is written out at the call site instead — so `describe` itself
is only emitted if some call of it knows nothing.

A `some <unknown>` is *not* such a call site any more: the `Option` here is written
unboxed (`LeanScript/Backend/OptionRepr.lean`), so what `test2` passes is the payload
itself, and there is no constructor at the call site left to specialize on.

`front1` is the same thing one step further: the character at a byte position of a
literal string is computed while compiling, so the primitive that reads it does not
appear in the generated code at all.
-/

private def describe (label : String) (n : Nat) (extra : Option String) : String :=
  match extra with
  | none => label ++ " (" ++ toString n ++ ")"
  | some s => label ++ " (" ++ toString n ++ ", " ++ s ++ ")"

/-- The label and the absence of the extra part are known: one string concatenation. -/
def test1 (n : Nat) : String := describe "count" n none

/-- The label is known and the last argument is a `some` whose field is not — which the
    unboxed representation of an `Option` leaves as an ordinary call of `describe`. -/
def test2 (n : Nat) (s : String) : String := describe "count" n (some s)

/-- Only the last argument is known here. -/
def test3 (label : String) (n : Nat) : String := describe label n none

/-- Everything is known: the whole call is the string it builds. -/
def test4 : String := describe "total" 3 (some "ok")

/-- The first character of a literal string, as a code point. -/
def test5 : Char := "hello".front

/-- The same of a string that is only known at run time. -/
def test6 (s : String) : Char := s.front
