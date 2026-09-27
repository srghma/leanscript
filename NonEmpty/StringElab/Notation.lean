module

public import NonEmpty.String.Basic
meta import NonEmpty.String.Basic

@[expose] public section

/-!
The literal notation `nes!"…"` for `NonEmptyString`: a non-empty string literal, whose
non-emptiness is checked by `decide`.
-/

namespace NonEmpty.String

macro "nes!" s:str : term => do
  let strVal := s.getString
  if strVal.isEmpty then
    Lean.Macro.throwErrorAt s "String literal cannot be empty for nes!"
  else
    ``( (NonEmptyString.mk $s (by decide) : NonEmptyString) )

#guard (nes!"world").toString == "world"
#guard (nes!"11" < nes!"112")
#guard if (nes!"112" < nes!"11") then true else true

#guard nes!"11" ≤ nes!"112"
#guard nes!"11" ≤ nes!"11"
#guard nes!"112" > nes!"11"
#guard nes!"112" ≥ nes!"11"
#guard nes!"11" == nes!"11"
#guard nes!"11" != nes!"12"

end NonEmpty.String
