module

public import NonEmpty.String.Basic
public import NonEmpty.ListCorrectByConstruction.Basic

@[expose] public section

namespace NonEmpty.String

open NonEmpty.ListCorrectByConstruction

def intercalateListCBC (s : String) (xs : NonEmptyList NonEmptyString) : NonEmptyString :=
  xs.tail.foldl (fun acc x => acc ++ s ++ x) xs.head
