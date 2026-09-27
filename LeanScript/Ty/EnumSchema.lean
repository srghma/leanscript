module

public import Init

@[expose] public section

namespace LeanScript

/-!
# Enums

`LeanEnumSchema`, the leaf type of a sum of at least three constructors none of which has
a field.
-/

/-- The payload of an **enum**: a sum whose constructors all have no fields, printed as
    the plain numbers `shift`, `shift + 1`, ….

    The number of constructors is held as `extraConstructors`, the number *beyond the
    three an enum must have*, so an enum of fewer than three constructors is
    unwritable: a type of no or one value has no type in the language, and a type of two
    values is `bool`.  `shift` is an arbitrary `Int`, which is what unites
    an ordinary enum (`shift = 0`) with the ones whose numbering Lean fixes (`Ordering`
    is three constructors at `shift = -1`, printing as `-1 | 0 | 1`). -/
structure LeanEnumSchema where
  /-- How many constructors the enum has **beyond** the three it has at minimum. -/
  extraConstructors : Nat := 0
  /-- The number the first constructor prints as. -/
  shift : Int := 0
  deriving DecidableEq, Repr, Inhabited, BEq, ReflBEq, LawfulBEq

namespace LeanEnumSchema

/-- How many constructors the enum has: at least three. -/
def nOfConstructors (s : LeanEnumSchema) : Nat := s.extraConstructors + 3

theorem three_le_nOfConstructors (s : LeanEnumSchema) : 3 ≤ s.nOfConstructors := by
  simp only [nOfConstructors]
  omega

/-- An enum has at least three constructors, so it has at least one: a constructor of it
    can be written as a plain numeral, `(2 : Fin s.nOfConstructors)`. -/
instance instNeZeroNOfConstructors (s : LeanEnumSchema) : NeZero s.nOfConstructors :=
  ⟨by simp only [nOfConstructors]; omega⟩

/-- The enum with this many constructors, if that is a number of constructors an enum
    can have. -/
def ofCount? (n : Nat) (shift : Int) : Option LeanEnumSchema :=
  if 3 ≤ n then some ⟨n - 3, shift⟩ else none

@[simp] theorem ofCount?_nOfConstructors (s : LeanEnumSchema) :
    ofCount? s.nOfConstructors s.shift = some s := by
  cases s with
  | mk e sh =>
    simp [ofCount?, nOfConstructors]

theorem nOfConstructors_ofCount? {n : Nat} {shift : Int} {s : LeanEnumSchema}
    (h : ofCount? n shift = some s) : s.nOfConstructors = n ∧ s.shift = shift := by
  unfold ofCount? at h
  split at h
  · next hn => cases h; simp [nOfConstructors]; omega
  · simp at h

end LeanEnumSchema

end LeanScript

end
