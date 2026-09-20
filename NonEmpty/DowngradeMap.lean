module

@[expose] public section

namespace NonEmpty

/--
A minimal "downgraded" version of `Functor.map` for non-empty container types.

Unlike `Functor`, this class does not require the container to live in a fixed
universe pair beyond `Type u → Type u`, and it carries no laws; it merely records
that the container supports mapping a function over its elements. It is used to
share the mapping API between the various non-empty container implementations
(`NonEmptyList`, `NonEmptyArray`, ...).
-/
class DowngradeMap (f : Type u → Type u) where
  /-- Map a function over every element of the container. -/
  map : {α β : Type u} → (α → β) → f α → f β

end NonEmpty
