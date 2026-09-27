/-!
A module whose declarations mention a type with **no constructors**, which the backend
refuses.

`Ty.enum` carries a proof that its constructor count is positive, so a type with no
constructors at all has no `Ty` — there is nothing to build and nothing to dispatch on,
because there is no value of it in the first place.  The front end therefore refuses
a declaration that mentions one rather than modelling it as a zero-constructor enum.
-/

/-- A type with no constructors: it has no values. -/
inductive NoValues where

/-- A function of a type that has no values.  It is total — there is no case to give —
    but it mentions `NoValues`, which the backend has no runtime representation for. -/
def fromNoValues (v : NoValues) : Nat := nomatch v

/-- An ordinary declaration, so that the module is refused for the empty type alone. -/
def bump (n : Nat) : Nat := n + 1
