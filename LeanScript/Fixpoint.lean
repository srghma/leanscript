module

@[expose] public section

namespace LeanScript

/-- One layer of a declaration that recurses on its own: an occurrence of the
    declaration, or a shape `f` of the type language.  `self` carries no number —
    there is only one declaration in scope to point at. -/
inductive WithSelf (f : Type) where
  /-- An occurrence of the declaration being defined. -/
  | self
  /-- A shape of the type language, which is not an occurrence of the declaration. -/
  | pure : f → WithSelf f
  deriving DecidableEq, Repr, Inhabited

/-- One layer of a member of a mutual family of `familySize` declarations: an occurrence
    of one of the members — `Fin familySize`, so never a member the family does not
    have — or a shape `f` of the type language. -/
inductive WithRefToMutualDatatype (familySize : Nat) (f : Type) where
  /-- An occurrence of member `i` of the family this body belongs to. -/
  | refToFamilyMember : Fin familySize → WithRefToMutualDatatype familySize f
  /-- A shape of the type language, which is not an occurrence of a member. -/
  | pure : f → WithRefToMutualDatatype familySize f
  deriving DecidableEq, Repr

namespace WithSelf

/-- Rebuild a layer with its shape mapped. -/
def map (g : α → β) : WithSelf α → WithSelf β
  | .self => .self
  | .pure a => .pure (g a)

/-- The shape of a layer, if it is not an occurrence of the declaration. -/
def shape? : WithSelf α → Option α
  | .self => none
  | .pure a => some a

@[simp] theorem map_self (g : α → β) : map g (.self) = .self := rfl
@[simp] theorem map_pure (g : α → β) (a : α) : map g (.pure a) = .pure (g a) := rfl

end WithSelf

namespace WithRefToMutualDatatype

/-- Rebuild a layer with its shape mapped. -/
def map (g : α → β) : WithRefToMutualDatatype n α → WithRefToMutualDatatype n β
  | .refToFamilyMember i => .refToFamilyMember i
  | .pure a => .pure (g a)

/-- The shape of a layer, if it is not an occurrence of a member. -/
def shape? : WithRefToMutualDatatype n α → Option α
  | .refToFamilyMember _ => none
  | .pure a => some a

/-- Which member of the family this layer is an occurrence of, if it is one. -/
def member? : WithRefToMutualDatatype n α → Option (Fin n)
  | .refToFamilyMember i => some i
  | .pure _ => none

@[simp] theorem map_refToFamilyMember (g : α → β) (i : Fin n) :
    map g (.refToFamilyMember i) = .refToFamilyMember (f := β) i := rfl
@[simp] theorem map_pure (g : α → β) (a : α) :
    map (n := n) g (.pure a) = .pure (g a) := rfl

end WithRefToMutualDatatype

end LeanScript

end
