module

public import LeanScript.Ty.Schema.Family

@[expose] public section

namespace LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-!
# The schemas: the shapes a user-defined type can have, *parametrised by a type language*

This module holds the shapes a declaration of a source language can have — a record, a
tagged union, a recursive newtype, a mutual family — **without** committing to what a
field's type is.  Every schema takes the type language as a parameter `α`, so the same
schema serves `LeanScript.Ty` (the JavaScript backend's type language), the layer inside a
whatever further language a later backend adds: a schema says how many fields or
constructors a shape has, and says nothing about what a field's type is.

## The invariants are in the types, not in a side condition

Every schema here is *correct by construction* for the counting conditions — the ones
that say a shape is the shape it claims to be rather than a degenerate one:

| schema                      | what is impossible to write                           |
| :-------------------------- | :---------------------------------------------------- |
| `LeanEnumSchema`            | fewer than **three** constructors                      |
| `LeanRecordSchema α`        | fewer than **two** fields                              |
| `LeanTaggedUnionSchema α`   | fewer than two constructors, or no constructor with a field |
| `LeanFamMemberSchema α`     | a member that is none of those three shapes            |
| `LeanMutualRecFamily α`     | fewer than two members, or a member number out of range |

Why three constructors for an enum?  Because the two smaller enums are **not** modelled
as enums at all:

* no constructor is an `Empty`-like type: it has no values, so no compiled declaration
  mentions it;
* one constructor is a `Unit`-like type: its single value carries no information and is
  erased before a type is built;
* two constructors is a `Bool`-like type, and the backend models those as `Bool`
  (`LeanPrimTy.bool`), so that the JavaScript is `true`/`false` rather than `0`/`1`.

So `Ty` (and any other language built on these schemas) cannot express an empty type, a
unit type, or a second boolean — which is what makes the erasure and the boolean
modelling decisions of the backend *decisions of the type language* rather than
conventions the translation has to keep to.

## What is **not** here

Three conditions are about a whole type rather than about one shape's payload, so they
cannot be fields of a schema — they mention the type language, which is a parameter:

* a recursive shape **mentions itself** (`Ty.self`);
* an occurrence names a member the scope in fact has.

They are stated about a whole tree, as the inductive proposition `LeanScript.Ty.Wf`
(`LeanScript.Ty.Wf`), and a `LeanScript.LeanScriptTyWf` instance carries a proof of it
beside its tree.

## Canonical encodings

A schema is a *representation* of a list, not a list plus a proof, and the
representation is chosen so that each admissible list has exactly **one** encoding.
That is what makes the derived equality of a schema the equality of the list it
denotes: `toList` is injective, and `ofList?` is its partial inverse
(`toList_ofList?`, `ofList?_toList`, in `LeanScript.Ty.Schema.Containers` and
`LeanScript.Ty.Schema.Sum`).  A subtype `{ xs : List α // P xs }` would
do the same job, but it cannot be nested inside an `inductive` the way these can, which
is the whole point: `Ty.record` takes a `LeanRecordSchema Ty`, so the invariant is
carried by the type of the constructor's argument.
-/

/-! ## Every schema is a lawful functor

`map` applies a function to every type a schema mentions and changes nothing else, so
each schema is a `Functor` whose `<$>` is that `map`, and the functor laws hold: mapping
the identity changes nothing, and mapping a composite is mapping one function after the
other. -/

namespace NonEmptyListSchema

variable {α β γ : Type}

@[simp] theorem map_id (xs : NonEmptyList α) : map id xs = xs := by
  cases xs; simp [map]

theorem map_comp (g : β → γ) (h : α → β) (xs : NonEmptyList α) :
    map (fun x => g (h x)) xs = map g (map h xs) := by
  cases xs; simp [map]

end NonEmptyListSchema

namespace LeanRecordSchema

variable {α β γ : Type}

@[simp] theorem map_id (xs : LeanRecordSchema α) : xs.map id = xs := by
  cases xs; simp [map]

theorem map_comp (g : β → γ) (h : α → β) (xs : LeanRecordSchema α) :
    xs.map (fun x => g (h x)) = (xs.map h).map g := by
  cases xs; simp [map]

instance : Functor LeanRecordSchema where
  map := map

instance : LawfulFunctor LeanRecordSchema where
  map_const := rfl
  id_map := map_id
  comp_map g h xs := map_comp h g xs

end LeanRecordSchema

namespace CtorsWithPayload

variable {α β γ : Type}

@[simp] theorem map_id (c : CtorsWithPayload α) : c.map id = c := by
  induction c with
  | here fields rest => simp [map]
  | skip rest ih => simp [map, ih]

theorem map_comp (g : β → γ) (h : α → β) (c : CtorsWithPayload α) :
    c.map (fun x => g (h x)) = (c.map h).map g := by
  induction c with
  | here fields rest => simp [map, NonEmptyListSchema.map_comp]
  | skip rest ih => simp [map, ih]

instance : Functor CtorsWithPayload where
  map := map

instance : LawfulFunctor CtorsWithPayload where
  map_const := rfl
  id_map := map_id
  comp_map g h c := map_comp h g c

end CtorsWithPayload

namespace LeanTaggedUnionSchema

variable {α β γ : Type}

@[simp] theorem map_id (c : LeanTaggedUnionSchema α) : c.map id = c := by
  cases c <;> simp [map]

theorem map_comp (g : β → γ) (h : α → β) (c : LeanTaggedUnionSchema α) :
    c.map (fun x => g (h x)) = (c.map h).map g := by
  cases c <;>
    simp [map, NonEmptyListSchema.map_comp, CtorsWithPayload.map_comp]

instance : Functor LeanTaggedUnionSchema where
  map := map

instance : LawfulFunctor LeanTaggedUnionSchema where
  map_const := rfl
  id_map := map_id
  comp_map g h c := map_comp h g c

end LeanTaggedUnionSchema

namespace LeanFamMemberSchema

variable {α β γ : Type}

@[simp] theorem map_id (m : LeanFamMemberSchema α) : m.map id = m := by
  cases m <;> simp [map]

theorem map_comp (g : β → γ) (h : α → β) (m : LeanFamMemberSchema α) :
    m.map (fun x => g (h x)) = (m.map h).map g := by
  cases m <;> simp [map, LeanRecordSchema.map_comp, LeanTaggedUnionSchema.map_comp]

instance : Functor LeanFamMemberSchema where
  map := map

instance : LawfulFunctor LeanFamMemberSchema where
  map_const := rfl
  id_map := map_id
  comp_map g h m := map_comp h g m

end LeanFamMemberSchema

namespace LeanMutualRecFamily

variable {α β γ : Type}

@[simp] theorem map_id (f : LeanMutualRecFamily α) : f.map id = f := by
  cases f <;> simp [map, LeanFamMemberSchema.map_id]

theorem map_comp (g : β → γ) (h : α → β) (f : LeanMutualRecFamily α) :
    f.map (fun x => g (h x)) = (f.map h).map g := by
  cases f <;> simp [map, LeanFamMemberSchema.map_comp]

instance : Functor LeanMutualRecFamily where
  map := map

instance : LawfulFunctor LeanMutualRecFamily where
  map_const := rfl
  id_map := map_id
  comp_map g h f := map_comp h g f

end LeanMutualRecFamily

/-! ## Coercions between the schemas

A record or a tagged union is a member of a family, and a sum whose first constructor
has no fields is a tagged union. -/

instance {α : Type} : CoeOut (CtorsWithPayload α) (LeanTaggedUnionSchema α) := ⟨.skip⟩
instance {α : Type} : CoeOut (LeanTaggedUnionSchema α) (LeanFamMemberSchema α) := ⟨.ctors⟩
instance {α : Type} : CoeOut (LeanRecordSchema α) (LeanFamMemberSchema α) := ⟨.record⟩

end LeanScript

end
