module

public import Init.Data.List.Lemmas
public import NonEmpty.ListCorrectByConstruction.Basic
public import NonEmpty.ListCorrectByConstruction.Ops
public import NonEmpty.ListCorrectByConstruction.Instances
public import NonEmpty.ListCorrectByConstruction.Notation

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
(`toList_ofList?`, `ofList?_toList` below).  A subtype `{ xs : List α // P xs }` would
do the same job, but it cannot be nested inside an `inductive` the way these can, which
is the whole point: `Ty.record` takes a `LeanRecordSchema Ty`, so the invariant is
carried by the type of the constructor's argument.
-/

/-! ## Generic containers -/

/-- The payload of a **record**: the types of its fields, in declaration order, of which
    there are **at least two** — a first, a second, and the rest.

    A one-field declaration is not a record but a newtype, whose wrapper is erased into
    its field, and a field-less one is a unit type, which is erased altogether; neither
    is writable here. -/
structure LeanRecordSchema (α : Type) where
  /-- The first element. -/
  fst : α
  /-- The second element. -/
  snd : α
  /-- Everything after the second. -/
  rest : List α
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

namespace LeanRecordSchema

variable {α β : Type}

/-- The elements, in order. -/
def toList (xs : LeanRecordSchema α) : List α := xs.fst :: xs.snd :: xs.rest

/-- How many elements there are — at least two. -/
def length (xs : LeanRecordSchema α) : Nat := xs.rest.length + 2

@[simp] theorem length_toList (xs : LeanRecordSchema α) : xs.toList.length = xs.length := by
  simp only [toList, length, List.length_cons]

theorem two_le_length (xs : LeanRecordSchema α) : 2 ≤ xs.toList.length := by
  simp only [length_toList, length]
  omega

/-- The list, if it has at least two elements. -/
def ofList? : List α → Option (LeanRecordSchema α)
  | a :: b :: rest => some ⟨a, b, rest⟩
  | _ => none

@[simp] theorem ofList?_toList (xs : LeanRecordSchema α) : ofList? xs.toList = some xs := rfl

theorem toList_ofList? : ∀ {xs : List α} {s : LeanRecordSchema α},
    ofList? xs = some s → s.toList = xs
  | _ :: _ :: _, _, h => by injection h with h; subst h; rfl
  | [], _, h => by simp [ofList?] at h
  | [_], _, h => by simp [ofList?] at h

theorem toList_injective {xs ys : LeanRecordSchema α} (h : xs.toList = ys.toList) : xs = ys := by
  cases xs; cases ys; simp_all [toList]

/-- Apply a function to every element. -/
def map (f : α → β) (xs : LeanRecordSchema α) : LeanRecordSchema β :=
  ⟨f xs.fst, f xs.snd, xs.rest.map f⟩

@[simp] theorem toList_map (f : α → β) (xs : LeanRecordSchema α) :
    (xs.map f).toList = xs.toList.map f := rfl

/-- Mapping the field types keeps the fields: a mapped record has as many of them. -/
@[simp] theorem length_map (f : α → β) (xs : LeanRecordSchema α) :
    (xs.map f).length = xs.length := by
  simp [map, length]

/-- The `i`-th element, if there is one. -/
def get? (xs : LeanRecordSchema α) (i : Nat) : Option α := xs.toList[i]?

end LeanRecordSchema

namespace NonEmptyListSchema

variable {α β : Type}

/-- Apply a function to every element of a non-empty list. -/
def map (f : α → β) (xs : NonEmptyList α) : NonEmptyList β :=
  ⟨f xs.head, xs.tail.map f⟩

@[simp] theorem toList_map (f : α → β) (xs : NonEmptyList α) :
    (map f xs).toList = xs.toList.map f := rfl

/-- The list, if it has an element. -/
def ofList? : List α → Option (NonEmptyList α)
  | a :: rest => some ⟨a, rest⟩
  | [] => none

@[simp] theorem ofList?_toList (xs : NonEmptyList α) : ofList? xs.toList = some xs := by
  cases xs; rfl

theorem toList_ofList? : ∀ {xs : List α} {s : NonEmptyList α},
    ofList? xs = some s → s.toList = xs
  | _ :: _, _, h => by injection h with h; subst h; rfl
  | [], _, h => by simp [ofList?] at h

end NonEmptyListSchema

/-! ## The constructors of a sum type -/

/-- The constructors of a sum type **of which at least one carries a field**, as the
    position of the *first* such constructor: `skip` is a constructor with no fields,
    and `here` is the first constructor that has some, followed by whatever comes after
    it.

    The encoding is canonical — a list of constructors in which some constructor has a
    field has exactly one encoding — so `toList` is injective and equality of two of
    these is equality of the constructor lists they denote. -/
inductive CtorsWithPayload (α : Type) where
  /-- This constructor carries at least one field; `rest` is what follows it. -/
  | here (fields : NonEmptyList α) (rest : List (List α))
  /-- This constructor carries no fields, and the one that does comes later. -/
  | skip (rest : CtorsWithPayload α)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

namespace CtorsWithPayload

variable {α β : Type}

/-- One entry per constructor, in declaration order, each holding its field types. -/
def toList : CtorsWithPayload α → List (List α)
  | .here fields rest => fields.toList :: rest
  | .skip rest => [] :: toList rest

/-- How many constructors there are — at least one. -/
def length : CtorsWithPayload α → Nat
  | .here _ rest => rest.length + 1
  | .skip rest => length rest + 1

@[simp] theorem length_toList (c : CtorsWithPayload α) : c.toList.length = c.length := by
  induction c with
  | here _ _ => simp [toList, length]
  | skip _ ih => simp [toList, length, ih]

/-- These constructors, if at least one of them has a field. -/
def ofList? : List (List α) → Option (CtorsWithPayload α)
  | [] => none
  | [] :: rest => (ofList? rest).map .skip
  | (f :: fs) :: rest => some (.here ⟨f, fs⟩ rest)

@[simp] theorem ofList?_toList (c : CtorsWithPayload α) : ofList? c.toList = some c := by
  induction c with
  | here fields _ => cases fields; rfl
  | skip _ ih => simp [toList, ofList?, ih]

theorem toList_ofList? : ∀ {l : List (List α)} {c : CtorsWithPayload α},
    ofList? l = some c → c.toList = l
  | [], _, h => by simp [ofList?] at h
  | (_ :: _) :: _, _, h => by injection h with h; subst h; rfl
  | [] :: rest, c, h => by
      simp only [ofList?, Option.map_eq_some_iff] at h
      obtain ⟨c', hc', rfl⟩ := h
      simp [toList, toList_ofList? hc']

/-- Some constructor of this sum carries a field. -/
theorem exists_nonempty (c : CtorsWithPayload α) : ∃ fs ∈ c.toList, fs ≠ [] := by
  induction c with
  | here fields rest =>
      exact ⟨fields.toList, by simp [toList], by simp⟩
  | skip rest ih =>
      obtain ⟨fs, hmem, hne⟩ := ih
      exact ⟨fs, by simp [toList, hmem], hne⟩

/-- Apply a function to the type of every field. -/
def map (f : α → β) : CtorsWithPayload α → CtorsWithPayload β
  | .here fields rest => .here (NonEmptyListSchema.map f fields) (rest.map (·.map f))
  | .skip rest => .skip (map f rest)

@[simp] theorem toList_map (f : α → β) (c : CtorsWithPayload α) :
    (c.map f).toList = c.toList.map (·.map f) := by
  induction c with
  | here _ _ => simp [toList, map]
  | skip _ ih => simp [toList, map, ih]

/-- Mapping the field types keeps the constructors: a mapped sum has as many of them. -/
@[simp] theorem length_map (f : α → β) (c : CtorsWithPayload α) :
    (c.map f).length = c.length := by
  induction c with
  | here _ _ => simp [map, length]
  | skip _ ih => simp [map, length, ih]

end CtorsWithPayload

/-! ## The five schemas -/

/-- The payload of an **enum**: a sum whose constructors all have no fields, printed as
    the plain numbers `shift`, `shift + 1`, ….

    The number of constructors is held as `extraConstructors`, the number *beyond the
    three an enum must have*, so an enum of fewer than three constructors is
    unwritable — see this module's header for why the three smaller cases are other
    types rather than small enums.  `shift` is an arbitrary `Int`, which is what unites
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

/-- The payload of a **tagged union**: at least two constructors, at least one of which
    carries a field.  (With one constructor it is a record, a newtype or a unit type;
    with no field anywhere it is an enum or a boolean.)

    As with `CtorsWithPayload`, the encoding names the *first* constructor with fields,
    so it is canonical. -/
inductive LeanTaggedUnionSchema (α : Type) where
  /-- Constructor `0` carries fields, and at least one further constructor follows. -/
  | payloadFirst (fields : NonEmptyList α) (next : List α) (rest : List (List α))
  /-- Constructor `0` carries no fields; the constructors after it are at least one,
      and one of them carries a field. -/
  | skip (rest : CtorsWithPayload α)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

namespace LeanTaggedUnionSchema

variable {α β : Type}

/-- One entry per constructor, in declaration order, each holding its field types. -/
def toList : LeanTaggedUnionSchema α → List (List α)
  | .payloadFirst fields next rest => fields.toList :: next :: rest
  | .skip rest => [] :: rest.toList

/-- How many constructors there are — at least two. -/
def length : LeanTaggedUnionSchema α → Nat
  | .payloadFirst _ _ rest => rest.length + 2
  | .skip rest => rest.length + 1

@[simp] theorem length_toList (c : LeanTaggedUnionSchema α) : c.toList.length = c.length := by
  cases c with
  | payloadFirst _ _ _ =>
      simp only [toList, length, List.length_cons]
  | skip rest =>
      simp only [toList, length, List.length_cons, CtorsWithPayload.length_toList]

theorem two_le_length (c : LeanTaggedUnionSchema α) : 2 ≤ c.toList.length := by
  cases c with
  | payloadFirst _ _ rest =>
      simp only [toList, List.length_cons]
      omega
  | skip rest =>
      simp only [toList, List.length_cons, CtorsWithPayload.length_toList]
      cases rest <;> simp only [CtorsWithPayload.length] <;> omega

theorem two_le_length' (c : LeanTaggedUnionSchema α) : 2 ≤ c.length := by
  have := c.two_le_length
  simpa using this

/-- The field types of constructor `t`, in declaration order.  The bound is stated
    against `length` — the number of constructors — rather than against the length of
    `toList`, so that a caller never has to see the list. -/
def get (c : LeanTaggedUnionSchema α) (t : Nat) (ht : t < c.length) : List α :=
  c.toList[t]'(by rw [length_toList]; exact ht)

@[simp] theorem get_eq_getElem (c : LeanTaggedUnionSchema α) (t : Nat) (ht : t < c.length) :
    c.get t ht = c.toList[t]'(by rw [length_toList]; exact ht) := rfl

/-- Some constructor of this union carries a field. -/
theorem exists_nonempty (c : LeanTaggedUnionSchema α) : ∃ fs ∈ c.toList, fs ≠ [] := by
  cases c with
  | payloadFirst fields _ _ =>
      exact ⟨fields.toList, by simp [toList], by simp⟩
  | skip rest =>
      obtain ⟨fs, hmem, hne⟩ := rest.exists_nonempty
      exact ⟨fs, by simp [toList, hmem], hne⟩

/-- These constructors, if they are the constructors of a tagged union. -/
def ofList? : List (List α) → Option (LeanTaggedUnionSchema α)
  | (f :: fs) :: next :: rest => some (.payloadFirst ⟨f, fs⟩ next rest)
  | [] :: rest => (CtorsWithPayload.ofList? rest).map .skip
  | _ => none

@[simp] theorem ofList?_toList (c : LeanTaggedUnionSchema α) : ofList? c.toList = some c := by
  cases c with
  | payloadFirst fields _ _ => cases fields; rfl
  | skip rest => simp [toList, ofList?]

theorem toList_ofList? : ∀ {l : List (List α)} {c : LeanTaggedUnionSchema α},
    ofList? l = some c → c.toList = l
  | (_ :: _) :: _ :: _, _, h => by injection h with h; subst h; rfl
  | [] :: rest, c, h => by
      simp only [ofList?, Option.map_eq_some_iff] at h
      obtain ⟨c', hc', rfl⟩ := h
      simp [toList, CtorsWithPayload.toList_ofList? hc']
  | [], _, h => by simp [ofList?] at h
  | [_ :: _], _, h => by simp [ofList?] at h

/-- Apply a function to the type of every field. -/
def map (f : α → β) : LeanTaggedUnionSchema α → LeanTaggedUnionSchema β
  | .payloadFirst fields next rest =>
      .payloadFirst (NonEmptyListSchema.map f fields) (next.map f) (rest.map (·.map f))
  | .skip rest => .skip (rest.map f)

@[simp] theorem toList_map (f : α → β) (c : LeanTaggedUnionSchema α) :
    (c.map f).toList = c.toList.map (·.map f) := by
  cases c <;> simp [toList, map]

/-- Mapping the field types keeps the constructors: a mapped union has as many of them,
    in the same order, so a number that is a constructor of one is a constructor of the
    other. -/
@[simp] theorem length_map (f : α → β) (c : LeanTaggedUnionSchema α) :
    (c.map f).length = c.length := by
  cases c <;> simp [map, length]

/-- The fields of constructor `t` of a mapped union are the fields of constructor `t`,
    mapped. -/
theorem get_map (f : α → β) (c : LeanTaggedUnionSchema α) (t : Nat) (ht : t < c.length) :
    (c.map f).get t (by simpa using ht) = (c.get t ht).map f := by
  simp only [get, toList_map]
  rw [List.getElem_map]

end LeanTaggedUnionSchema

/-! ## Mutual families -/

/-- One member of a mutual recursive family: the shape it contributes, which is one of
    the three shapes a member can have.  There is deliberately no *enum* member: an enum
    mentions no other member, so a block containing one is not a family but a `mutual`
    block of independent declarations. -/
inductive LeanFamMemberSchema (α : Type) where
  /-- A member with at least two constructors, one of which carries a field. -/
  | ctors (schema : LeanTaggedUnionSchema α)
  /-- A single-constructor member with at least two fields. -/
  | record (schema : LeanRecordSchema α)
  /-- A newtype member: it has no object of its own, and a value of it is a value of
      this, its single field. -/
  | alias (body : α)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

namespace LeanFamMemberSchema

variable {α β : Type}

/-- The constructors of a member, as a list of the field types of each: a `record`
    member has one constructor and an `alias` member one constructor of one field. -/
def toCtors : LeanFamMemberSchema α → List (List α)
  | .ctors s => s.toList
  | .record s => [s.toList]
  | .alias b => [[b]]

/-- Apply a function to every type the member mentions. -/
def map (f : α → β) : LeanFamMemberSchema α → LeanFamMemberSchema β
  | .ctors s => .ctors (s.map f)
  | .record s => .record (s.map f)
  | .alias b => .alias (f b)

end LeanFamMemberSchema

/-- The payload of one member of a **mutual recursive family**: the bodies of *all* of
    its members, in declaration order, and which of them this type is.

    It is a zipper — the members before this one, this one, and the members after it —
    so the member number is in range by construction, and the family has at least two
    members by construction: a block of one member is not mutual, and is the ordinary
    recursive shape it is. -/
inductive LeanMutualRecFamily (α : Type) where
  /-- The selected member is followed by at least one further member. -/
  | selectedThenMore (before : List (LeanFamMemberSchema α)) (current : LeanFamMemberSchema α)
      (next : LeanFamMemberSchema α) (after : List (LeanFamMemberSchema α))
  /-- The selected member is the last one, and at least one member precedes it. -/
  | selectedLast (first : LeanFamMemberSchema α) (before : List (LeanFamMemberSchema α))
      (current : LeanFamMemberSchema α)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

namespace LeanMutualRecFamily

variable {α β : Type}

/-- All the members of the family, in declaration order. -/
def members : LeanMutualRecFamily α → List (LeanFamMemberSchema α)
  | .selectedThenMore before current next after => before ++ current :: next :: after
  | .selectedLast first before current => first :: before ++ [current]

/-- Which member of the family this type is. -/
def memberIdx : LeanMutualRecFamily α → Nat
  | .selectedThenMore before _ _ _ => before.length
  | .selectedLast _ before _ => before.length + 1

/-- The member this type is. -/
def current : LeanMutualRecFamily α → LeanFamMemberSchema α
  | .selectedThenMore _ current _ _ => current
  | .selectedLast _ _ current => current

theorem two_le_members (f : LeanMutualRecFamily α) : 2 ≤ f.members.length := by
  cases f with
  | selectedThenMore before _ _ after =>
      simp only [members, List.length_append, List.length_cons]
      omega
  | selectedLast _ before _ =>
      simp only [members, List.length_cons, List.length_append]
      omega

theorem memberIdx_lt (f : LeanMutualRecFamily α) : f.memberIdx < f.members.length := by
  cases f with
  | selectedThenMore before _ _ after =>
      simp only [members, memberIdx, List.length_append, List.length_cons]
      omega
  | selectedLast _ before _ =>
      simp only [members, memberIdx, List.length_cons, List.length_append]
      omega

theorem getElem?_memberIdx (f : LeanMutualRecFamily α) :
    f.members[f.memberIdx]? = some f.current := by
  cases f with
  | selectedThenMore before _ _ _ =>
      simp [members, memberIdx, current]
  | selectedLast _ before _ =>
      simp [members, memberIdx, current]

/-- The family with these members, selecting member `i` — if there are at least two of
    them and `i` is one of them. -/
def ofMembers? (ms : List (LeanFamMemberSchema α)) (i : Nat) :
    Option (LeanMutualRecFamily α) :=
  match ms[i]? with
  | none => none
  | some m =>
    let before := ms.take i
    match ms.drop (i + 1) with
    | next :: after =>
        if 2 ≤ ms.length then some (.selectedThenMore before m next after) else none
    | [] =>
        match before with
        | first :: bs => some (.selectedLast first bs m)
        | [] => none

/-- Apply a function to every type the family mentions. -/
def map (f : α → β) : LeanMutualRecFamily α → LeanMutualRecFamily β
  | .selectedThenMore before current next after =>
      .selectedThenMore (before.map (·.map f)) (current.map f) (next.map f)
        (after.map (·.map f))
  | .selectedLast first before current =>
      .selectedLast (first.map f) (before.map (·.map f)) (current.map f)

end LeanMutualRecFamily

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
