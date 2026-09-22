module

public import LeanScript.RTyWf

@[expose] public section

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

namespace LeanScript

/-!
# `Ty`: the types that can be compiled to JavaScript

`Ty` is a **tree of types**.  There are no schemas held on the side, no names and no
side tables: a type is built out of its own parts, and two types are equal when their
trees are equal.

Six decisions are baked into it.

* **no names anywhere.**  A constructor is a *position* in the list of constructors and
  a field is a *position* in the list of fields, so a value of a user-defined type is
  `{ tag: 0, _1: …, _2: … }` — a number and positional fields, never a string.

* **ordinary equality.**  `Ty` is a first-order inductive with a `DecidableEq` instance
  (`Ty.beq` and the lemmas below), so two types are compared with `=` and `decide`.

* **no degenerate type is writable.**  The payload of each shape is one of the schemas
  of `LeanScript.Schema`, and those carry their counting invariants in their *types*:

  | shape             | payload                          | what cannot be written              |
  | :---------------- | :------------------------------- | :---------------------------------- |
  | `Ty.enum`         | `LeanEnumSchema`                 | fewer than three constructors       |
  | `Ty.record`       | `LeanRecordSchema Ty`            | fewer than two fields               |
  | `Ty.taggedUnion`  | `LeanTaggedUnionSchema Ty`       | fewer than two constructors, or none with a field |
  | `Ty.recObject`    | `LeanRecordSchema RTy`        | fewer than two fields               |
  | `Ty.recTaggedUnion` | `LeanTaggedUnionSchema RTy` | fewer than two constructors, or none with a field |
  | `Ty.mutualRecursiveFamily` | `LeanMutualRecFamily RTy` | fewer than two members, or a member number out of range |

  So an `Empty`-like type (no values) and a `Unit`-like type (one value, carrying no
  information, erased before a type is built) have no `Ty`, and a `Bool`-like type — a
  sum of exactly two field-less constructors — is not an enum with two constructors but
  `Ty.bool`, so that it prints as `true`/`false`.  There is likewise no `Ty.void` and no
  `Ty.erased`, and `bitvec n` needs `n ≥ 1` because `BitVec 0` is a unit type.

* **no unmodelled type.**  There is no `dynamic`, and no stand-in for a type the backend
  does not know the shape of: every Lean type a compiled declaration mentions is either
  one of the shapes below or the declaration is refused.  A parameterised declaration is
  modelled *at its instantiation* (`Except Nat String` is a `taggedUnion` of
  `[[nat], [string]]`) — a polymorphic Lean declaration is translated once per
  instantiation the module uses, and one with no instantiation is not translated at all —
  and a mutual block of declarations is modelled as a `mutualRecursiveFamily`.

* **leaves live in `LeanPrimTy`.**  Every terminal type (`bool`, `nat`, `uint32`,
  `bitvec n`, `string`, …) is a constructor of `LeanScript.LeanPrimTy`, and `Ty` embeds them
  with `Ty.prim`.  `Ty.nat`, `Ty.uint32`, … remain available as abbreviations.

* **the shapes are language-independent.**  The schemas are parametrised by the type
  language (`LeanRecordSchema α`), so the *same* schema describes a record of `Ty`s and
  a record of `RTy`s — and will describe a record of the types of whatever further
  language is added next.  Only their instantiation lives here.

## The shapes a user-defined type can have

A Lean declaration is modelled by *which* of the following shapes it has, so a
traversal never has to ask a schema what kind of declaration it came from:

| Lean                                              | `Ty`                                   |
| :------------------------------------------------ | :------------------------------------- |
| `inductive Dir \| north \| south`                  | `.bool` — a two-constructor enum is a boolean |
| `inductive Dir3 \| n \| s \| e`                    | `.enum ⟨0, 0⟩` (three constructors, from `0`) |
| `structure Point where x y : Nat`                  | `.record ⟨.nat, .nat, []⟩`             |
| `structure Wrap where v : Nat` (a newtype)         | `.nat` — the wrapper is erased         |
| `Option Nat`                                       | `.option .nat`                         |
| `inductive T \| leaf \| node : T → T → T`          | `.recTaggedUnion (.skip (.here ⟨.self, [.self]⟩ []))` |
| `structure Tree where n : Nat; kids : Array Tree`  | `.recObject ⟨.nat, .array (.self), []⟩` |
| `structure Rose where kids : Array Rose`           | `.recAlias (.array (.self))`         |
| a mutual block                                     | `.mutualRecursiveFamily f`             |

## `.self` is available in the recursive shapes and nowhere else

The recursive shapes — `recTaggedUnion`, `recObject`, `recAlias` and
`mutualRecursiveFamily` — are the *binders* of the type language: their children are
`RTy`s, the types *inside a recursive declaration*.  A declaration that recurses on its
own is pointed at by `RTy.self`, which carries no number — there is one declaration in
scope, so an occurrence is the whole of the information — and a member of a mutual
family by `RTy.familyMember i`.  That is the distinction of `LeanScript.Fixpoint`:
`RTy.asWithSelf` reads a layer of the first kind of scope as a `WithSelf`, and
`RTy.asMutualRef` reads a layer of the second as a `WithRefToMutualDatatype`, whose
`Fin familySize` cannot point outside the family.  Which reading is total is decided by
the scope, and `LeanScript.RTyWf` asks for exactly that.  The other shapes carry ordinary
`Ty`s, which have no self-reference at all, so a type outside a recursive declaration
cannot mention one.

`RTy` mirrors `Ty`, so anything may appear inside a recursive declaration — a `Nat`, an
`Option Tree`, an `Array Tree`.  Where an `RTy` is itself a *recursive* shape, it opens
a new scope: the `.self` of its children is that inner declaration, exactly as a nested
binder shadows an outer one.

## Why `Ty` and `RTy` are two types, and what they share

They differ in two ways that no common fixed point removes.  `Ty` has no
self-reference, which is what makes a closed type closed, and its recursive shapes carry
**sealed** payloads — a schema together with `h_wf`, a proof *about `RTy`* — while the
payloads inside `RTy` carry none, since `RTy.Wf` is a predicate on `RTy` and cannot be
mentioned while `RTy` is being declared.  So `RTy` is the raw language and `Ty` the
language a compiler reads, and they meet through `Ty.toRTy`: a closed type is a payload
that uses none of the freedom a payload has.

What they no longer duplicate is the work.  `Ty.toRTy` is injective
(`Ty.toRTy_inj`), so `Ty.beq` *is* `RTy.beq` on the two readings rather than a second
structural comparison over the same schemas, and `RTy.hasSelf` is `RTy.selfRefs` read as
a `Bool` rather than a second traversal.  What is left of `Ty`'s own code is the
inductive itself, the reading, and the lemmas that say the reading lands where it should.

That a recursive shape really does mention itself, and that the type it describes has
any values at all (`inductive Bad | mk : Bad → Bad` has none), are conditions on a whole
type rather than counting conditions on one payload — and they are carried by the
payload all the same: each of the four recursive constructors takes a **sealed** payload
(`LeanTaggedUnionSchemaSealed`, `LeanRecordSchemaSealed`, `RTySealed`,
`LeanMutualRecFamilySealed` of `LeanScript.RTyWf`), which is the payload together with
`h_wf`, the proposition that says the shape describes a type that exists; it is
discharged by `by decide` for a type written out.  So there is no subtype of the
well-formed types and no check to forget: a degenerate recursive declaration is not a
`Ty` that fails a test, it is not a `Ty`.  And since `h_wf` is a `Prop`, two sealed
payloads with the same schema are equal, so equality of types never looks at a proof.

## The shared type formers

`array`, `task`, `promise` and `thunk` are the constructors of
`LeanPrimTyCovariant`: it says nothing about recursion and makes sense at every layer, so
it is parametrised by the layer's own type and embedded by `Ty` and by `RTy` alike, with
`Ty.primCovariant`.  `Ty.array`, … remain available — and usable in patterns —
as abbreviations for its cases.  The function type is a constructor of each layer in its
own right (`Ty.fn`).
-/

/-! ## `Ty`, `RTy` and the members of a mutual family -/

/-- A closed type: one that mentions no recursive declaration it is not itself part of.
    This is the type language the terms of `LeanScript.Expr` are indexed by. -/
inductive Ty where
  /-- A terminal type: a scalar or other built-in leaf.  See `LeanPrimTy`. -/
  | prim : LeanPrimTy → Ty
  -- Erased values are unrepresentable, so there is no `typeParam` constructor: a value
  -- whose Lean type is a type parameter of the enclosing declaration carries nothing at
  -- run time and never reaches this language.
  /-- A function type, `σ ⇒ τ`: **one** parameter and **one** result.  Every function of
      the language is curried, so Lean's `def foo : Int → Int → Int` is
      `.fn .int (.fn .int .int)`, and a function answering with several values at once
      is a function answering with the one type that holds them (a record). -/
  | fn : Ty → Ty → Ty
  /-- A built-in type former that carries one type: an array, a list, a task, a promise
      or a thunk.  `Ty.array`, … abbreviate the cases. -/
  | primCovariant : LeanPrimTyCovariant Ty → Ty
  /-- A non-recursive sum whose constructors all have no fields, printed as the plain
      numbers `shift`, `shift + 1`, … — of which there are **at least three**, since the
      smaller cases are not enums: see `LeanEnumSchema`. -/
  | enum : LeanEnumSchema → Ty
  /-- A non-recursive single-constructor type with ≥ 2 fields, in declaration order.
      In JS: `{ tag: 0, _1: …, _2: … }`.  A *one*-field record is a newtype: it is
      erased, and its `Ty` is the field's own `Ty`. -/
  | record : LeanRecordSchema Ty → Ty
  /-- A non-recursive sum type with fields (`Option`, `Except`, …): one entry per
      constructor, in declaration order, each holding the types of that constructor's
      fields.  In JS: `{ tag: 1, _1: … }`. -/
  | taggedUnion : LeanTaggedUnionSchema Ty → Ty
  /-- A recursive sum type (`MyList`, a tree, …): one entry per constructor, each
      holding the types of its fields, in which `RTy.self` is an occurrence of the
      declaration itself.  In JS: `{ tag: …, … }`. -/
  | recTaggedUnion : (l : LeanTaggedUnionSchemaSealed) → Ty
  /-- A recursive single-constructor type with ≥ 2 fields
      (`structure Tree where n : Nat; kids : Array Tree`), in which `RTy.self` is an
      occurrence of the declaration itself.  In JS: `{ tag: 0, _1: …, _2: … }`. -/
  | recObject : (fs : LeanRecordSchemaSealed) → Ty
  /-- A recursive **newtype**, with the wrapper erased
      (`structure Rose where kids : Array Rose`): the fixed point of the single field's
      type.  In JS a `Rose` is just `[…]`, an array of arrays of …, with no object
      wrapper — `[[], [[], []]]` is a `Rose`. -/
  | recAlias : (b : RTySealed) → Ty
  /-- One member of a genuinely mutual recursive family: the bodies of *all* of its
      members, in declaration order, and which of them this type is — held as a zipper,
      so the member number is in range and the family has two members or more by
      construction.  Inside the bodies, `RTy.self i` is an occurrence of member `i`, so
      a type never points outside its family. -/
  | mutualRecursiveFamily : (f : LeanMutualRecFamilySealed) → Ty
  /-- A declaration that **caches values computed from itself**: the declaration, and the
      type of each cached value.  `Lean.Name` is one — it stores its own `hash`, declared
      `@[computed_field]`.  A cached value is a function of the value, so it is not a
      field and carries no information the declaration does not already have; what it
      decides is the object the runtime holds, and so the JavaScript that is printed.
      `Ty.enum_withComputedFields`, … name the shapes the base is meant to be. -/
  | withComputedFields : Ty → NonEmptyList LeanPrimTy → Ty

namespace Ty

/-! ## A closed type, read as a payload of a recursive declaration

A closed type mentions no `.self`, so it is a payload that happens to use none of the
freedom a payload has: `Ty.toRTy` is that inclusion.  The lemmas further down say
exactly that — the image of a closed type mentions no member of the declaration it is
placed in, and it is well formed — and they are what lets `Ty.list` be written for a
*variable* element type, rather than only for one written out. -/

mutual

/-- A closed type, as a payload of a recursive declaration. -/
def toRTy : Ty → RTy
  | .prim p => .prim p
  | .fn a b => .fn (toRTy a) (toRTy b)
  | .primCovariant s => .primCovariant (toRTyCov s)
  | .enum s => .enum s
  | .record fs => .record (toRTyA2 fs)
  | .taggedUnion l => .taggedUnion (toRTyTU l)
  | .recTaggedUnion l => .recTaggedUnion l.schema
  | .recObject fs => .recObject fs.fields
  | .recAlias b => .recAlias b.body
  | .mutualRecursiveFamily f => .mutualRecursiveFamily f.family
  | .withComputedFields b cs => .withComputedFields (toRTy b) cs

/-- `Ty.toRTy`, on an invariant type former. -/
def toRTyCov : LeanPrimTyCovariant Ty → LeanPrimTyCovariant RTy
  | .array a => .array (toRTy a)
  -- | .task a => .task (toRTy a)
  -- | .promise a => .promise (toRTy a)
  | .thunk a => .thunk (toRTy a)
  | .lazy a => .lazy (toRTy a)

/-- `Ty.toRTy`, on a list of types. -/
def toRTyList : List Ty → List RTy
  | [] => []
  | a :: as => toRTy a :: toRTyList as

/-- `Ty.toRTy`, on the constructors of a layout. -/
def toRTyCtors : List (List Ty) → List (List RTy)
  | [] => []
  | fs :: l => toRTyList fs :: toRTyCtors l

/-- `Ty.toRTy`, on the fields of a record. -/
def toRTyA2 : LeanRecordSchema Ty → LeanRecordSchema RTy
  | ⟨a, b, rest⟩ => ⟨toRTy a, toRTy b, toRTyList rest⟩

/-- `Ty.toRTy`, on the fields of a constructor that has at least one. -/
def toRTyNE : NonEmptyList Ty → NonEmptyList RTy
  | ⟨a, as⟩ => ⟨toRTy a, toRTyList as⟩

/-- `Ty.toRTy`, on the constructors of a tagged union. -/
def toRTyTU : LeanTaggedUnionSchema Ty → LeanTaggedUnionSchema RTy
  | .payloadFirst f n r => .payloadFirst (toRTyNE f) (toRTyList n) (toRTyCtors r)
  | .skip rest => .skip (toRTyCP rest)

/-- `Ty.toRTy`, on the constructors that follow a field-less one. -/
def toRTyCP : CtorsWithPayload Ty → CtorsWithPayload RTy
  | .here f r => .here (toRTyNE f) (toRTyCtors r)
  | .skip rest => .skip (toRTyCP rest)

end

/-! ## A closed type read as a payload is a **reading**: it loses nothing

Every constructor of `Ty` is carried to a constructor of `RTy`, and the four sealed
payloads are carried to their schemas — which is faithful, since a sealed payload is
its schema and a proof, and the proof is a `Prop`.  So `Ty.toRTy` is injective, and
that is what lets the equality of `Ty` *be* the equality of `RTy` rather than a second
copy of it. -/

mutual

/-- A closed type is determined by its reading as a payload. -/
theorem toRTy_inj : ∀ {a b : Ty}, toRTy a = toRTy b → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [toRTy]
  case fn.fn => exact ⟨toRTy_inj h.1, toRTy_inj h.2⟩
  case primCovariant.primCovariant => exact toRTyCov_inj h
  case record.record => exact toRTyA2_inj h
  case taggedUnion.taggedUnion => exact toRTyTU_inj h
  case recTaggedUnion.recTaggedUnion => exact LeanTaggedUnionSchemaSealed.eq_of_schema_eq h
  case recObject.recObject => exact LeanRecordSchemaSealed.eq_of_fields_eq h
  case recAlias.recAlias => exact RTySealed.eq_of_body_eq h
  case mutualRecursiveFamily.mutualRecursiveFamily =>
    exact LeanMutualRecFamilySealed.eq_of_family_eq h
  case withComputedFields.withComputedFields => exact toRTy_inj h.1

/-- The same, for an invariant type former. -/
theorem toRTyCov_inj :
    ∀ {a b : LeanPrimTyCovariant Ty}, toRTyCov a = toRTyCov b → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [toRTyCov] <;> exact toRTy_inj h

/-- The same, for a list of types. -/
theorem toRTyList_inj : ∀ {a b : List Ty}, toRTyList a = toRTyList b → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [toRTyList]
  exact ⟨toRTy_inj h.1, toRTyList_inj h.2⟩

/-- The same, for the constructors of a layout. -/
theorem toRTyCtors_inj :
    ∀ {a b : List (List Ty)}, toRTyCtors a = toRTyCtors b → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [toRTyCtors]
  exact ⟨toRTyList_inj h.1, toRTyCtors_inj h.2⟩

/-- The same, for the fields of a record. -/
theorem toRTyA2_inj :
    ∀ {a b : LeanRecordSchema Ty}, toRTyA2 a = toRTyA2 b → a = b := by
  intro a b h
  cases a
  cases b
  simp_all [toRTyA2]
  exact ⟨toRTy_inj h.1, toRTy_inj h.2.1, toRTyList_inj h.2.2⟩

/-- The same, for the fields of a constructor that has at least one. -/
theorem toRTyNE_inj : ∀ {a b : NonEmptyList Ty}, toRTyNE a = toRTyNE b → a = b := by
  intro a b h
  cases a
  cases b
  simp_all [toRTyNE]
  exact ⟨toRTy_inj h.1, toRTyList_inj h.2⟩

/-- The same, for the constructors of a tagged union. -/
theorem toRTyTU_inj :
    ∀ {a b : LeanTaggedUnionSchema Ty}, toRTyTU a = toRTyTU b → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [toRTyTU]
  case payloadFirst.payloadFirst =>
    exact ⟨toRTyNE_inj h.1, toRTyList_inj h.2.1, toRTyCtors_inj h.2.2⟩
  case skip.skip => exact toRTyCP_inj h

/-- The same, for the constructors that follow a field-less one. -/
theorem toRTyCP_inj :
    ∀ {a b : CtorsWithPayload Ty}, toRTyCP a = toRTyCP b → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [toRTyCP]
  case here.here => exact ⟨toRTyNE_inj h.1, toRTyCtors_inj h.2⟩
  case skip.skip => exact toRTyCP_inj h

end

/-! ## Deciding equality

A closed type is a payload of a recursive declaration that mentions no declaration
(`Ty.toRTy`), and that reading is injective (`Ty.toRTy_inj`).  So the equality of
`LeanScript.RTy` decides the equality of `Ty` too: `Ty.beq` is `RTy.beq` on the two
readings, and the lemmas that make it equality follow from `RTy`'s, instead of a second
structural comparison over the same schemas. -/

/-- Structural equality of two closed types: the equality of `LeanScript.RTy`, on their
    readings as payloads. -/
def beq (a b : Ty) : Bool := RTy.beq (toRTy a) (toRTy b)

/-- Closed types that compare equal are equal. -/
theorem eq_of_beq : ∀ {a b : Ty}, Ty.beq a b = true → a = b :=
  fun h => toRTy_inj (RTy.eq_of_beq h)

/-- Every closed type compares equal to itself. -/
theorem beq_refl (a : Ty) : Ty.beq a a = true := RTy.beq_refl (toRTy a)

instance : DecidableEq Ty := fun a b =>
  decidable_of_iff (Ty.beq a b = true) ⟨Ty.eq_of_beq, fun h => h ▸ Ty.beq_refl a⟩

instance : BEq Ty := ⟨Ty.beq⟩
instance : ReflBEq Ty where
  rfl {a} := Ty.beq_refl a
instance : LawfulBEq Ty where
  eq_of_beq := by intro a b; exact eq_of_beq


/-! ## The shared type formers, as abbreviations

`Ty.primCovariant` is the only way to build an array, a thunk or a delayed value, but
writing `.primCovariant (.array α)` everywhere is noise, so each former is also
available directly under `Ty` and `RTy`.  They are `@[match_pattern]`, so `.array α` works
in a pattern as well as in a term. -/

/-- In JS: an array. -/
@[match_pattern] abbrev array (α : Ty) : Ty := .primCovariant (.array α)
-- /-- In JS: `Promise<α>`. -/
-- @[match_pattern] abbrev task (α : Ty) : Ty := .primCovariant (.task α)
-- /-- In JS: `Promise<α>`. -/
-- @[match_pattern] abbrev promise (α : Ty) : Ty := .primCovariant (.promise α)
/-- A thunk. -/
@[match_pattern] abbrev thunk (α : Ty) : Ty := .primCovariant (.thunk α)

/-- A JS function of no arguments answering with an `α`: what a Lean `Unit → α` is once
    its erased argument is dropped. -/
@[match_pattern] abbrev lazy (α : Ty) : Ty := .primCovariant (.lazy α)


/-! ## The terminal types, as `Ty` abbreviations

`Ty.prim` is the only leaf constructor, but writing `.prim .nat` everywhere is noise,
so each `LeanPrimTy` is also available directly under the `Ty` namespace — which is what
makes `.nat`, `.uint32`, `.bitvec 32`, … keep working in a position expecting a
`Ty`. -/

instance : CoeOut (LeanPrimTy) Ty := ⟨.prim⟩
instance : CoeOut (LeanPrimTyCovariant Ty) Ty := ⟨.primCovariant⟩

/-- In JS: `boolean`. -/
abbrev bool : Ty := .prim .bool
/-- A natural number. -/
abbrev nat : Ty := .prim .nat
/-- An integer. -/
abbrev int : Ty := .prim .int
/-- An 8-bit unsigned integer. -/
abbrev uint8 : Ty := .prim .uint8
/-- A 16-bit unsigned integer. -/
abbrev uint16 : Ty := .prim .uint16
/-- A 32-bit unsigned integer. -/
abbrev uint32 : Ty := .prim .uint32
/-- A 64-bit unsigned integer. -/
abbrev uint64 : Ty := .prim .uint64
/-- An 8-bit signed integer. -/
abbrev int8 : Ty := .prim .int8
/-- A 16-bit signed integer. -/
abbrev int16 : Ty := .prim .int16
/-- A 32-bit signed integer. -/
abbrev int32 : Ty := .prim .int32
/-- A 64-bit signed integer. -/
abbrev int64 : Ty := .prim .int64
/-- A character. -/
abbrev char : Ty := .prim .char
/-- A string. -/
abbrev string : Ty := .prim .string
/-- A 64-bit float. -/
abbrev float : Ty := .prim .float
/-- A 32-bit float. -/
abbrev float32 : Ty := .prim .float32
/-- A raw position in a string. -/
abbrev stringPosRaw : Ty := .prim .stringPosRaw
/-- A raw substring. -/
abbrev substringRaw : Ty := .prim .substringRaw

/-- In JS: `Uint8Array`.  At this layer it is an array of bytes; the later JavaScript
    type language is what turns it into a `Uint8Array`. -/
abbrev byteArray : Ty := .array (.prim .uint8)
/-- In JS: `Float64Array`.  At this layer it is an array of floats. -/
abbrev floatArray : Ty := .array (.prim .float)
/-- `Ordering` is the enum with three constructors whose numbering starts at `-1`, so
    it prints as `-1 | 0 | 1` — the numbering the comparison functions of the runtime
    answer with.  It is not a terminal type of its own: `Ty.enum` with a shift is what
    a specially numbered enum is. -/
abbrev ordering : Ty := .enum ⟨0, -1⟩
-- /-- In JS (node only): a `ChildProcess` handle. -/
-- abbrev childProcess : Ty := .prim .childProcess
-- Commented out with `LeanPrimTy.childProcess`.
-- /-- In JS: `object` / `any`. -/
-- abbrev shareCommonObject : Ty := .prim .shareCommonObject
-- /-- In JS: a `Map` / cache object. -/
-- abbrev shareCommonState : Ty := .prim .shareCommonState
-- Commented out with the two `ShareCommon` handles of `LeanPrimTy`, which are erased.

/-- The enum with `n` constructors numbered from `shift` — `none` unless `n` is a number
    of constructors an enum can have, which is three or more: with none the type has no
    values, with one it is a unit type and is erased, and with two it is `Ty.bool`. -/
def enumOfCount? (n : Nat) (shift : Int := 0) : Option Ty :=
  (LeanEnumSchema.ofCount? n shift).map Ty.enum -- TODO: same as in RTy, refactor

/-- The type of a field-less sum with `n` constructors: `Ty.bool` for two of them and an
    enum for three or more.  `none` for the two degenerate cases, which have no type:
    a sum with no constructors has no values, and one with a single constructor is a
    unit type, which is erased. -/
def enumOrBool? (n : Nat) (shift : Int := 0) : Option Ty :=
  if n == 2 && shift == 0 then some LeanPrimTy.bool else enumOfCount? n shift -- TODO: same as in RTy, refactor

infixr:70 " ⇒ " => Ty.fn

/-- The curried function type with these argument types and this result:
    `arrows [σ₁, σ₂] τ` is `σ₁ ⇒ σ₂ ⇒ τ`, and `arrows [] τ` is `τ`. -/
abbrev arrows (σs : List Ty) (τ : Ty) : Ty := σs.foldr Ty.fn τ


/-- `Option α`: a non-recursive sum whose constructor `0` (`none`) carries nothing and
    whose constructor `1` (`some`) carries the value. -/
abbrev option (α : Ty) : Ty := .taggedUnion (.skip (.here ⟨α, []⟩ [])) -- TODO: derive using elab

/-- `α × β`: one constructor with two fields. -/
abbrev prod (α β : Ty) : Ty := .record ⟨α, β, []⟩ -- TODO: derive using elab


mutual

/-- A closed type points at no member of the declaration it is placed in. -/
theorem selfRefs_toRTy : ∀ (t : Ty), RTy.selfRefs (toRTy t) = []
  | .prim _ => by simp [toRTy, RTy.selfRefs]
  | .fn a b => by simp [toRTy, RTy.selfRefs, selfRefs_toRTy a, selfRefs_toRTy b]
  | .primCovariant s => by simp [toRTy, RTy.selfRefs, selfRefsCov_toRTyCov s]
  | .enum _ => by simp [toRTy, RTy.selfRefs]
  | .record fs => by simp [toRTy, RTy.selfRefs, selfRefsA2_toRTyA2 fs]
  | .taggedUnion l => by simp [toRTy, RTy.selfRefs, selfRefsTU_toRTyTU l]
  | .recTaggedUnion _ => by simp [toRTy, RTy.selfRefs]
  | .recObject _ => by simp [toRTy, RTy.selfRefs]
  | .recAlias _ => by simp [toRTy, RTy.selfRefs]
  | .mutualRecursiveFamily _ => by simp [toRTy, RTy.selfRefs]
  | .withComputedFields b _ => by simp [toRTy, RTy.selfRefs, selfRefs_toRTy b]

/-- The same, for an invariant type former. -/
theorem selfRefsCov_toRTyCov :
    ∀ (s : LeanPrimTyCovariant Ty), RTy.selfRefsCov (toRTyCov s) = []
  | .array a => by simp [toRTyCov, RTy.selfRefsCov, selfRefs_toRTy a]
  -- | .task a => by simp [toRTyCov, RTy.selfRefsCov, selfRefs_toRTy a]
  -- | .promise a => by simp [toRTyCov, RTy.selfRefsCov, selfRefs_toRTy a]
  | .thunk a => by simp [toRTyCov, RTy.selfRefsCov, selfRefs_toRTy a]
  | .lazy a => by simp [toRTyCov, RTy.selfRefsCov, selfRefs_toRTy a]

/-- The same, for a list of types. -/
theorem selfRefsList_toRTyList : ∀ (l : List Ty), RTy.selfRefsList (toRTyList l) = []
  | [] => by simp [toRTyList, RTy.selfRefsList]
  | a :: as => by
      simp [toRTyList, RTy.selfRefsList, selfRefs_toRTy a, selfRefsList_toRTyList as]

/-- The same, for the constructors of a layout. -/
theorem selfRefsCtors_toRTyCtors :
    ∀ (l : List (List Ty)), RTy.selfRefsCtors (toRTyCtors l) = []
  | [] => by simp [toRTyCtors, RTy.selfRefsCtors]
  | fs :: l => by
      simp [toRTyCtors, RTy.selfRefsCtors, selfRefsList_toRTyList fs,
        selfRefsCtors_toRTyCtors l]

/-- The same, for the fields of a record. -/
theorem selfRefsA2_toRTyA2 :
    ∀ (fs : LeanRecordSchema Ty), RTy.selfRefsA2 (toRTyA2 fs) = []
  | ⟨a, b, rest⟩ => by
      simp [toRTyA2, RTy.selfRefsA2, selfRefs_toRTy a, selfRefs_toRTy b,
        selfRefsList_toRTyList rest]

/-- The same, for the fields of a constructor that has at least one. -/
theorem selfRefsNE_toRTyNE : ∀ (f : NonEmptyList Ty), RTy.selfRefsNE (toRTyNE f) = []
  | ⟨a, as⟩ => by
      simp [toRTyNE, RTy.selfRefsNE, selfRefs_toRTy a, selfRefsList_toRTyList as]

/-- The same, for the constructors of a tagged union. -/
theorem selfRefsTU_toRTyTU :
    ∀ (l : LeanTaggedUnionSchema Ty), RTy.selfRefsTU (toRTyTU l) = []
  | .payloadFirst f n r => by
      simp [toRTyTU, RTy.selfRefsTU, selfRefsNE_toRTyNE f, selfRefsList_toRTyList n,
        selfRefsCtors_toRTyCtors r]
  | .skip rest => by simp [toRTyTU, RTy.selfRefsTU, selfRefsCP_toRTyCP rest]

/-- The same, for the constructors that follow a field-less one. -/
theorem selfRefsCP_toRTyCP :
    ∀ (c : CtorsWithPayload Ty), RTy.selfRefsCP (toRTyCP c) = []
  | .here f r => by
      simp [toRTyCP, RTy.selfRefsCP, selfRefsNE_toRTyNE f, selfRefsCtors_toRTyCtors r]
  | .skip rest => by simp [toRTyCP, RTy.selfRefsCP, selfRefsCP_toRTyCP rest]

end

/-- A closed type mentions no member of the declaration it is placed in: it makes no
    self-reference at all. -/
theorem hasSelf_toRTy (t : Ty) : RTy.hasSelf (toRTy t) = false := by
  simp [RTy.hasSelf, selfRefs_toRTy t]

/-- The same, for an invariant type former. -/
theorem hasSelfCov_toRTyCov (s : LeanPrimTyCovariant Ty) :
    RTy.hasSelfCov (toRTyCov s) = false := by
  simp [RTy.hasSelfCov, selfRefsCov_toRTyCov s]

/-- The same, for a list of types. -/
theorem hasSelfList_toRTyList (l : List Ty) : RTy.hasSelfList (toRTyList l) = false := by
  simp [RTy.hasSelfList, selfRefsList_toRTyList l]

/-- The same, for the constructors of a layout. -/
theorem hasSelfCtors_toRTyCtors (l : List (List Ty)) :
    RTy.hasSelfCtors (toRTyCtors l) = false := by
  simp [RTy.hasSelfCtors, selfRefsCtors_toRTyCtors l]

/-- The same, for the fields of a record. -/
theorem hasSelfA2_toRTyA2 (fs : LeanRecordSchema Ty) :
    RTy.hasSelfA2 (toRTyA2 fs) = false := by
  simp [RTy.hasSelfA2, selfRefsA2_toRTyA2 fs]

/-- The same, for the fields of a constructor that has at least one. -/
theorem hasSelfNE_toRTyNE (f : NonEmptyList Ty) : RTy.hasSelfNE (toRTyNE f) = false := by
  simp [RTy.hasSelfNE, selfRefsNE_toRTyNE f]

/-- The same, for the constructors of a tagged union. -/
theorem hasSelfTU_toRTyTU (l : LeanTaggedUnionSchema Ty) :
    RTy.hasSelfTU (toRTyTU l) = false := by
  simp [RTy.hasSelfTU, selfRefsTU_toRTyTU l]

/-- The same, for the constructors that follow a field-less one. -/
theorem hasSelfCP_toRTyCP (c : CtorsWithPayload Ty) :
    RTy.hasSelfCP (toRTyCP c) = false := by
  simp [RTy.hasSelfCP, selfRefsCP_toRTyCP c]


mutual

/-- A closed type is a well-formed payload: it is well formed as a type, and the one
    extra condition a payload is under — no `.self` to the left of an arrow — is met
    vacuously, since it has no `.self` at all. -/
theorem wf_toRTy : ∀ (t : Ty), RTy.wf (toRTy t) = true
  | .prim _ => by simp [toRTy, RTy.wf]
  | .fn a b => by simp [toRTy, RTy.wf, hasSelf_toRTy a, wf_toRTy a, wf_toRTy b]
  | .primCovariant s => by simp [toRTy, RTy.wf, wfCov_toRTyCov s]
  | .enum _ => by simp [toRTy, RTy.wf]
  | .record fs => by simp [toRTy, RTy.wf, wfA2_toRTyA2 fs]
  | .taggedUnion l => by simp [toRTy, RTy.wf, wfTU_toRTyTU l]
  | .recTaggedUnion l => by simpa [toRTy, RTy.Wf] using l.h_wf
  | .recObject fs => by simpa [toRTy, RTy.Wf] using fs.h_wf
  | .recAlias b => by simpa [toRTy, RTy.Wf] using b.h_wf
  | .mutualRecursiveFamily f => by simpa [toRTy, RTy.Wf] using f.h_wf
  | .withComputedFields b _ => by simp [toRTy, RTy.wf, wf_toRTy b]

/-- The same, for an invariant type former. -/
theorem wfCov_toRTyCov : ∀ (s : LeanPrimTyCovariant Ty), RTy.wfCov (toRTyCov s) = true
  | .array a => by simp [toRTyCov, RTy.wfCov, wf_toRTy a]
  -- | .task a => by simp [toRTyCov, RTy.wfCov, wf_toRTy a]
  -- | .promise a => by simp [toRTyCov, RTy.wfCov, wf_toRTy a]
  | .thunk a => by simp [toRTyCov, RTy.wfCov, wf_toRTy a]
  | .lazy a => by simp [toRTyCov, RTy.wfCov, wf_toRTy a]

/-- The same, for a list of types. -/
theorem wfList_toRTyList : ∀ (l : List Ty), RTy.wfList (toRTyList l) = true
  | [] => by simp [toRTyList, RTy.wfList]
  | a :: as => by simp [toRTyList, RTy.wfList, wf_toRTy a, wfList_toRTyList as]

/-- The same, for the constructors of a layout. -/
theorem wfCtors_toRTyCtors : ∀ (l : List (List Ty)), RTy.wfCtors (toRTyCtors l) = true
  | [] => by simp [toRTyCtors, RTy.wfCtors]
  | fs :: l => by
      simp [toRTyCtors, RTy.wfCtors, wfList_toRTyList fs, wfCtors_toRTyCtors l]

/-- The same, for the fields of a record. -/
theorem wfA2_toRTyA2 : ∀ (fs : LeanRecordSchema Ty), RTy.wfA2 (toRTyA2 fs) = true
  | ⟨a, b, rest⟩ => by
      simp [toRTyA2, RTy.wfA2, wf_toRTy a, wf_toRTy b, wfList_toRTyList rest]

/-- The same, for the fields of a constructor that has at least one. -/
theorem wfNE_toRTyNE : ∀ (f : NonEmptyList Ty), RTy.wfNE (toRTyNE f) = true
  | ⟨a, as⟩ => by simp [toRTyNE, RTy.wfNE, wf_toRTy a, wfList_toRTyList as]

/-- The same, for the constructors of a tagged union. -/
theorem wfTU_toRTyTU : ∀ (l : LeanTaggedUnionSchema Ty), RTy.wfTU (toRTyTU l) = true
  | .payloadFirst f n r => by
      simp [toRTyTU, RTy.wfTU, wfNE_toRTyNE f, wfList_toRTyList n, wfCtors_toRTyCtors r]
  | .skip rest => by simp [toRTyTU, RTy.wfTU, wfCP_toRTyCP rest]

/-- The same, for the constructors that follow a field-less one. -/
theorem wfCP_toRTyCP : ∀ (c : CtorsWithPayload Ty), RTy.wfCP (toRTyCP c) = true
  | .here f r => by simp [toRTyCP, RTy.wfCP, wfNE_toRTyNE f, wfCtors_toRTyCtors r]
  | .skip rest => by simp [toRTyCP, RTy.wfCP, wfCP_toRTyCP rest]

end

/-- The recursive tagged union `List α` is well formed for **every** element type: it
    mentions itself (in the tail of `cons`), it points only at itself, and `nil` builds
    a value without one, so it has values. -/
theorem list_wf (α : Ty) :
    RTy.wf (.recTaggedUnion (.skip (.here ⟨toRTy α, [.self]⟩ []))) = true := by
  simp [RTy.wf, recTUWf, RTy.hasSelfTU, selfRefsPlain, RTy.selfRefsTU, RTy.selfRefsCP,
    RTy.selfRefsNE, RTy.selfRefsList, RTy.selfRefs, selfRefs_toRTy α, famAllInhabited,
    famInhabited, famInhabIter, famInhabStep, LeanFamMemberSchema_RTy.inhabWith,
    RTy.inhabWithTU, RTy.wfTU, RTy.wfCP, RTy.wfNE, RTy.wfList, RTy.wfCtors,
    RTy.selfRefsCtors, wf_toRTy α]

/-- `List α`: constructor `0` (`nil`) carries nothing and constructor `1` (`cons`)
    carries the head of type `α` and tail of type `List α`. -/
def list (α : Ty) : Ty :=
  Ty.recTaggedUnion ⟨.skip (.here ⟨toRTy α, [.self]⟩ []), list_wf α⟩

/-! ## The shapes that may carry computed fields

`Ty.withComputedFields` takes the declaration and the types of the values it caches.
Which declaration shapes that is for is said by the seven names below, one per datatype
shape; they are `@[match_pattern]`, so a traversal may match on
`.recTaggedUnion_withComputedFields l cs` directly. -/

/-- An enum that caches values computed from itself. -/
@[match_pattern] abbrev enum_withComputedFields
    (s : LeanEnumSchema) (cs : NonEmptyList LeanPrimTy) : Ty :=
  .withComputedFields (.enum s) cs
/-- A record that caches values computed from itself. -/
@[match_pattern] abbrev record_withComputedFields
    (fs : LeanRecordSchema Ty) (cs : NonEmptyList LeanPrimTy) : Ty :=
  .withComputedFields (.record fs) cs
/-- A tagged union that caches values computed from itself. -/
@[match_pattern] abbrev taggedUnion_withComputedFields
    (l : LeanTaggedUnionSchema Ty) (cs : NonEmptyList LeanPrimTy) : Ty :=
  .withComputedFields (.taggedUnion l) cs
/-- A recursive tagged union that caches values computed from itself — the shape of
    `Lean.Name`, whose `hash` is a computed field. -/
@[match_pattern] abbrev recTaggedUnion_withComputedFields
    (l : LeanTaggedUnionSchemaSealed) (cs : NonEmptyList LeanPrimTy) : Ty :=
  .withComputedFields (.recTaggedUnion l) cs
/-- A recursive record that caches values computed from itself. -/
@[match_pattern] abbrev recObject_withComputedFields
    (fs : LeanRecordSchemaSealed) (cs : NonEmptyList LeanPrimTy) : Ty :=
  .withComputedFields (.recObject fs) cs
/-- A recursive newtype that caches values computed from itself. -/
@[match_pattern] abbrev recAlias_withComputedFields
    (b : RTySealed) (cs : NonEmptyList LeanPrimTy) : Ty :=
  .withComputedFields (.recAlias b) cs
/-- A mutual recursive family that caches values computed from itself. -/
@[match_pattern] abbrev mutualRecursiveFamily_withComputedFields
    (f : LeanMutualRecFamilySealed) (cs : NonEmptyList LeanPrimTy) : Ty :=
  .withComputedFields (.mutualRecursiveFamily f) cs

/-- A schema with computed fields, at this layer: the type of a cached value is a
    terminal type, since what a declaration caches is a scalar (`Lean.Name.hash` is a
    `UInt64`). -/
abbrev EnumWithComputedFields := LeanEnumWithComputedFieldsSchema LeanPrimTy
/-- A record with computed fields, at this layer. -/
abbrev RecordWithComputedFields := LeanRecordWithComputedFieldsSchema Ty LeanPrimTy
/-- A tagged union with computed fields, at this layer. -/
abbrev TaggedUnionWithComputedFields := LeanTaggedUnionWithComputedFieldsSchema Ty LeanPrimTy

/-- The type of a schema with computed fields. -/
abbrev ofEnumWithComputedFields (s : EnumWithComputedFields) : Ty :=
  .enum_withComputedFields s.base s.computed
/-- The same, for a record. -/
abbrev ofRecordWithComputedFields (s : RecordWithComputedFields) : Ty :=
  .record_withComputedFields s.base s.computed
/-- The same, for a tagged union. -/
abbrev ofTaggedUnionWithComputedFields (s : TaggedUnionWithComputedFields) : Ty :=
  .taggedUnion_withComputedFields s.base s.computed

/-! ## `Lean.Name`

`Name` is the recursive tagged union `anonymous | str (pre : Name) (str : String) |
num (pre : Name) (i : Nat)`, with one computed field: the `hash : UInt64` it caches. -/

/-- The constructors of `Lean.Name`, in declaration order: `anonymous` carries nothing,
    `str` carries the prefix and a `String`, `num` the prefix and a `Nat`. -/
abbrev nameCtors : LeanTaggedUnionSchema RTy :=
  .skip (.here ⟨.self, [.prim .string]⟩ [[.self, .prim .nat]])

/-- `Lean.Name`: the recursive tagged union above, caching its own `hash`. -/
abbrev name : Ty := .recTaggedUnion_withComputedFields ⟨nameCtors, by decide⟩ ⟨.uint64, []⟩

end Ty

end LeanScript

end
