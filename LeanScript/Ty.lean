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
| `inductive T \| leaf \| node : T → T → T`          | `.recTaggedUnion (.skip (.here ⟨.self 0, [.self 0]⟩ []))` |
| `structure Tree where n : Nat; kids : Array Tree`  | `.recObject ⟨.nat, .array (.self 0), []⟩` |
| `structure Rose where kids : Array Rose`           | `.recAlias (.array (.self 0))`         |
| a mutual block                                     | `.mutualRecursiveFamily f`             |

## `.self` is available in the recursive shapes and nowhere else

The recursive shapes — `recTaggedUnion`, `recObject`, `recAlias` and
`mutualRecursiveFamily` — are the *binders* of the type language: their children are
`RTy`s, the types *inside a recursive declaration*, and `RTy.self i` is an occurrence of
member `i` of that declaration (`i = 0` unless the binder is a mutual family).  The
other shapes carry ordinary `Ty`s, which have no `.self` constructor at all, so a type
outside a recursive declaration cannot mention one.

`RTy` mirrors `Ty`, so anything may appear inside a recursive declaration — a `Nat`, an
`Option Tree`, an `Array Tree`.  Where an `RTy` is itself a *recursive* shape, it opens
a new scope: the `.self` of its children is that inner declaration, exactly as a nested
binder shadows an outer one.

That a recursive shape really does mention itself, and that the type it describes has
any values at all (`inductive Bad | mk : Bad → Bad` has none), are conditions on a whole
type rather than counting conditions on one payload — and they are carried by the
constructors all the same: each of the four recursive constructors takes a field
`RTy.wf … = true` (`LeanScript.RTyWf`), discharged by `by decide` for a type written out.
So there is no subtype of the well-formed types and no check to forget: a degenerate
recursive declaration is not a `Ty` that fails a test, it is not a `Ty`.

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
      holding the types of its fields, in which `RTy.self 0` is an occurrence of the
      declaration itself.  In JS: `{ tag: …, … }`. -/
  | recTaggedUnion : (l : LeanTaggedUnionSchema RTy) →
      (h : RTy.wf (.recTaggedUnion l) = true := by decide) → Ty
  /-- A recursive single-constructor type with ≥ 2 fields
      (`structure Tree where n : Nat; kids : Array Tree`), in which `RTy.self 0` is an
      occurrence of the declaration itself.  In JS: `{ tag: 0, _1: …, _2: … }`. -/
  | recObject : (fs : LeanRecordSchema RTy) →
      (h : RTy.wf (.recObject fs) = true := by decide) → Ty
  /-- A recursive **newtype**, with the wrapper erased
      (`structure Rose where kids : Array Rose`): the fixed point of the single field's
      type.  In JS a `Rose` is just `[…]`, an array of arrays of …, with no object
      wrapper — `[[], [[], []]]` is a `Rose`. -/
  | recAlias : (b : RTy) → (h : RTy.wf (.recAlias b) = true := by decide) → Ty
  /-- One member of a genuinely mutual recursive family: the bodies of *all* of its
      members, in declaration order, and which of them this type is — held as a zipper,
      so the member number is in range and the family has two members or more by
      construction.  Inside the bodies, `RTy.self i` is an occurrence of member `i`, so
      a type never points outside its family. -/
  | mutualRecursiveFamily : (f : LeanMutualRecFamily RTy) →
      (h : RTy.wf (.mutualRecursiveFamily f) = true := by decide) → Ty

namespace Ty

/-! ## Deciding equality

`Ty` holds schemas of types, and schemas of schemas of types, which no `deriving`
handler covers, so the instance is written out: a structural `Ty.beq` over the whole
family of types and schemas, and the two lemmas that make it equality. -/

mutual

/-- Structural equality of two closed types. -/
def beq : Ty → Ty → Bool
  | .prim p, .prim q => p == q
  | .fn a b, .fn c d => Ty.beq a c && Ty.beq b d
  | .primCovariant s, .primCovariant t => Ty.beqCov s t
  | .enum a, .enum b => a == b
  | .record a, .record b => Ty.beqA2 a b
  | .taggedUnion a, .taggedUnion b => Ty.beqTU a b
  | .recTaggedUnion a _, .recTaggedUnion b _ => RTy.beqTU a b
  | .recObject a _, .recObject b _ => RTy.beqA2 a b
  | .recAlias a _, .recAlias b _ => RTy.beq a b
  | .mutualRecursiveFamily a _, .mutualRecursiveFamily b _ => RTy.beqFamily a b
  | _, _ => false

/-- Structural equality of two invariant type formers over closed types. -/
def beqCov : LeanPrimTyCovariant Ty → LeanPrimTyCovariant Ty → Bool
  | .array a, .array b => Ty.beq a b
  | .task a, .task b => Ty.beq a b
  | .promise a, .promise b => Ty.beq a b
  | .thunk a, .thunk b => Ty.beq a b
  | .lazy a, .lazy b => Ty.beq a b
  | _, _ => false

/-- `Ty.beq`, on a list of closed types. -/
def beqList : List Ty → List Ty → Bool
  | [], [] => true
  | a :: as, b :: bs => Ty.beq a b && Ty.beqList as bs
  | _, _ => false

/-- `Ty.beq`, on the constructors of a closed layout. -/
def beqCtors : List (List Ty) → List (List Ty) → Bool
  | [], [] => true
  | a :: as, b :: bs => Ty.beqList a b && Ty.beqCtors as bs
  | _, _ => false

/-- `Ty.beq`, on the fields of a record of closed types. -/
def beqA2 : LeanRecordSchema Ty → LeanRecordSchema Ty → Bool
  | ⟨a1, a2, as⟩, ⟨b1, b2, bs⟩ => Ty.beq a1 b1 && Ty.beq a2 b2 && Ty.beqList as bs

/-- `Ty.beq`, on the fields of a constructor that has at least one. -/
def beqNE : NonEmptyList Ty → NonEmptyList Ty → Bool
  | ⟨a, as⟩, ⟨b, bs⟩ => Ty.beq a b && Ty.beqList as bs

/-- `Ty.beq`, on the constructors of a tagged union of closed types. -/
def beqTU : LeanTaggedUnionSchema Ty → LeanTaggedUnionSchema Ty → Bool
  | .payloadFirst f n r, .payloadFirst g m s =>
      Ty.beqNE f g && Ty.beqList n m && Ty.beqCtors r s
  | .skip a, .skip b => Ty.beqCP a b
  | _, _ => false

/-- `Ty.beq`, on the constructors that follow a field-less one. -/
def beqCP : CtorsWithPayload Ty → CtorsWithPayload Ty → Bool
  | .here f r, .here g s => Ty.beqNE f g && Ty.beqCtors r s
  | .skip a, .skip b => Ty.beqCP a b
  | _, _ => false

end

mutual

/-- Closed types that compare equal are equal. -/
theorem eq_of_beq : ∀ {a b : Ty}, Ty.beq a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [Ty.beq]
  case fn.fn => exact ⟨Ty.eq_of_beq h.1, Ty.eq_of_beq h.2⟩
  case primCovariant.primCovariant => exact Ty.eq_of_beqCov h
  case record.record => exact Ty.eq_of_beqA2 h
  case taggedUnion.taggedUnion => exact Ty.eq_of_beqTU h
  case recTaggedUnion.recTaggedUnion => exact RTy.eq_of_beqTU h
  case recObject.recObject => exact RTy.eq_of_beqA2 h
  case recAlias.recAlias => exact RTy.eq_of_beq h
  case mutualRecursiveFamily.mutualRecursiveFamily => exact RTy.eq_of_beqFamily h

/-- The same, for an invariant type former over closed types. -/
theorem eq_of_beqCov : ∀ {a b : LeanPrimTyCovariant Ty}, Ty.beqCov a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [Ty.beqCov] <;> exact Ty.eq_of_beq h

/-- The same, for a list of closed types. -/
theorem eq_of_beqList : ∀ {a b : List Ty}, Ty.beqList a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [Ty.beqList]
  exact ⟨Ty.eq_of_beq h.1, Ty.eq_of_beqList h.2⟩

/-- The same, for the constructors of a closed layout. -/
theorem eq_of_beqCtors : ∀ {a b : List (List Ty)}, Ty.beqCtors a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [Ty.beqCtors]
  exact ⟨Ty.eq_of_beqList h.1, Ty.eq_of_beqCtors h.2⟩

/-- The same, for the fields of a record of closed types. -/
theorem eq_of_beqA2 : ∀ {a b : LeanRecordSchema Ty}, Ty.beqA2 a b = true → a = b := by
  intro a b h
  cases a
  cases b
  simp_all [Ty.beqA2]
  exact ⟨Ty.eq_of_beq h.1.1, Ty.eq_of_beq h.1.2, Ty.eq_of_beqList h.2⟩

/-- The same, for the fields of a constructor that has at least one. -/
theorem eq_of_beqNE : ∀ {a b : NonEmptyList Ty}, Ty.beqNE a b = true → a = b := by
  intro a b h
  cases a
  cases b
  simp_all [Ty.beqNE]
  exact ⟨Ty.eq_of_beq h.1, Ty.eq_of_beqList h.2⟩

/-- The same, for the constructors of a tagged union of closed types. -/
theorem eq_of_beqTU : ∀ {a b : LeanTaggedUnionSchema Ty}, Ty.beqTU a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [Ty.beqTU]
  case payloadFirst.payloadFirst =>
    exact ⟨Ty.eq_of_beqNE h.1.1, Ty.eq_of_beqList h.1.2, Ty.eq_of_beqCtors h.2⟩
  case skip.skip => exact Ty.eq_of_beqCP h

/-- The same, for the constructors that follow a field-less one. -/
theorem eq_of_beqCP : ∀ {a b : CtorsWithPayload Ty}, Ty.beqCP a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [Ty.beqCP]
  case here.here => exact ⟨Ty.eq_of_beqNE h.1, Ty.eq_of_beqCtors h.2⟩
  case skip.skip => exact Ty.eq_of_beqCP h

end

mutual

/-- Every closed type compares equal to itself. -/
theorem beq_refl : ∀ (a : Ty), Ty.beq a a = true
  | .prim _ => by simp [Ty.beq]
  | .fn a b => by simp [Ty.beq, Ty.beq_refl a, Ty.beq_refl b]
  | .primCovariant s => by simp [Ty.beq, Ty.beqCov_refl s]
  | .enum _ => by simp [Ty.beq]
  | .record a => by simp [Ty.beq, Ty.beqA2_refl a]
  | .taggedUnion a => by simp [Ty.beq, Ty.beqTU_refl a]
  | .recTaggedUnion a _ => by simp [Ty.beq, RTy.beqTU_refl a]
  | .recObject a _ => by simp [Ty.beq, RTy.beqA2_refl a]
  | .recAlias a _ => by simp [Ty.beq, RTy.beq_refl a]
  | .mutualRecursiveFamily a _ => by simp [Ty.beq, RTy.beqFamily_refl a]

/-- The same, for an invariant type former over closed types. -/
theorem beqCov_refl : ∀ (a : LeanPrimTyCovariant Ty), Ty.beqCov a a = true
  | .array a => by simp [Ty.beqCov, Ty.beq_refl a]
  | .task a => by simp [Ty.beqCov, Ty.beq_refl a]
  | .promise a => by simp [Ty.beqCov, Ty.beq_refl a]
  | .thunk a => by simp [Ty.beqCov, Ty.beq_refl a]
  | .lazy a => by simp [Ty.beqCov, Ty.beq_refl a]

/-- The same, for a list of closed types. -/
theorem beqList_refl : ∀ (a : List Ty), Ty.beqList a a = true
  | [] => by simp [Ty.beqList]
  | a :: as => by simp [Ty.beqList, Ty.beq_refl a, Ty.beqList_refl as]

/-- The same, for the constructors of a closed layout. -/
theorem beqCtors_refl : ∀ (a : List (List Ty)), Ty.beqCtors a a = true
  | [] => by simp [Ty.beqCtors]
  | a :: as => by simp [Ty.beqCtors, Ty.beqList_refl a, Ty.beqCtors_refl as]

/-- The same, for the fields of a record of closed types. -/
theorem beqA2_refl : ∀ (a : LeanRecordSchema Ty), Ty.beqA2 a a = true
  | ⟨a1, a2, as⟩ => by
      simp [Ty.beqA2, Ty.beq_refl a1, Ty.beq_refl a2, Ty.beqList_refl as]

/-- The same, for the fields of a constructor that has at least one. -/
theorem beqNE_refl : ∀ (a : NonEmptyList Ty), Ty.beqNE a a = true
  | ⟨f, fs⟩ => by simp [Ty.beqNE, Ty.beq_refl f, Ty.beqList_refl fs]

/-- The same, for the constructors of a tagged union of closed types. -/
theorem beqTU_refl : ∀ (a : LeanTaggedUnionSchema Ty), Ty.beqTU a a = true
  | .payloadFirst f n r => by
      simp [Ty.beqTU, Ty.beqNE_refl f, Ty.beqList_refl n, Ty.beqCtors_refl r]
  | .skip a => by simp [Ty.beqTU, Ty.beqCP_refl a]

/-- The same, for the constructors that follow a field-less one. -/
theorem beqCP_refl : ∀ (a : CtorsWithPayload Ty), Ty.beqCP a a = true
  | .here f r => by simp [Ty.beqCP, Ty.beqNE_refl f, Ty.beqCtors_refl r]
  | .skip a => by simp [Ty.beqCP, Ty.beqCP_refl a]

end

instance : DecidableEq Ty := fun a b =>
  decidable_of_iff (Ty.beq a b = true) ⟨Ty.eq_of_beq, fun h => h ▸ Ty.beq_refl a⟩

instance : BEq Ty := ⟨Ty.beq⟩
instance : ReflBEq Ty where
  rfl {a} := Ty.beq_refl a
instance : LawfulBEq Ty where
  eq_of_beq := by intro a b; exact eq_of_beq

/-! ## The shared type formers, as abbreviations

`Ty.primCovariant` is the only way to build an array, a list, a task, a promise or a
thunk, but writing `.primCovariant (.array α)` everywhere is noise, so each former is also
available directly under `Ty` and `RTy`.  They are `@[match_pattern]`, so `.array α` works
in a pattern as well as in a term. -/

/-- In JS: an array. -/
@[match_pattern] abbrev array (α : Ty) : Ty := .primCovariant (.array α)
/-- In JS: `Promise<α>`. -/
@[match_pattern] abbrev task (α : Ty) : Ty := .primCovariant (.task α)
/-- In JS: `Promise<α>`. -/
@[match_pattern] abbrev promise (α : Ty) : Ty := .primCovariant (.promise α)
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

-- Precedence 70 matches your infixr operator
syntax:70 (priority := default + 10) "(" term,* ")" " ⇒ " term:70 : term

macro_rules
  | `(($[$xs],*) ⇒ $τ) => `(arrows [$xs,*] $τ)

-- #check (x, y, z) ⇒ τ      -- Ty (expands to arrows [x, y, z] τ)
-- #check (x, y) ⇒ z ⇒ τ     -- Ty (chains correctly)
-- #check (x) ⇒ τ            -- Ty (expands to arrows [x] τ = x ⇒ τ)
-- #check () ⇒ τ             -- Ty (expands to arrows [] τ = τ)

end Ty

end LeanScript

end
