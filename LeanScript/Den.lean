module

public import LeanScript.Ty.TyWfIn

@[expose] public section

set_option autoImplicit false

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

namespace LeanScript

/-!
# `Ty.Den`: what a type of the language *is*

The evaluator of `LeanScript.Term` is a **total Lean function**, so a value of the
language has to be a value of a Lean type.  This module says which Lean type: `Ty.Den τ`
is the type of the values of `τ`.

| `τ` | `Ty.Den τ` |
| :-- | :-- |
| `Ty.prim p` | `LeanScript.LeanPrimTy.denote p` — the Lean type of that leaf's literals |
| `σ ⇒ τ` | `Ty.Den σ → Ty.Den τ` — a **Lean** function, so there is no closure and no environment in a value |
| `Ty.array α` | `List (Ty.Den α)` |
| `Ty.thunk α`, `Ty.lazy α` | `Ty.Den α` — a delay carries nothing beyond the value it stands for; the two wrappers differ only in the code printed for them |
| `Ty.enum s` | `Fin s.nOfConstructors` — a constructor *number*, which is what the runtime holds |
| `Ty.record fs` | the product of its fields' denotations, in declaration order |
| `Ty.taggedUnion l` | a constructor number **with** that constructor's fields: `(t : Fin l.length) × Ty.DenAt l t` |

The four recursive shapes, and the two occurrence leaves `Ty.self` and
`Ty.familyMember`, denote `PEmpty`.  This is therefore a model of the language **without
recursive data**: it is consistent with taking a value of a recursive shape apart (there
is nothing to take apart) but not with building one, and `LeanScript.Term` does have
introduction forms for all four.  `LeanScript.Term.eval` is the evaluator *of this model*
and so carries `LeanScript.Term.NoRecMk`, the hypothesis that the term builds no such
value; see the section of `LeanScript.Eval` that states it.  Giving the recursive shapes
their values needs the least fixpoint of the functor a binder's payload describes, which
is a construction this module does not have yet.

Every definition here is written the way `LeanScript.Ty.beq` is — one function per shape
of the nested tree, all in one `mutual` block — so that each recursive call is on a
syntactic subterm and the whole family is *structurally* recursive.  That is also what
makes the equations hold definitionally, which the evaluator relies on.
-/

mutual

/-- The Lean type of the values of a type of the language. -/
@[reducible] def Ty.Den : Ty → Type
  | .self => PEmpty
  | .familyMember _ => PEmpty
  | .shape s => Ty.DenShape s
  | .recTaggedUnion _ => PEmpty
  | .recObject _ => PEmpty
  | .recAlias _ => PEmpty
  | .mutualRecursiveFamily _ => PEmpty

/-- `Ty.Den`, on a node. -/
@[reducible] def Ty.DenShape : TyShape Ty → Type
  | .prim p => p.denote
  | .fn a b => Ty.Den a → Ty.Den b
  | .primCovariant c => Ty.DenCov c
  | .enum s => Fin s.nOfConstructors
  | .record fs => Ty.DenRecord fs
  | .taggedUnion l => (t : Fin l.length) × Ty.DenAt l t.val

/-- `Ty.Den`, on an array, a thunk or a lazy value.  A delay denotes the value it stands
    for: a `Term` is a total function of its environment, so forcing it twice cannot give
    two answers, and memoisation is invisible here. -/
@[reducible] def Ty.DenCov : LeanPrimTyCovariant Ty → Type
  | .array a => List (Ty.Den a)
  | .thunk a => Ty.Den a
  | .lazy a => Ty.Den a

/-- `Ty.DenList`, on a list that has at least one entry. -/
@[reducible] def Ty.DenNE : NonEmptyList Ty → Type
  | ⟨a, as⟩ => Ty.Den a × Ty.DenList as

/-- `Ty.DenList`, on the fields of a record — of which there are at least two. -/
@[reducible] def Ty.DenRecord : LeanRecordSchema Ty → Type
  | ⟨a, b, rest⟩ => Ty.Den a × Ty.Den b × Ty.DenList rest

/-- The product of the denotations of a list of types, in order: an environment, the
    fields of a constructor, the arguments of a call. -/
@[reducible] def Ty.DenList : List Ty → Type
  | [] => PUnit
  | τ :: ts => Ty.Den τ × Ty.DenList ts

/-- The fields of constructor number `t` of a tagged union, as a product.  Out of range
    it is `PEmpty`, which is what makes a dispatch on a union exhaustive without a
    bound. -/
@[reducible] def Ty.DenAt : LeanTaggedUnionSchema Ty → Nat → Type
  | .payloadFirst fields _ _, 0 => Ty.DenNE fields
  | .payloadFirst _ next _, 1 => Ty.DenList next
  | .payloadFirst _ _ rest, n + 2 => Ty.DenAtList rest n
  | .skip _, 0 => PUnit
  | .skip rest, n + 1 => Ty.DenAtCP rest n

/-- `Ty.DenAt`, on the constructors that follow a field-less one. -/
@[reducible] def Ty.DenAtCP : CtorsWithPayload Ty → Nat → Type
  | .here fields _, 0 => Ty.DenNE fields
  | .here _ rest, n + 1 => Ty.DenAtList rest n
  | .skip _, 0 => PUnit
  | .skip rest, n + 1 => Ty.DenAtCP rest n

/-- `Ty.DenAt`, on a plain list of constructors. -/
@[reducible] def Ty.DenAtList : List (List Ty) → Nat → Type
  | [], _ => PEmpty
  | fs :: _, 0 => Ty.DenList fs
  | _ :: rest, n + 1 => Ty.DenAtList rest n

end

/-- The values of a tagged union: a constructor number, with exactly that constructor's
    fields.  There is no way to build one whose tag is out of range, and no way to read a
    field of a constructor other than the one the value holds. -/
abbrev Ty.DenTU (l : LeanTaggedUnionSchema Ty) : Type :=
  (t : Fin l.length) × Ty.DenAt l t.val

/-! ## The fields of a constructor, named by number

`LeanScript.Term.taggedUnion_mk` and `LeanScript.TaggedUnionSomeCases` name a constructor
by a number `t` with a proof `t < l.length`, and speak of its fields as
`Ty.DenList (l.get t ht)`; a value holds them as `Ty.DenAt l t`.  The two are the same
type — that is `Ty.denAt_eq` — and `Ty.DenTU.mk` and `Ty.DenTU.field?` are the two
directions of that identification. -/

/-- The fields of a constructor that has at least one are the product of their
    denotations.  This is not definitional — `Ty.DenNE` is a case analysis on the schema,
    and a schema in hand is a variable rather than a pair — so an evaluator that has a
    `Ty.DenNE` and wants an environment `cast`s along it. -/
theorem Ty.denNE_eq (xs : NonEmptyList Ty) : Ty.DenNE xs = Ty.DenList xs.toList := by
  cases xs; rfl

/-- The fields of a record are the product of their denotations, in declaration order. -/
theorem Ty.denRecord_eq (fs : LeanRecordSchema Ty) :
    Ty.DenRecord fs = Ty.DenList fs.toList := by
  cases fs; rfl

theorem Ty.denAtList_eq : ∀ (l : List (List Ty)) (t : Nat) (ht : t < l.length),
    Ty.DenAtList l t = Ty.DenList l[t]
  | [], _, ht => absurd ht (by simp)
  | _ :: _, 0, _ => rfl
  | _ :: rest, n + 1, ht => Ty.denAtList_eq rest n (by simpa using ht)

theorem Ty.denAtCP_eq : ∀ (c : CtorsWithPayload Ty) (t : Nat) (ht : t < c.toList.length),
    Ty.DenAtCP c t = Ty.DenList c.toList[t]
  | .here fields _, 0, _ => by cases fields; rfl
  | .here _ rest, n + 1, ht =>
      Ty.denAtList_eq rest n (by simpa [CtorsWithPayload.toList] using ht)
  | .skip _, 0, _ => rfl
  | .skip rest, n + 1, ht =>
      Ty.denAtCP_eq rest n (by simpa [CtorsWithPayload.toList] using ht)

theorem Ty.denAt_eq : ∀ (l : LeanTaggedUnionSchema Ty) (t : Nat) (ht : t < l.length),
    Ty.DenAt l t = Ty.DenList (l.get t ht)
  | .payloadFirst fields _ _, 0, _ => by cases fields; rfl
  | .payloadFirst _ _ _, 1, _ => rfl
  | .payloadFirst _ _ rest, n + 2, ht => by
      simp only [LeanTaggedUnionSchema.get, LeanTaggedUnionSchema.toList]
      exact Ty.denAtList_eq rest n (by
        simp only [LeanTaggedUnionSchema.length] at ht; omega)
  | .skip _, 0, _ => rfl
  | .skip rest, n + 1, ht => by
      simp only [LeanTaggedUnionSchema.get, LeanTaggedUnionSchema.toList]
      exact Ty.denAtCP_eq rest n (by
        simp only [LeanTaggedUnionSchema.length] at ht
        simpa using ht)

/-- A value of a tagged union: constructor `t`, with its fields. -/
def Ty.DenTU.mk {l : LeanTaggedUnionSchema Ty} (t : Nat) (ht : t < l.length)
    (fields : Ty.DenList (l.get t ht)) : Ty.DenTU l :=
  ⟨⟨t, ht⟩, cast (Ty.denAt_eq l t ht).symm fields⟩

/-- The fields of a value of a tagged union **if** it is the value of constructor `t`,
    and nothing if it is the value of another constructor. -/
def Ty.DenTU.field? {l : LeanTaggedUnionSchema Ty} (t : Nat) (ht : t < l.length)
    (v : Ty.DenTU l) : Option (Ty.DenList (l.get t ht)) :=
  if h : v.1.val = t then
    some (cast (by subst h; exact Ty.denAt_eq l _ ht) v.2)
  else
    none

/-- Reading the fields of the constructor a value was built with gives them back. -/
theorem Ty.DenTU.field?_mk {l : LeanTaggedUnionSchema Ty} (t : Nat) (ht : t < l.length)
    (fields : Ty.DenList (l.get t ht)) :
    Ty.DenTU.field? t ht (Ty.DenTU.mk t ht fields) = some fields := by
  show (if _ : t = t then _ else _) = _
  simp only [↓reduceDIte]
  exact congrArg some ((cast_cast _ _ _).trans (cast_eq _ _))

/-- Reading the fields of **another** constructor gives nothing. -/
theorem Ty.DenTU.field?_of_ne {l : LeanTaggedUnionSchema Ty} (t : Nat) (ht : t < l.length)
    (v : Ty.DenTU l) (h : v.1.val ≠ t) : Ty.DenTU.field? t ht v = none := by
  simp [Ty.DenTU.field?, h]

/-! ## The values of a type of the language

`LeanScript.Term` is indexed by `LeanScript.TyWf` — a tree **together with the proof that
it is a type** — so the evaluator wants the denotation of a bundle, of a list of bundles,
and of a schema of bundles.  Each of them is the denotation of the tree underneath, which
is what makes them *definitionally* the ones above: nothing new is denoted here, the
proofs are simply dropped. -/

/-- The Lean type of the values of a type of the language. -/
@[reducible] def TyWf.Den (τ : TyWf) : Type := Ty.Den τ.toTy

/-- The values of a list of types, as a product: an environment, the fields of a
    constructor, the arguments of a call. -/
@[reducible] def TyWf.DenList (ts : List TyWf) : Type := Ty.DenList (ts.map TyWf.toTy)

/-- The values of a record of types, in declaration order. -/
@[reducible] def TyWf.DenRecord (fs : LeanRecordSchema TyWf) : Type :=
  Ty.DenRecord (fs.map TyWf.toTy)

/-- The values of a tagged union of types: a constructor number with that constructor's
    fields. -/
@[reducible] def TyWf.DenTU (l : LeanTaggedUnionSchema TyWf) : Type :=
  Ty.DenTU (l.map TyWf.toTy)

/-- `TyWf.DenTU`, on the constructors that follow a field-less one. -/
@[reducible] def TyWf.DenAtCP (c : CtorsWithPayload TyWf) (t : Nat) : Type :=
  Ty.DenAtCP (c.map TyWf.toTy) t

/-- `TyWf.DenTU`, on a plain list of constructors. -/
@[reducible] def TyWf.DenAtList (cs : List (List TyWf)) (t : Nat) : Type :=
  Ty.DenAtList (cs.map (List.map TyWf.toTy)) t

/-- A value of a tagged union of types: constructor `t`, with its fields. -/
def TyWf.DenTU.mk {l : LeanTaggedUnionSchema TyWf} (t : Nat) (ht : t < l.length)
    (fields : TyWf.DenList (l.get t ht)) : TyWf.DenTU l :=
  Ty.DenTU.mk t (by simpa using ht)
    (cast (by rw [LeanTaggedUnionSchema.get_map]) fields)

/-- The fields of a value of a tagged union **if** it is the value of constructor `t`,
    and nothing if it is the value of another constructor. -/
def TyWf.DenTU.field? {l : LeanTaggedUnionSchema TyWf} (t : Nat) (ht : t < l.length)
    (v : TyWf.DenTU l) : Option (TyWf.DenList (l.get t ht)) :=
  (Ty.DenTU.field? t (by simpa using ht) v).map
    (cast (by rw [LeanTaggedUnionSchema.get_map]))

/-- Reading the fields of the constructor a value was built with gives them back. -/
theorem TyWf.DenTU.field?_mk {l : LeanTaggedUnionSchema TyWf} (t : Nat)
    (ht : t < l.length) (fields : TyWf.DenList (l.get t ht)) :
    TyWf.DenTU.field? t ht (TyWf.DenTU.mk t ht fields) = some fields := by
  simp only [TyWf.DenTU.field?, TyWf.DenTU.mk, Ty.DenTU.field?_mk, Option.map_some]
  exact congrArg some ((cast_cast _ _ _).trans (cast_eq _ _))

end LeanScript

end
