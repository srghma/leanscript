module

public import LeanScript.Ty.TyWfIn
public import LeanScript.Den.PFunctor
public import LeanScript.Den.IPFunctor

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
| `Ty.array α` | `Array (Ty.Den α)` |
| `Ty.thunk α`, `Ty.lazy α` | `Ty.Den α` — a delay carries nothing beyond the value it stands for; the two wrappers differ only in the code printed for them |
| `Ty.enum s` | `Fin s.nOfConstructors` — a constructor *number*, which is what the runtime holds |
| `Ty.record fs` | the product of its fields' denotations, in declaration order, with no trailing `PUnit`: `⟨α, β, []⟩` is `Ty.Den α × Ty.Den β` |
| `Ty.taggedUnion l` | a constructor number **with** that constructor's fields: `(t : Fin l.length) × Ty.DenAt l t` |
| `Ty.recTaggedUnion l` | a **W-tree**: a node is a constructor number with that constructor's fields with their occurrences of the union blanked out, and one subtree per occurrence |
| `Ty.recObject fs` | a **W-tree**: a node is the record's fields with its occurrences of itself blanked out, and one subtree per occurrence |
| `Ty.recAlias b` | a **W-tree**: a node is the body with its occurrences of the newtype blanked out, and one subtree per occurrence |
| `Ty.mutualRecursiveFamily f` | an **indexed W-tree**: a node of member `i` is that member's value with its occurrences of members blanked out, and one subtree per occurrence, rooted at the member it names |

## Recursive shapes: containers

Every type is read as a **container** (`PFunctor`, in `LeanScript.Den.PFunctor`):
`Ty.toPFunctor τ` has a type of shapes and, for each shape, a type of *holes* — the places
where the shape holds an occurrence `Ty.self` of the binder it is written under.  A
closed type has no holes, the domain of an arrow is used as a type (`Ty.WfIn` keeps
`Ty.self` out of it), and `Ty.Den τ` is the type of shapes, `(Ty.toPFunctor τ).A`.  Every
equation of the table holds by `rfl`.

A recursive tagged union is then the least fixpoint of the container of its
constructors, which is its W-type (`WType`).  `LeanScript.Den.Rec` relates a
node of it to the constructor's *unfolded* fields (`Ty.roll`, `Ty.unroll`,
`Ty.DenRec.mk`, `Ty.DenRec.unfold`), which is what the evaluator's introduction form and
eliminators use.

A recursive record and a recursive newtype are read the same way: the least fixpoint of
the container of the record's fields (`Ty.toPFunctorRecord`) and of the newtype's body,
so each denotes a W-type too, and `LeanScript.Den.Rec` relates a node of it to the
*unfolded* fields or body (`Ty.DenObj.mk`/`unfold`, `Ty.DenAlias.mk`/`unfold`).  A record
or newtype that could only be built from an occurrence of itself has no finite value, and
its W-type is empty, which is the right answer: `ty_wf` rejects those anyway.

A **mutual family** (`Ty.mutualRecursiveFamily f`) is the least fixpoint of *one container
per member*, whose holes are its occurrences `Ty.familyMember j` of members: an indexed
polynomial functor (`LeanScript.IPFunctor`, in `LeanScript.Den.IPFunctor`), which records
the member each hole holds.  `Ty.toIPF` is the container of a type written in the scope
of a family, `Ty.toIPFFamily f` the list of containers of `f`'s members, and the values of
the family are the indexed W-tree `FamW (Ty.toIPFFamily f) f.memberIdx` rooted at the
member `f` selects.  `LeanScript.Den.Family` relates a node of it to the member's unfolded
constructors, fields or body (`Ty.DenFam.mk`, `Ty.DenFam.unfold`).

The occurrence leaves are not types on their own: `Ty.familyMember` denotes `PEmpty`, and
`Ty.self`, which only occurs outside a binder in an ill-formed tree, denotes `PUnit`, the
one hole.  Every *closed* type has values, so `LeanScript.Term.eval` interprets every term.

Every definition here is written the way `LeanScript.Ty.beq` is — one function per shape
of the nested tree, all in one `mutual` block — so that each recursive call is on a
syntactic subterm and the whole family is *structurally* recursive.  That is also what
makes the equations hold definitionally, which the evaluator relies on.
-/

mutual

/-- The container a type of the language describes: its values are the shapes, and the
    holes of a shape are the places where it holds an occurrence `Ty.self` of the binder
    it is written under.  A closed type has no holes.  See the section header. -/
@[reducible] def Ty.toPFunctor : Ty → PFunctor.{0, 0}
  | .self => ⟨PUnit, fun _ => PUnit⟩
  | .familyMember _ => PFunctor.const PEmpty
  | .shape s => Ty.toPFunctorShape s
  | .recTaggedUnion l => PFunctor.mu (PFunctor.sigma (Fin l.length) (fun t => Ty.toPFunctorAt l t.val))
  | .recObject fs => PFunctor.mu (Ty.toPFunctorRecord fs)
  | .recAlias b => PFunctor.mu (Ty.toPFunctor b)
  | .mutualRecursiveFamily f => PFunctor.const (FamW (Ty.toIPFFamily f) f.memberIdx)

/-- `Ty.toPFunctor`, on a node.  The domain of an arrow is used as a type — its holes are
    ignored, and `LeanScript.Ty.WfIn` keeps `Ty.self` out of it anyway. -/
@[reducible] def Ty.toPFunctorShape : TyShape Ty → PFunctor.{0, 0}
  | .prim p => PFunctor.const p.denote
  | .fn a b => PFunctor.pi (Ty.toPFunctor a).A (Ty.toPFunctor b)
  | .primCovariant c => Ty.toPFunctorCov c
  | .enum s => PFunctor.const (Fin s.nOfConstructors)
  | .record fs => Ty.toPFunctorRecord fs
  | .taggedUnion l => PFunctor.sigma (Fin l.length) (fun t => Ty.toPFunctorAt l t.val)

/-- `Ty.toPFunctor`, on an array, a thunk or a lazy value. -/
@[reducible] def Ty.toPFunctorCov : LeanPrimTyCovariant Ty → PFunctor.{0, 0}
  | .array a => PFunctor.array (Ty.toPFunctor a)
  | .thunk a => Ty.toPFunctor a
  | .lazy a => Ty.toPFunctor a

/-- The fields of a constructor that has at least one, as a tuple (`Ty.toPFunctorFields`):
    a single field is that field itself, and there is no trailing `PUnit`. -/
@[reducible] def Ty.toPFunctorNE : NonEmptyList Ty → PFunctor.{0, 0}
  | ⟨a, rest⟩ => match rest with
    | [] => Ty.toPFunctor a
    | _ :: _ => PFunctor.prod (Ty.toPFunctor a) (Ty.toPFunctorFields rest)

/-- The fields of a record, as a tuple (`Ty.toPFunctorFields`): `⟨a, b, []⟩` is `a × b`. -/
@[reducible] def Ty.toPFunctorRecord : LeanRecordSchema Ty → PFunctor.{0, 0}
  | ⟨a, b, rest⟩ => PFunctor.prod (Ty.toPFunctor a) (match rest with
    | [] => Ty.toPFunctor b
    | _ :: _ => PFunctor.prod (Ty.toPFunctor b) (Ty.toPFunctorFields rest))

/-- The fields of a constructor, as a tuple nested to the right **without** a trailing
    `PUnit`: `[]` is `PUnit`, `[a]` is `a`, `[a, b]` is `a × b`, `[a, b, c]` is
    `a × (b × c)`. -/
@[reducible] def Ty.toPFunctorFields : List Ty → PFunctor.{0, 0}
  | [] => PFunctor.const PUnit
  | a :: rest => match rest with
    | [] => Ty.toPFunctor a
    | _ :: _ => PFunctor.prod (Ty.toPFunctor a) (Ty.toPFunctorFields rest)

/-- The product of the containers of a list of types, in order, closed by `PUnit`: the
    shape of an environment, where extending by one entry must be one more pair. -/
@[reducible] def Ty.toPFunctorList : List Ty → PFunctor.{0, 0}
  | [] => PFunctor.const PUnit
  | τ :: ts => PFunctor.prod (Ty.toPFunctor τ) (Ty.toPFunctorList ts)

/-- The container of the fields of constructor number `t` of a tagged union; out of range
    it is empty. -/
@[reducible] def Ty.toPFunctorAt : LeanTaggedUnionSchema Ty → Nat → PFunctor.{0, 0}
  | .payloadFirst fields _ _, 0 => Ty.toPFunctorNE fields
  | .payloadFirst _ next _, 1 => Ty.toPFunctorFields next
  | .payloadFirst _ _ rest, n + 2 => Ty.toPFunctorAtList rest n
  | .skip _, 0 => PFunctor.const PUnit
  | .skip rest, n + 1 => Ty.toPFunctorAtCP rest n

/-- `Ty.toPFunctorAt`, on the constructors that follow a field-less one. -/
@[reducible] def Ty.toPFunctorAtCP : CtorsWithPayload Ty → Nat → PFunctor.{0, 0}
  | .here fields _, 0 => Ty.toPFunctorNE fields
  | .here _ rest, n + 1 => Ty.toPFunctorAtList rest n
  | .skip _, 0 => PFunctor.const PUnit
  | .skip rest, n + 1 => Ty.toPFunctorAtCP rest n

/-- `Ty.toPFunctorAt`, on a plain list of constructors. -/
@[reducible] def Ty.toPFunctorAtList : List (List Ty) → Nat → PFunctor.{0, 0}
  | [], _ => PFunctor.const PEmpty
  | fs :: _, 0 => Ty.toPFunctorFields fs
  | _ :: rest, n + 1 => Ty.toPFunctorAtList rest n

/-- The container a type **written in the scope of a mutual family** describes: its values
    are the shapes, a hole is an occurrence `Ty.familyMember j`, and its target is `j`.
    A nested binder is closed, so it is a constant, as is `Ty.self`, which a family's scope
    does not have. -/
@[reducible] def Ty.toIPF : Ty → IPFunctor
  | .self => IPFunctor.const PUnit
  | .familyMember j => IPFunctor.hole j
  | .shape s => Ty.toIPFShape s
  | .recTaggedUnion l =>
      IPFunctor.const (PFunctor.mu (PFunctor.sigma (Fin l.length) (fun t => Ty.toPFunctorAt l t.val))).A
  | .recObject fs => IPFunctor.const (PFunctor.mu (Ty.toPFunctorRecord fs)).A
  | .recAlias b => IPFunctor.const (PFunctor.mu (Ty.toPFunctor b)).A
  | .mutualRecursiveFamily f => IPFunctor.const (FamW (Ty.toIPFFamily f) f.memberIdx)

/-- `Ty.toIPF`, on a node.  The domain of an arrow is a closed type. -/
@[reducible] def Ty.toIPFShape : TyShape Ty → IPFunctor
  | .prim p => IPFunctor.const p.denote
  | .fn a b => IPFunctor.pi (Ty.toPFunctor a).A (Ty.toIPF b)
  | .primCovariant c => Ty.toIPFCov c
  | .enum s => IPFunctor.const (Fin s.nOfConstructors)
  | .record fs => Ty.toIPFRecord fs
  | .taggedUnion l => IPFunctor.sigma (Fin l.length) (fun t => Ty.toIPFAt l t.val)

/-- `Ty.toIPF`, on an array, a thunk or a lazy value. -/
@[reducible] def Ty.toIPFCov : LeanPrimTyCovariant Ty → IPFunctor
  | .array a => IPFunctor.array (Ty.toIPF a)
  | .thunk a => Ty.toIPF a
  | .lazy a => Ty.toIPF a

/-- `Ty.toIPFFields`, on a list that has at least one entry. -/
@[reducible] def Ty.toIPFNE : NonEmptyList Ty → IPFunctor
  | ⟨a, rest⟩ => match rest with
    | [] => Ty.toIPF a
    | _ :: _ => IPFunctor.prod (Ty.toIPF a) (Ty.toIPFFields rest)

/-- `Ty.toIPFFields`, on the fields of a record. -/
@[reducible] def Ty.toIPFRecord : LeanRecordSchema Ty → IPFunctor
  | ⟨a, b, rest⟩ => IPFunctor.prod (Ty.toIPF a) (match rest with
    | [] => Ty.toIPF b
    | _ :: _ => IPFunctor.prod (Ty.toIPF b) (Ty.toIPFFields rest))

/-- The fields of a constructor, as a tuple without a trailing `PUnit`
    (see `Ty.toPFunctorFields`). -/
@[reducible] def Ty.toIPFFields : List Ty → IPFunctor
  | [] => IPFunctor.const PUnit
  | a :: rest => match rest with
    | [] => Ty.toIPF a
    | _ :: _ => IPFunctor.prod (Ty.toIPF a) (Ty.toIPFFields rest)

/-- The product of the containers of a list of types, in order, closed by `PUnit` (see
    `Ty.toPFunctorList`). -/
@[reducible] def Ty.toIPFList : List Ty → IPFunctor
  | [] => IPFunctor.const PUnit
  | τ :: ts => IPFunctor.prod (Ty.toIPF τ) (Ty.toIPFList ts)

/-- The container of the fields of constructor number `t`; out of range it is empty. -/
@[reducible] def Ty.toIPFAt : LeanTaggedUnionSchema Ty → Nat → IPFunctor
  | .payloadFirst fields _ _, 0 => Ty.toIPFNE fields
  | .payloadFirst _ next _, 1 => Ty.toIPFFields next
  | .payloadFirst _ _ rest, n + 2 => Ty.toIPFAtList rest n
  | .skip _, 0 => IPFunctor.const PUnit
  | .skip rest, n + 1 => Ty.toIPFAtCP rest n

/-- `Ty.toIPFAt`, on the constructors that follow a field-less one. -/
@[reducible] def Ty.toIPFAtCP : CtorsWithPayload Ty → Nat → IPFunctor
  | .here fields _, 0 => Ty.toIPFNE fields
  | .here _ rest, n + 1 => Ty.toIPFAtList rest n
  | .skip _, 0 => IPFunctor.const PUnit
  | .skip rest, n + 1 => Ty.toIPFAtCP rest n

/-- `Ty.toIPFAt`, on a plain list of constructors. -/
@[reducible] def Ty.toIPFAtList : List (List Ty) → Nat → IPFunctor
  | [], _ => IPFunctor.const PEmpty
  | fs :: _, 0 => Ty.toIPFFields fs
  | _ :: rest, n + 1 => Ty.toIPFAtList rest n

/-- The container of one member of a family: its constructors, its fields or its body. -/
@[reducible] def Ty.toIPFMember : LeanFamMemberSchema Ty → IPFunctor
  | .ctors l => IPFunctor.sigma (Fin l.length) (fun t => Ty.toIPFAt l t.val)
  | .record fs => Ty.toIPFRecord fs
  | .alias b => Ty.toIPF b

/-- The containers of a list of members, in order. -/
@[reducible] def Ty.toIPFMemberList : List (LeanFamMemberSchema Ty) → List IPFunctor
  | [] => []
  | m :: ms => Ty.toIPFMember m :: Ty.toIPFMemberList ms

/-- The containers of the members of a family, in declaration order
    (`LeanScript.Ty.toIPFFamily_eq` says it is `f.members.map Ty.toIPFMember`). -/
@[reducible] def Ty.toIPFFamily : LeanMutualRecFamily Ty → List IPFunctor
  | .selectedThenMore before current next after =>
      Ty.toIPFMemberList before ++ Ty.toIPFMember current :: Ty.toIPFMember next ::
        Ty.toIPFMemberList after
  | .selectedLast first before current =>
      Ty.toIPFMember first :: (Ty.toIPFMemberList before ++ [Ty.toIPFMember current])

end

/-- The Lean type of the values of a type of the language: the shapes of its container. -/
@[reducible] def Ty.Den (t : Ty) : Type := (Ty.toPFunctor t).A

/-- `Ty.Den`, on a node. -/
@[reducible] def Ty.DenShape (s : TyShape Ty) : Type := (Ty.toPFunctorShape s).A

/-- `Ty.Den`, on an array, a thunk or a lazy value.  A delay denotes the value it stands
    for: a `Term` is a total function of its environment, so forcing it twice cannot give
    two answers, and memoisation is invisible here. -/
@[reducible] def Ty.DenCov (c : LeanPrimTyCovariant Ty) : Type := (Ty.toPFunctorCov c).A

/-- `Ty.DenFields`, on a list that has at least one entry. -/
@[reducible] def Ty.DenNE (xs : NonEmptyList Ty) : Type := (Ty.toPFunctorNE xs).A

/-- `Ty.DenFields`, on the fields of a record — of which there are at least two. -/
@[reducible] def Ty.DenRecord (fs : LeanRecordSchema Ty) : Type := (Ty.toPFunctorRecord fs).A

/-- The fields of a constructor or a record, as a tuple: `PUnit` for none, the field
    itself for one, and `Ty.Den a × Ty.Den b` — **not** `Ty.Den a × (Ty.Den b × PUnit)` —
    for two.  `Ty.DenFields.toList` and `Ty.DenFields.ofList` convert to and from
    `Ty.DenList`, the environment-shaped product. -/
@[reducible] def Ty.DenFields (ts : List Ty) : Type := (Ty.toPFunctorFields ts).A

/-- The product of the denotations of a list of types, in order, closed by `PUnit`: an
    environment, the arguments of a call.  Extending it by one entry is one more pair,
    which is what an environment needs; the values of a record or a constructor are held
    as `Ty.DenFields` instead. -/
@[reducible] def Ty.DenList (ts : List Ty) : Type := (Ty.toPFunctorList ts).A

/-- A tuple of fields, as an environment-shaped product. -/
def Ty.DenFields.toList : (ts : List Ty) → Ty.DenFields ts → Ty.DenList ts
  | [], _ => PUnit.unit
  | [_], x => (x, PUnit.unit)
  | _ :: b :: bs, x => (x.1, Ty.DenFields.toList (b :: bs) x.2)

/-- An environment-shaped product, as a tuple of fields. -/
def Ty.DenFields.ofList : (ts : List Ty) → Ty.DenList ts → Ty.DenFields ts
  | [], _ => PUnit.unit
  | [_], x => x.1
  | _ :: b :: bs, x => (x.1, Ty.DenFields.ofList (b :: bs) x.2)

@[simp] theorem Ty.DenFields.toList_ofList :
    ∀ (ts : List Ty) (x : Ty.DenList ts), Ty.DenFields.toList ts (Ty.DenFields.ofList ts x) = x
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: b :: bs, x => by
      show (x.1, Ty.DenFields.toList (b :: bs) (Ty.DenFields.ofList (b :: bs) x.2)) = x
      rw [Ty.DenFields.toList_ofList]

@[simp] theorem Ty.DenFields.ofList_toList :
    ∀ (ts : List Ty) (x : Ty.DenFields ts), Ty.DenFields.ofList ts (Ty.DenFields.toList ts x) = x
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: b :: bs, x => by
      show (x.1, Ty.DenFields.ofList (b :: bs) (Ty.DenFields.toList (b :: bs) x.2)) = x
      rw [Ty.DenFields.ofList_toList]

/-! ### Shapes of fields, as shapes of an environment

The fold of a recursive type reads a node's fields one at a time, as an environment is
read, so it sees them as a shape of `Ty.toPFunctorList` (resp. `Ty.toIPFList`); a node
holds them as a shape of `Ty.toPFunctorFields` (resp. `Ty.toIPFFields`).  These are the
conversions. -/

/-- A shape of the fields of a constructor, as a shape of the environment-shaped product. -/
def Ty.fieldsObjToList {X : Type} : (ts : List Ty) → (Ty.toPFunctorFields ts).Obj X →
    (Ty.toPFunctorList ts).Obj X
  | [], _ => ⟨PUnit.unit, fun p => PEmpty.elim p⟩
  | _ :: as, x => match as, x with
    | [], x => PFunctor.Obj.pair x ⟨PUnit.unit, fun p => PEmpty.elim p⟩
    | b :: bs, x => PFunctor.Obj.pair x.prodFst (Ty.fieldsObjToList (b :: bs) x.prodSnd)

/-- `Ty.fieldsObjToList`, on the fields of a constructor that has at least one. -/
def Ty.neObjToList {X : Type} : (xs : NonEmptyList Ty) → (Ty.toPFunctorNE xs).Obj X →
    (Ty.toPFunctorList xs.toList).Obj X
  | ⟨a, as⟩, x => Ty.fieldsObjToList (a :: as) x

theorem PFunctor.Obj.map_pair {c d : PFunctor.{0, 0}} {X Y : Type} (g : X → Y) (x : c.Obj X)
    (y : d.Obj X) :
    PFunctor.map _ g (PFunctor.Obj.pair x y) =
      PFunctor.Obj.pair (PFunctor.map _ g x) (PFunctor.map _ g y) := by
  obtain ⟨a, f⟩ := x
  obtain ⟨b, h⟩ := y
  exact congrArg (Sigma.mk _) (funext fun | .inl _ => rfl | .inr _ => rfl)

theorem PFunctor.Obj.map_const {A X Y : Type} (g : X → Y) (a : A) :
    PFunctor.map (PFunctor.const A) g ⟨a, fun p => PEmpty.elim p⟩ = ⟨a, fun p => PEmpty.elim p⟩ :=
  congrArg (Sigma.mk a) (funext fun p => PEmpty.elim p)

/-- Converting a shape of fields commutes with changing what its holes hold. -/
theorem Ty.fieldsObjToList_map {X Y : Type} (g : X → Y) :
    ∀ (ts : List Ty) (x : (Ty.toPFunctorFields ts).Obj X),
      PFunctor.map _ g (Ty.fieldsObjToList ts x) =
        Ty.fieldsObjToList ts (PFunctor.map _ g x)
  | [], _ => PFunctor.Obj.map_const g _
  | [_], x => by
      show PFunctor.map _ g (PFunctor.Obj.pair x _) = PFunctor.Obj.pair (PFunctor.map _ g x) _
      rw [PFunctor.Obj.map_pair, PFunctor.Obj.map_const]
  | a :: b :: bs, x => by
      show PFunctor.map _ g (PFunctor.Obj.pair x.prodFst (Ty.fieldsObjToList (b :: bs) x.prodSnd)) =
        PFunctor.Obj.pair (PFunctor.map _ g x).prodFst
          (Ty.fieldsObjToList (b :: bs) (PFunctor.map _ g x).prodSnd)
      rw [PFunctor.Obj.map_pair, Ty.fieldsObjToList_map g (b :: bs)]
      rfl

theorem Ty.neObjToList_map {X Y : Type} (g : X → Y) :
    ∀ (xs : NonEmptyList Ty) (x : (Ty.toPFunctorNE xs).Obj X),
      PFunctor.map _ g (Ty.neObjToList xs x) = Ty.neObjToList xs (PFunctor.map _ g x)
  | ⟨a, as⟩, x => Ty.fieldsObjToList_map g (a :: as) x

/-- `Ty.fieldsObjToList`, for a mutual family's containers. -/
def Ty.fieldsIPFObjToList {X : Nat → Type} : (ts : List Ty) → (Ty.toIPFFields ts).Obj X →
    (Ty.toIPFList ts).Obj X
  | [], _ => ⟨PUnit.unit, fun p => PEmpty.elim p⟩
  | _ :: as, x => match as, x with
    | [], x => IPFunctor.Obj.pair x ⟨PUnit.unit, fun p => PEmpty.elim p⟩
    | b :: bs, x => IPFunctor.Obj.pair x.prodFst (Ty.fieldsIPFObjToList (b :: bs) x.prodSnd)

/-- `Ty.fieldsIPFObjToList`, on the fields of a constructor that has at least one. -/
def Ty.neIPFObjToList {X : Nat → Type} : (xs : NonEmptyList Ty) → (Ty.toIPFNE xs).Obj X →
    (Ty.toIPFList xs.toList).Obj X
  | ⟨a, as⟩, x => Ty.fieldsIPFObjToList (a :: as) x

/-- `Ty.fieldsIPFObjToList`, on the fields of a record. -/
def Ty.recordIPFObjToList {X : Nat → Type} : (fs : LeanRecordSchema Ty) →
    (Ty.toIPFRecord fs).Obj X → (Ty.toIPFList fs.toList).Obj X
  | ⟨a, b, rest⟩, x => Ty.fieldsIPFObjToList (a :: b :: rest) x

/-- The fields of constructor number `t` of a tagged union, as a product.  Out of range
    it is `PEmpty`, which is what makes a dispatch on a union exhaustive without a
    bound. -/
@[reducible] def Ty.DenAt (l : LeanTaggedUnionSchema Ty) (t : Nat) : Type :=
  (Ty.toPFunctorAt l t).A

/-- `Ty.DenAt`, on the constructors that follow a field-less one. -/
@[reducible] def Ty.DenAtCP (c : CtorsWithPayload Ty) (t : Nat) : Type := (Ty.toPFunctorAtCP c t).A

/-- `Ty.DenAt`, on a plain list of constructors. -/
@[reducible] def Ty.DenAtList (cs : List (List Ty)) (t : Nat) : Type :=
  (Ty.toPFunctorAtList cs t).A

/-- The values of a tagged union: a constructor number, with exactly that constructor's
    fields.  There is no way to build one whose tag is out of range, and no way to read a
    field of a constructor other than the one the value holds. -/
abbrev Ty.DenTU (l : LeanTaggedUnionSchema Ty) : Type :=
  (t : Fin l.length) × Ty.DenAt l t.val

/-! ## The fields of a constructor, named by number

`LeanScript.Term.taggedUnion_mk` and `LeanScript.TaggedUnionSomeCases` name a constructor
by a number `t` with a proof `t < l.length`, and speak of its fields as
`Ty.DenFields (l.get t ht)`; a value holds them as `Ty.DenAt l t`.  The two are the same
type — that is `Ty.denAt_eq` — and `Ty.DenTU.mk` and `Ty.DenTU.field?` are the two
directions of that identification. -/

/-- The fields of a constructor that has at least one are the product of their
    denotations.  This is not definitional — `Ty.DenNE` is a case analysis on the schema,
    and a schema in hand is a variable rather than a pair — so an evaluator that has a
    `Ty.DenNE` and wants an environment `cast`s along it. -/
theorem Ty.denNE_eq (xs : NonEmptyList Ty) : Ty.DenNE xs = Ty.DenFields xs.toList := by
  cases xs; rfl

/-- The fields of a record are the product of their denotations, in declaration order. -/
theorem Ty.denRecord_eq (fs : LeanRecordSchema Ty) :
    Ty.DenRecord fs = Ty.DenFields fs.toList := by
  cases fs; rfl

theorem Ty.denAtList_eq : ∀ (l : List (List Ty)) (t : Nat) (ht : t < l.length),
    Ty.DenAtList l t = Ty.DenFields l[t]
  | [], _, ht => absurd ht (by simp)
  | _ :: _, 0, _ => rfl
  | _ :: rest, n + 1, ht => Ty.denAtList_eq rest n (by simpa using ht)

theorem Ty.denAtCP_eq : ∀ (c : CtorsWithPayload Ty) (t : Nat) (ht : t < c.toList.length),
    Ty.DenAtCP c t = Ty.DenFields c.toList[t]
  | .here fields _, 0, _ => by cases fields; rfl
  | .here _ rest, n + 1, ht =>
      Ty.denAtList_eq rest n (by simpa [CtorsWithPayload.toList] using ht)
  | .skip _, 0, _ => rfl
  | .skip rest, n + 1, ht =>
      Ty.denAtCP_eq rest n (by simpa [CtorsWithPayload.toList] using ht)

theorem Ty.denAt_eq : ∀ (l : LeanTaggedUnionSchema Ty) (t : Nat) (ht : t < l.length),
    Ty.DenAt l t = Ty.DenFields (l.get t ht)
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
    (fields : Ty.DenFields (l.get t ht)) : Ty.DenTU l :=
  ⟨⟨t, ht⟩, cast (Ty.denAt_eq l t ht).symm fields⟩

/-- The fields of a value of a tagged union **if** it is the value of constructor `t`,
    and nothing if it is the value of another constructor. -/
def Ty.DenTU.field? {l : LeanTaggedUnionSchema Ty} (t : Nat) (ht : t < l.length)
    (v : Ty.DenTU l) : Option (Ty.DenFields (l.get t ht)) :=
  if h : v.1.val = t then
    some (cast (by subst h; exact Ty.denAt_eq l _ ht) v.2)
  else
    none

/-- Reading the fields of the constructor a value was built with gives them back. -/
theorem Ty.DenTU.field?_mk {l : LeanTaggedUnionSchema Ty} (t : Nat) (ht : t < l.length)
    (fields : Ty.DenFields (l.get t ht)) :
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

/-- The fields of a constructor or a record of types, as a tuple (see `Ty.DenFields`). -/
@[reducible] def TyWf.DenFields (ts : List TyWf) : Type := Ty.DenFields (ts.map TyWf.toTy)

/-- A tuple of fields, as an environment-shaped product. -/
abbrev TyWf.DenFields.toList {ts : List TyWf} : TyWf.DenFields ts → TyWf.DenList ts :=
  Ty.DenFields.toList (ts.map TyWf.toTy)

/-- An environment-shaped product, as a tuple of fields. -/
abbrev TyWf.DenFields.ofList {ts : List TyWf} : TyWf.DenList ts → TyWf.DenFields ts :=
  Ty.DenFields.ofList (ts.map TyWf.toTy)

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
    (fields : TyWf.DenFields (l.get t ht)) : TyWf.DenTU l :=
  Ty.DenTU.mk t (by simpa using ht)
    (cast (by rw [LeanTaggedUnionSchema.get_map]) fields)

/-- The fields of a value of a tagged union **if** it is the value of constructor `t`,
    and nothing if it is the value of another constructor. -/
def TyWf.DenTU.field? {l : LeanTaggedUnionSchema TyWf} (t : Nat) (ht : t < l.length)
    (v : TyWf.DenTU l) : Option (TyWf.DenFields (l.get t ht)) :=
  (Ty.DenTU.field? t (by simpa using ht) v).map
    (cast (by rw [LeanTaggedUnionSchema.get_map]))

/-- Reading the fields of the constructor a value was built with gives them back. -/
theorem TyWf.DenTU.field?_mk {l : LeanTaggedUnionSchema TyWf} (t : Nat)
    (ht : t < l.length) (fields : TyWf.DenFields (l.get t ht)) :
    TyWf.DenTU.field? t ht (TyWf.DenTU.mk t ht fields) = some fields := by
  simp only [TyWf.DenTU.field?, TyWf.DenTU.mk, Ty.DenTU.field?_mk, Option.map_some]
  exact congrArg some ((cast_cast _ _ _).trans (cast_eq _ _))

end LeanScript

end
