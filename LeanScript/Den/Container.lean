module

public import LeanScript.Ty.TyWfIn
public import LeanScript.Den.PFunctor
public import LeanScript.Den.IPFunctor

@[expose] public section

set_option autoImplicit false

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

namespace LeanScript

/-!
# The container of a type of the language, and `Ty.Den`

`Ty.toPFunctor` (and `Ty.toIPF`, for the scope of a mutual family) and the
denotations `Ty.Den`, `Ty.DenFields`, `Ty.DenList` defined as its shapes.  See
`LeanScript.Den` for the overview.
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

end LeanScript

end
