module

public import LeanScript.Den.Container

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
