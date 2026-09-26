module

public import LeanScript.Den
public import LeanScript.Expr.SelfField
public import LeanScript.Ty.Traversable

@[expose] public section

set_option autoImplicit false

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

namespace LeanScript

/-!
# The values of a recursive tagged union

`Ty.Den (.recTaggedUnion L)` is the W-tree of the container of `L`'s constructors
(`LeanScript.Ty.toPFunctor`): a node is a constructor number with that constructor's fields
**with the occurrences of the union blanked out**, and one subtree per occurrence.  This
module is the bridge between that and what a term of the language sees — the constructor's
fields *unfolded*, where an occurrence of the union is a value of the union again:

* `Ty.roll` / `Ty.unroll`: a value of an unfolded field is a shape of the payload with a
  value of the binder in each hole, and back.  Neither needs a `cast`: substitution
  leaves the domain of an arrow alone (`LeanScript.Ty.substOccShape`), so the domain of an
  unfolded arrow *is* the domain of the container.  They are mutually inverse
  (`Ty.unroll_roll`, `Ty.roll_unroll`).
* `Ty.DenRec.mk` / `Ty.DenRec.unfold`: the introduction form and the one-level
  elimination of a recursive union, and their `TyWf` versions, which move along the one
  equation between the unfolded schema of bundles and the unfolded schema of trees.
* `recBindEnv`: the environment a branch of the fold binds, read off a node whose
  subtrees carry the fold's answers (`LeanScript.WType.memo`).
-/

namespace Ty

theorem length_substOccTU (s : Ty) (m : Nat → Ty) (l : LeanTaggedUnionSchema Ty) :
    (substOccTU s m l).length = l.length := by
  rw [substOccTU_eq_map, LeanTaggedUnionSchema.length_map]

/-! ## `roll`: an unfolded field is a shape with a value of the binder in each hole -/

section
variable (R : Ty)

mutual

/-- A value of the tree `a` unfolded at `R` is a shape of `a` with a value of `R` in each
    hole. -/
def roll : (a : Ty) → Ty.Den (substOcc R .familyMember a) → (Ty.toPFunctor a).Obj (Ty.Den R)
  | .self, x => ⟨PUnit.unit, fun _ => x⟩
  | .familyMember _, x => PEmpty.elim x
  | .shape s, x => rollShape s x
  | .recTaggedUnion _, x => ⟨x, fun p => PEmpty.elim p⟩
  | .recObject _, x => ⟨x, fun p => PEmpty.elim p⟩
  | .recAlias _, x => ⟨x, fun p => PEmpty.elim p⟩
  | .mutualRecursiveFamily _, x => ⟨x, fun p => PEmpty.elim p⟩

/-- `Ty.roll`, on a node. -/
def rollShape : (s : TyShape Ty) → Ty.Den (.shape (substOccShape R .familyMember s)) →
    (Ty.toPFunctorShape s).Obj (Ty.Den R)
  | .prim _, x => ⟨x, fun p => PEmpty.elim p⟩
  | .fn _ b, f => PFunctor.Obj.ofPi (fun y => roll b (f y))
  | .primCovariant c, x => rollCov c x
  | .enum _, x => ⟨x, fun p => PEmpty.elim p⟩
  | .record ⟨a, b, rest⟩, x =>
      PFunctor.Obj.pair (roll a x.1) (match rest, x.2 with
        | [], y => roll b y
        | c :: cs, y => PFunctor.Obj.pair (roll b y.1) (rollFields (c :: cs) y.2))
  | .taggedUnion l, ⟨t, v⟩ =>
      let r := rollAt l t.val v
      ⟨⟨⟨t.val, length_substOccTU R .familyMember l ▸ t.isLt⟩, r.1⟩, r.2⟩

/-- `Ty.roll`, on an array, a thunk or a lazy value. -/
def rollCov : (c : LeanPrimTyCovariant Ty) →
    Ty.Den (.primCovariant (substOccCov R .familyMember c)) → (Ty.toPFunctorCov c).Obj (Ty.Den R)
  | .array a, xs => PFunctor.Obj.ofArray (fun x => roll a x) xs
  | .thunk a, x => roll a x
  | .lazy a, x => roll a x

/-- `Ty.roll`, on the fields of a constructor. -/
def rollFields : (ts : List Ty) → Ty.DenFields (substOccList R .familyMember ts) →
    (Ty.toPFunctorFields ts).Obj (Ty.Den R)
  | [], _ => ⟨PUnit.unit, fun p => PEmpty.elim p⟩
  | a :: as, x => match as, x with
    | [], x => roll a x
    | b :: bs, x => PFunctor.Obj.pair (roll a x.1) (rollFields (b :: bs) x.2)

/-- `Ty.roll`, on the fields of a constructor that has at least one. -/
def rollNE : (xs : NonEmptyList Ty) → Ty.DenNE (substOccNE R .familyMember xs) →
    (Ty.toPFunctorNE xs).Obj (Ty.Den R)
  | ⟨a, as⟩, x => match as, x with
    | [], x => roll a x
    | b :: bs, x => PFunctor.Obj.pair (roll a x.1) (rollFields (b :: bs) x.2)

/-- `Ty.roll`, on the fields of constructor `t`. -/
def rollAt : (l : LeanTaggedUnionSchema Ty) → (t : Nat) →
    Ty.DenAt (substOccTU R .familyMember l) t → (Ty.toPFunctorAt l t).Obj (Ty.Den R)
  | .payloadFirst f _ _, 0, v => rollNE f v
  | .payloadFirst _ next _, 1, v => rollFields next v
  | .payloadFirst _ _ rest, n + 2, v => rollAtList rest n v
  | .skip _, 0, _ => ⟨PUnit.unit, fun p => PEmpty.elim p⟩
  | .skip rest, n + 1, v => rollAtCP rest n v

/-- `Ty.rollAt`, on the constructors that follow a field-less one. -/
def rollAtCP : (c : CtorsWithPayload Ty) → (t : Nat) →
    Ty.DenAtCP (substOccCP R .familyMember c) t → (Ty.toPFunctorAtCP c t).Obj (Ty.Den R)
  | .here f _, 0, v => rollNE f v
  | .here _ rest, n + 1, v => rollAtList rest n v
  | .skip _, 0, _ => ⟨PUnit.unit, fun p => PEmpty.elim p⟩
  | .skip rest, n + 1, v => rollAtCP rest n v

/-- `Ty.rollAt`, on a plain list of constructors. -/
def rollAtList : (cs : List (List Ty)) → (t : Nat) →
    Ty.DenAtList (substOccCtors R .familyMember cs) t → (Ty.toPFunctorAtList cs t).Obj (Ty.Den R)
  | [], _, v => PEmpty.elim v
  | fs :: _, 0, v => rollFields fs v
  | _ :: rest, n + 1, v => rollAtList rest n v

end

/-! ## `unroll`: the other direction -/

mutual

/-- A shape of `a` with a value of `R` in each hole is a value of `a` unfolded at `R`. -/
def unroll : (a : Ty) → (Ty.toPFunctor a).Obj (Ty.Den R) → Ty.Den (substOcc R .familyMember a)
  | .self, x => x.2 PUnit.unit
  | .familyMember _, x => PEmpty.elim x.1
  | .shape s, x => unrollShape s x
  | .recTaggedUnion _, x => x.1
  | .recObject _, x => x.1
  | .recAlias _, x => x.1
  | .mutualRecursiveFamily _, x => x.1

/-- `Ty.unroll`, on a node. -/
def unrollShape : (s : TyShape Ty) → (Ty.toPFunctorShape s).Obj (Ty.Den R) →
    Ty.Den (.shape (substOccShape R .familyMember s))
  | .prim _, x => x.1
  | .fn _ b, x => fun y => unroll b ⟨x.1 y, fun p => x.2 ⟨y, p⟩⟩
  | .primCovariant c, x => unrollCov c x
  | .enum _, x => x.1
  | .record ⟨a, b, rest⟩, x =>
      (unroll a x.prodFst, match rest, x.prodSnd with
        | [], y => unroll b y
        | c :: cs, y => (unroll b y.prodFst, unrollFields (c :: cs) y.prodSnd))
  | .taggedUnion l, x =>
      ⟨⟨x.1.1.val, (length_substOccTU R .familyMember l).symm ▸ x.1.1.isLt⟩,
        unrollAt l x.1.1.val ⟨x.1.2, x.2⟩⟩

/-- `Ty.unroll`, on an array, a thunk or a lazy value. -/
def unrollCov : (c : LeanPrimTyCovariant Ty) →
    (Ty.toPFunctorCov c).Obj (Ty.Den R) → Ty.Den (.primCovariant (substOccCov R .familyMember c))
  | .array a, x => PFunctor.Obj.toArray (fun y => unroll a y) x.1 x.2
  | .thunk a, x => unroll a x
  | .lazy a, x => unroll a x

/-- `Ty.unroll`, on the fields of a constructor. -/
def unrollFields : (ts : List Ty) → (Ty.toPFunctorFields ts).Obj (Ty.Den R) →
    Ty.DenFields (substOccList R .familyMember ts)
  | [], _ => PUnit.unit
  | a :: as, x => match as, x with
    | [], x => unroll a x
    | b :: bs, x => (unroll a x.prodFst, unrollFields (b :: bs) x.prodSnd)

/-- `Ty.unroll`, on the fields of a constructor that has at least one. -/
def unrollNE : (xs : NonEmptyList Ty) → (Ty.toPFunctorNE xs).Obj (Ty.Den R) →
    Ty.DenNE (substOccNE R .familyMember xs)
  | ⟨a, as⟩, x => match as, x with
    | [], x => unroll a x
    | b :: bs, x => (unroll a x.prodFst, unrollFields (b :: bs) x.prodSnd)

/-- `Ty.unroll`, on the fields of constructor `t`. -/
def unrollAt : (l : LeanTaggedUnionSchema Ty) → (t : Nat) →
    (Ty.toPFunctorAt l t).Obj (Ty.Den R) → Ty.DenAt (substOccTU R .familyMember l) t
  | .payloadFirst f _ _, 0, x => unrollNE f x
  | .payloadFirst _ next _, 1, x => unrollFields next x
  | .payloadFirst _ _ rest, n + 2, x => unrollAtList rest n x
  | .skip _, 0, _ => PUnit.unit
  | .skip rest, n + 1, x => unrollAtCP rest n x

/-- `Ty.unrollAt`, on the constructors that follow a field-less one. -/
def unrollAtCP : (c : CtorsWithPayload Ty) → (t : Nat) →
    (Ty.toPFunctorAtCP c t).Obj (Ty.Den R) → Ty.DenAtCP (substOccCP R .familyMember c) t
  | .here f _, 0, x => unrollNE f x
  | .here _ rest, n + 1, x => unrollAtList rest n x
  | .skip _, 0, _ => PUnit.unit
  | .skip rest, n + 1, x => unrollAtCP rest n x

/-- `Ty.unrollAt`, on a plain list of constructors. -/
def unrollAtList : (cs : List (List Ty)) → (t : Nat) →
    (Ty.toPFunctorAtList cs t).Obj (Ty.Den R) → Ty.DenAtList (substOccCtors R .familyMember cs) t
  | [], _, x => PEmpty.elim x.1
  | fs :: _, 0, x => unrollFields fs x
  | _ :: rest, n + 1, x => unrollAtList rest n x

end

end

end Ty

end LeanScript

end
