module

public import LeanScript.Den.RecRoll

@[expose] public section

set_option autoImplicit false

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

namespace LeanScript

/-!
# The values of a recursive tagged union: introduction, elimination, fold

The introduction form `Ty.DenRec.mk`, the one-level elimination `Ty.DenRec.unfold`, their
round trips and `TyWf` versions, and the environment a branch of the fold binds.  Built on
`Ty.roll` / `Ty.unroll` from `LeanScript.Den.RecRoll`.
-/

namespace Ty

/-! ## Introduction and one-level elimination -/

/-- The nodes of a value of `recTaggedUnion L`: a constructor number, with that
    constructor's fields with their occurrences blanked out. -/
abbrev RecNode (L : LeanTaggedUnionSchema Ty) : Type := (t : Fin L.length) × Ty.DenAt L t.val

/-- The occurrences of the union among the fields of a node: one subtree each. -/
abbrev RecHole (L : LeanTaggedUnionSchema Ty) (p : RecNode L) : Type :=
  (Ty.toPFunctorAt L p.1.val).B p.2

/-- The unfolded constructors of `recTaggedUnion L`, as trees. -/
abbrev recUnfoldTy (L : LeanTaggedUnionSchema Ty) : LeanTaggedUnionSchema Ty :=
  substOccTU (.recTaggedUnion L) .familyMember L

/-- A value of `recTaggedUnion L` is a W-tree of its nodes. -/
example (L : LeanTaggedUnionSchema Ty) :
    Ty.Den (.recTaggedUnion L) = WType (RecHole L) := rfl

/-- **The introduction form** of a recursive tagged union: a constructor number with that
    constructor's *unfolded* fields. -/
def DenRec.mk (L : LeanTaggedUnionSchema Ty) (v : Ty.DenTU (recUnfoldTy L)) :
    Ty.Den (.recTaggedUnion L) :=
  let r := rollAt (.recTaggedUnion L) L v.1.val v.2
  WType.mk ⟨⟨v.1.val, length_substOccTU _ _ L ▸ v.1.isLt⟩, r.1⟩ r.2

/-- **One level of a value** of a recursive tagged union: its constructor number and its
    unfolded fields, which is what a dispatch on it binds. -/
def DenRec.unfold (L : LeanTaggedUnionSchema Ty) :
    Ty.Den (.recTaggedUnion L) → Ty.DenTU (recUnfoldTy L)
  | .mk ⟨t, s⟩ f =>
      ⟨⟨t.val, (length_substOccTU _ _ L).symm ▸ t.isLt⟩,
        unrollAt (.recTaggedUnion L) L t.val ⟨s, f⟩⟩

/-! ## The round trips -/

section
variable (R : Ty)

mutual

theorem unroll_roll : ∀ (a : Ty) (x : Ty.Den (substOcc R .familyMember a)),
    unroll R a (roll R a x) = x
  | .self, _ => rfl
  | .familyMember _, x => PEmpty.elim x
  | .shape s, x => unroll_rollShape s x
  | .recTaggedUnion _, _ => rfl
  | .recObject _, _ => rfl
  | .recAlias _, _ => rfl
  | .mutualRecursiveFamily _, _ => rfl

theorem unroll_rollShape : ∀ (s : TyShape Ty)
    (x : Ty.Den (.shape (substOccShape R .familyMember s))),
    unrollShape R s (rollShape R s x) = x
  | .prim _, _ => rfl
  | .fn _ b, f => funext fun y => unroll_roll b (f y)
  | .primCovariant c, x => unroll_rollCov c x
  | .enum _, _ => rfl
  | .record ⟨a, b, []⟩, ⟨x, y⟩ => by
      show (unroll R a (roll R a x), unroll R b (roll R b y)) = _
      rw [unroll_roll a x, unroll_roll b y]
      rfl
  | .record ⟨a, b, c :: cs⟩, ⟨x, y, zs⟩ => by
      show (unroll R a (roll R a x), unroll R b (roll R b y),
        unrollFields R (c :: cs) (rollFields R (c :: cs) zs)) = _
      rw [unroll_roll a x, unroll_roll b y, unroll_rollFields (c :: cs) zs]
      rfl
  | .taggedUnion l, ⟨t, v⟩ => by
      show (⟨⟨t.val, _⟩, unrollAt R l t.val (rollAt R l t.val v)⟩ :
        Ty.Den (.shape (substOccShape R .familyMember (.taggedUnion l)))) = _
      rw [unroll_rollAt l t.val v]

theorem unroll_rollCov : ∀ (c : LeanPrimTyCovariant Ty)
    (x : Ty.Den (.primCovariant (substOccCov R .familyMember c))),
    unrollCov R c (rollCov R c x) = x
  | .array a, xs => PFunctor.Obj.toArray_ofArray _ _ (fun x => unroll_roll a x) xs
  | .thunk a, x => unroll_roll a x
  | .lazy a, x => unroll_roll a x

theorem unroll_rollFields : ∀ (ts : List Ty) (x : Ty.DenFields (substOccList R .familyMember ts)),
    unrollFields R ts (rollFields R ts x) = x
  | [], _ => rfl
  | [a], x => unroll_roll a x
  | a :: b :: bs, ⟨x, xs⟩ => by
      show (unroll R a (roll R a x), unrollFields R (b :: bs) (rollFields R (b :: bs) xs)) = _
      rw [unroll_roll a x, unroll_rollFields (b :: bs) xs]

theorem unroll_rollNE : ∀ (xs : NonEmptyList Ty) (x : Ty.DenNE (substOccNE R .familyMember xs)),
    unrollNE R xs (rollNE R xs x) = x
  | ⟨a, []⟩, x => unroll_roll a x
  | ⟨a, b :: bs⟩, ⟨x, xs⟩ => by
      show (unroll R a (roll R a x), unrollFields R (b :: bs) (rollFields R (b :: bs) xs)) = _
      rw [unroll_roll a x, unroll_rollFields (b :: bs) xs]

theorem unroll_rollAt : ∀ (l : LeanTaggedUnionSchema Ty) (t : Nat)
    (v : Ty.DenAt (substOccTU R .familyMember l) t),
    unrollAt R l t (rollAt R l t v) = v
  | .payloadFirst f _ _, 0, v => unroll_rollNE f v
  | .payloadFirst _ next _, 1, v => unroll_rollFields next v
  | .payloadFirst _ _ rest, n + 2, v => unroll_rollAtList rest n v
  | .skip _, 0, _ => rfl
  | .skip rest, n + 1, v => unroll_rollAtCP rest n v

theorem unroll_rollAtCP : ∀ (c : CtorsWithPayload Ty) (t : Nat)
    (v : Ty.DenAtCP (substOccCP R .familyMember c) t),
    unrollAtCP R c t (rollAtCP R c t v) = v
  | .here f _, 0, v => unroll_rollNE f v
  | .here _ rest, n + 1, v => unroll_rollAtList rest n v
  | .skip _, 0, _ => rfl
  | .skip rest, n + 1, v => unroll_rollAtCP rest n v

theorem unroll_rollAtList : ∀ (cs : List (List Ty)) (t : Nat)
    (v : Ty.DenAtList (substOccCtors R .familyMember cs) t),
    unrollAtList R cs t (rollAtList R cs t v) = v
  | [], _, v => PEmpty.elim v
  | fs :: _, 0, v => unroll_rollFields fs v
  | _ :: rest, n + 1, v => unroll_rollAtList rest n v

end

mutual

theorem roll_unroll : ∀ (a : Ty) (x : (Ty.toPFunctor a).Obj (Ty.Den R)), roll R a (unroll R a x) = x
  | .self, _ => rfl
  | .familyMember _, x => PEmpty.elim x.1
  | .shape s, x => roll_unrollShape s x
  | .recTaggedUnion _, ⟨s, f⟩ => PFunctor.Obj.const_eta s f
  | .recObject _, ⟨s, f⟩ => PFunctor.Obj.const_eta s f
  | .recAlias _, ⟨s, f⟩ => PFunctor.Obj.const_eta s f
  | .mutualRecursiveFamily _, ⟨s, f⟩ => PFunctor.Obj.const_eta s f

theorem roll_unrollShape : ∀ (s : TyShape Ty) (x : (Ty.toPFunctorShape s).Obj (Ty.Den R)),
    rollShape R s (unrollShape R s x) = x
  | .prim _, ⟨s, f⟩ => PFunctor.Obj.const_eta s f
  | .fn a b, x => by
      revert x
      show ∀ x : (PFunctor.pi (Ty.toPFunctor a).A (Ty.toPFunctor b)).Obj (Ty.Den R),
        PFunctor.Obj.ofPi (fun y => roll R b (unroll R b ⟨x.1 y, fun p => x.2 ⟨y, p⟩⟩)) = x
      intro ⟨s, f⟩
      have hb : (fun y => roll R b (unroll R b ⟨s y, fun p => f ⟨y, p⟩⟩))
          = fun y => ⟨s y, fun p => f ⟨y, p⟩⟩ := funext fun y => roll_unroll b _
      show PFunctor.Obj.ofPi (fun y => roll R b (unroll R b ⟨s y, fun p => f ⟨y, p⟩⟩)) = _
      rw [hb]
      rfl
  | .primCovariant c, x => roll_unrollCov c x
  | .enum _, ⟨s, f⟩ => PFunctor.Obj.const_eta s f
  | .record ⟨a, b, []⟩, x => by
      revert x
      show ∀ x : (PFunctor.prod (Ty.toPFunctor a) (Ty.toPFunctor b)).Obj (Ty.Den R),
        PFunctor.Obj.pair (roll R a (unroll R a x.prodFst)) (roll R b (unroll R b x.prodSnd)) = x
      intro x
      rw [roll_unroll a, roll_unroll b, PFunctor.Obj.pair_prodFst_prodSnd]
  | .record ⟨a, b, c :: cs⟩, x => by
      revert x
      show ∀ x : (PFunctor.prod (Ty.toPFunctor a)
          (PFunctor.prod (Ty.toPFunctor b) (Ty.toPFunctorFields (c :: cs)))).Obj (Ty.Den R),
        PFunctor.Obj.pair (roll R a (unroll R a x.prodFst))
          (PFunctor.Obj.pair (roll R b (unroll R b x.prodSnd.prodFst))
            (rollFields R (c :: cs) (unrollFields R (c :: cs) x.prodSnd.prodSnd))) = x
      intro x
      rw [roll_unroll a, roll_unroll b, roll_unrollFields (c :: cs),
        PFunctor.Obj.pair_prodFst_prodSnd, PFunctor.Obj.pair_prodFst_prodSnd]
  | .taggedUnion l, x => by
      revert x
      show ∀ x : (PFunctor.sigma (Fin l.length) (fun t => Ty.toPFunctorAt l t.val)).Obj (Ty.Den R),
        rollShape R (.taggedUnion l) (unrollShape R (.taggedUnion l) x) = x
      intro ⟨⟨t, s⟩, f⟩
      exact congrArg (fun r : (Ty.toPFunctorAt l t.val).Obj (Ty.Den R) =>
        (⟨⟨t, r.1⟩, r.2⟩ :
          (PFunctor.sigma (Fin l.length) (fun t => Ty.toPFunctorAt l t.val)).Obj (Ty.Den R)))
        (roll_unrollAt l t.val ⟨s, f⟩)

theorem roll_unrollCov : ∀ (c : LeanPrimTyCovariant Ty) (x : (Ty.toPFunctorCov c).Obj (Ty.Den R)),
    rollCov R c (unrollCov R c x) = x
  | .array a, ⟨ss, g⟩ => PFunctor.Obj.ofArray_toArray _ _ (fun e => roll_unroll a e) ss g
  | .thunk a, x => roll_unroll a x
  | .lazy a, x => roll_unroll a x

theorem roll_unrollFields : ∀ (ts : List Ty) (x : (Ty.toPFunctorFields ts).Obj (Ty.Den R)),
    rollFields R ts (unrollFields R ts x) = x
  | [], ⟨s, f⟩ => PFunctor.Obj.const_eta s f
  | [a], x => roll_unroll a x
  | a :: b :: bs, x => by
      revert x
      show ∀ x : (PFunctor.prod (Ty.toPFunctor a) (Ty.toPFunctorFields (b :: bs))).Obj (Ty.Den R),
        PFunctor.Obj.pair (roll R a (unroll R a x.prodFst))
          (rollFields R (b :: bs) (unrollFields R (b :: bs) x.prodSnd)) = x
      intro x
      rw [roll_unroll a, roll_unrollFields (b :: bs), PFunctor.Obj.pair_prodFst_prodSnd]

theorem roll_unrollNE : ∀ (xs : NonEmptyList Ty) (x : (Ty.toPFunctorNE xs).Obj (Ty.Den R)),
    rollNE R xs (unrollNE R xs x) = x
  | ⟨a, []⟩, x => roll_unroll a x
  | ⟨a, b :: bs⟩, x => by
      revert x
      show ∀ x : (PFunctor.prod (Ty.toPFunctor a) (Ty.toPFunctorFields (b :: bs))).Obj (Ty.Den R),
        PFunctor.Obj.pair (roll R a (unroll R a x.prodFst))
          (rollFields R (b :: bs) (unrollFields R (b :: bs) x.prodSnd)) = x
      intro x
      rw [roll_unroll a, roll_unrollFields (b :: bs), PFunctor.Obj.pair_prodFst_prodSnd]

theorem roll_unrollAt : ∀ (l : LeanTaggedUnionSchema Ty) (t : Nat)
    (x : (Ty.toPFunctorAt l t).Obj (Ty.Den R)), rollAt R l t (unrollAt R l t x) = x
  | .payloadFirst f _ _, 0, x => roll_unrollNE f x
  | .payloadFirst _ next _, 1, x => roll_unrollFields next x
  | .payloadFirst _ _ rest, n + 2, x => roll_unrollAtList rest n x
  | .skip _, 0, ⟨s, f⟩ => PFunctor.Obj.const_eta s f
  | .skip rest, n + 1, x => roll_unrollAtCP rest n x

theorem roll_unrollAtCP : ∀ (c : CtorsWithPayload Ty) (t : Nat)
    (x : (Ty.toPFunctorAtCP c t).Obj (Ty.Den R)), rollAtCP R c t (unrollAtCP R c t x) = x
  | .here f _, 0, x => roll_unrollNE f x
  | .here _ rest, n + 1, x => roll_unrollAtList rest n x
  | .skip _, 0, ⟨s, f⟩ => PFunctor.Obj.const_eta s f
  | .skip rest, n + 1, x => roll_unrollAtCP rest n x

theorem roll_unrollAtList : ∀ (cs : List (List Ty)) (t : Nat)
    (x : (Ty.toPFunctorAtList cs t).Obj (Ty.Den R)), rollAtList R cs t (unrollAtList R cs t x) = x
  | [], _, x => PEmpty.elim x.1
  | fs :: _, 0, x => roll_unrollFields fs x
  | _ :: rest, n + 1, x => roll_unrollAtList rest n x

end

end

/-- Taking one level off a value built by the introduction form gives back its tag and
    its fields. -/
theorem DenRec.unfold_mk (L : LeanTaggedUnionSchema Ty) (v : Ty.DenTU (recUnfoldTy L)) :
    DenRec.unfold L (DenRec.mk L v) = v := by
  obtain ⟨⟨t, ht⟩, x⟩ := v
  show (⟨⟨t, _⟩, unrollAt (.recTaggedUnion L) L t (rollAt (.recTaggedUnion L) L t x)⟩ :
      Ty.DenTU (recUnfoldTy L)) = _
  rw [unroll_rollAt]

/-- Every value of a recursive tagged union is built by the introduction form. -/
theorem DenRec.mk_unfold (L : LeanTaggedUnionSchema Ty) (v : Ty.Den (.recTaggedUnion L)) :
    DenRec.mk L (DenRec.unfold L v) = v := by
  obtain ⟨⟨⟨t, ht⟩, s⟩, f⟩ := v
  have key : ∀ r : (Ty.toPFunctorAt L t).Obj (Ty.Den (.recTaggedUnion L)), r = ⟨s, f⟩ →
      (WType.mk ⟨⟨t, ht⟩, r.1⟩ r.2 : Ty.Den (.recTaggedUnion L)) = WType.mk ⟨⟨t, ht⟩, s⟩ f := by
    rintro r rfl; rfl
  exact key _ (roll_unrollAt (.recTaggedUnion L) L t ⟨s, f⟩)

/-- The values of a recursive tagged union **are** its unfolded constructors: the two
    directions `Ty.DenRec.mk` and `Ty.DenRec.unfold`, as a Mathlib `Equiv`. -/
def DenRec.equiv (L : LeanTaggedUnionSchema Ty) :
    Ty.DenTU (recUnfoldTy L) ≃ Ty.Den (.recTaggedUnion L) where
  toFun := DenRec.mk L
  invFun := DenRec.unfold L
  left_inv := DenRec.unfold_mk L
  right_inv := DenRec.mk_unfold L

end Ty

/-! ## At the level of bundles

`LeanScript.Term` is indexed by `TyWf`, and speaks of the unfolded constructors of a
recursive union as `TyWf.recTaggedUnionUnfold l hwf`, a schema of bundles.  Its trees are
the unfolded constructors of the trees — `TyWf.recTaggedUnionUnfold_map_toTy` — so the two
have the same values, and `TyWf.DenRec.mk` / `TyWf.DenRec.unfold` move along that one
equation.  On a concrete union the equation is between two closed types that are
definitionally equal, so the `cast` reduces and a concrete run still computes. -/

namespace TyWf

/-- The trees of the unfolded constructors of a recursive union of bundles are the
    unfolded constructors of its trees. -/
theorem recTaggedUnionUnfold_map_toTy (l : LeanTaggedUnionSchema (TyWfIn 1))
    (hwf : Ty.Wf (recTaggedUnionTy l)) :
    (recTaggedUnionUnfold l hwf).map TyWf.toTy = Ty.recUnfoldTy (l.map TyWfIn.toTy) := by
  simp only [Ty.recUnfoldTy, Ty.substOccTU_eq_map, recTaggedUnionUnfold]
  show (_ <$> _ <$> l) = (_ <$> _ <$> l)
  rw [Functor.map_map, Functor.map_map]
  rfl

/-- The values of the unfolded constructors, as bundles and as trees, are the same. -/
theorem denTU_recTaggedUnionUnfold (l : LeanTaggedUnionSchema (TyWfIn 1))
    (hwf : Ty.Wf (recTaggedUnionTy l)) :
    TyWf.DenTU (recTaggedUnionUnfold l hwf) = Ty.DenTU (Ty.recUnfoldTy (l.map TyWfIn.toTy)) :=
  congrArg Ty.DenTU (recTaggedUnionUnfold_map_toTy l hwf)

/-- **The introduction form** of a recursive tagged union of bundles, from a value of its
    unfolded constructors. -/
def DenRec.mk (l : LeanTaggedUnionSchema (TyWfIn 1)) (hwf : Ty.Wf (recTaggedUnionTy l))
    (v : TyWf.DenTU (recTaggedUnionUnfold l hwf)) : TyWf.Den (recTaggedUnion l hwf) :=
  Ty.DenRec.mk (l.map TyWfIn.toTy) (cast (denTU_recTaggedUnionUnfold l hwf) v)

/-- **One level of a value** of a recursive tagged union of bundles. -/
def DenRec.unfold (l : LeanTaggedUnionSchema (TyWfIn 1)) (hwf : Ty.Wf (recTaggedUnionTy l))
    (v : TyWf.Den (recTaggedUnion l hwf)) : TyWf.DenTU (recTaggedUnionUnfold l hwf) :=
  cast (denTU_recTaggedUnionUnfold l hwf).symm (Ty.DenRec.unfold (l.map TyWfIn.toTy) v)

theorem DenRec.unfold_mk (l : LeanTaggedUnionSchema (TyWfIn 1))
    (hwf : Ty.Wf (recTaggedUnionTy l)) (v : TyWf.DenTU (recTaggedUnionUnfold l hwf)) :
    DenRec.unfold l hwf (DenRec.mk l hwf v) = v := by
  simp only [DenRec.unfold, DenRec.mk, Ty.DenRec.unfold_mk, cast_cast, cast_eq]

theorem DenRec.mk_unfold (l : LeanTaggedUnionSchema (TyWfIn 1))
    (hwf : Ty.Wf (recTaggedUnionTy l)) (v : TyWf.Den (recTaggedUnion l hwf)) :
    DenRec.mk l hwf (DenRec.unfold l hwf v) = v := by
  simp only [DenRec.unfold, DenRec.mk, cast_cast, cast_eq]
  exact Ty.DenRec.mk_unfold _ v

/-- `TyWf.DenRec.mk` and `TyWf.DenRec.unfold`, as a Mathlib `Equiv`. -/
def DenRec.equiv (l : LeanTaggedUnionSchema (TyWfIn 1)) (hwf : Ty.Wf (recTaggedUnionTy l)) :
    TyWf.DenTU (recTaggedUnionUnfold l hwf) ≃ TyWf.Den (recTaggedUnion l hwf) where
  toFun := DenRec.mk l hwf
  invFun := DenRec.unfold l hwf
  left_inv := DenRec.unfold_mk l hwf
  right_inv := DenRec.mk_unfold l hwf

end TyWf

/-! ## What a branch of the fold binds

`LeanScript.Term.recTaggedUnion_rec` folds a value by `LeanScript.WType.memo`: the answer
at every node is computed once, bottom-up, and stored beside the node.  A branch of the
fold is then evaluated at a node whose subtrees are *memos*, and the environment it binds
(`LeanScript.TyWf.recBinders`) is read off them: a field that is literally `Ty.self` is
the subtree **and** the answer stored at it, and every other field is `Ty.unroll` of the
field with the subtrees put back in its holes. -/

/-- The trees of a schema of bundles. -/
abbrev recL (l : LeanTaggedUnionSchema (TyWfIn 1)) : LeanTaggedUnionSchema Ty :=
  l.map TyWfIn.toTy

/-- A value of `recTaggedUnion l` with the answer of a fold of motive `τ` at every node. -/
abbrev RecMemo (l : LeanTaggedUnionSchema (TyWfIn 1)) (τ : TyWf) : Type :=
  WType.Memo (Ty.RecNode (recL l)) (Ty.RecHole (recL l)) (TyWf.Den τ)

/-- A node of the fold of `recTaggedUnion l`, at a constructor with fields `fs`: the
    fields' shape, with the memo of a subtree in each hole. -/
abbrev RecFields (l : LeanTaggedUnionSchema (TyWfIn 1)) (τ : TyWf) (fs : List (TyWfIn 1)) :
    Type :=
  (Ty.toPFunctorList (fs.map TyWfIn.toTy)).Obj (RecMemo l τ)

/-- The value of a field that is not literally `Ty.self`: the field unrolled, with the
    subtrees put back in its holes. -/
def recBindField (l : LeanTaggedUnionSchema (TyWfIn 1)) (hwf : Ty.Wf (TyWf.recTaggedUnionTy l))
    (τ : TyWf) (a : TyWfIn 1) (e : (Ty.toPFunctor a.toTy).Obj (RecMemo l τ)) :
    TyWf.Den (TyWfIn.unfold (TyWf.recTaggedUnion l hwf) a) :=
  Ty.unroll (TyWf.recTaggedUnionTy l) a.toTy ⟨e.1, fun p => (e.2 p).tree⟩

/-- The environment a branch of the fold binds, at a constructor with fields `fs`. -/
def recBindEnv (l : LeanTaggedUnionSchema (TyWfIn 1)) (hwf : Ty.Wf (TyWf.recTaggedUnionTy l))
    (τ : TyWf) :
    (fs : List (TyWfIn 1)) → RecFields l τ fs →
      TyWf.DenList (TyWf.recBinders (TyWf.recTaggedUnion l hwf) τ fs)
  | [], _ => PUnit.unit
  | ⟨.self, _⟩ :: fs, e =>
      let m := e.prodFst.2 PUnit.unit
      (m.tree, m.answer, recBindEnv l hwf τ fs e.prodSnd)
  | ⟨.familyMember _, h⟩ :: _, _ =>
      -- A lone binder's payload holds no member occurrence (`Ty.WfIn 1` needs `2 ≤ 1`).
      absurd h Ty.not_wfIn_one_familyMember
  | ⟨.shape sh, h⟩ :: fs, e =>
      (recBindField l hwf τ ⟨.shape sh, h⟩ e.prodFst, recBindEnv l hwf τ fs e.prodSnd)
  | ⟨.recTaggedUnion l', h⟩ :: fs, e =>
      (recBindField l hwf τ ⟨.recTaggedUnion l', h⟩ e.prodFst, recBindEnv l hwf τ fs e.prodSnd)
  | ⟨.recObject r, h⟩ :: fs, e =>
      (recBindField l hwf τ ⟨.recObject r, h⟩ e.prodFst, recBindEnv l hwf τ fs e.prodSnd)
  | ⟨.recAlias b, h⟩ :: fs, e =>
      (recBindField l hwf τ ⟨.recAlias b, h⟩ e.prodFst, recBindEnv l hwf τ fs e.prodSnd)
  | ⟨.mutualRecursiveFamily f, h⟩ :: fs, e =>
      (recBindField l hwf τ ⟨.mutualRecursiveFamily f, h⟩ e.prodFst, recBindEnv l hwf τ fs e.prodSnd)

/-- The hole of a field that is `Ty.self`. -/
def selfHole : (a : Ty) → a = .self → (s : (Ty.toPFunctor a).A) → (Ty.toPFunctor a).B s
  | .self, _, _ => PUnit.unit

/-- The memo of the subtree at the occurrence a deeper look descends into. -/
def selfFieldMemo {l : LeanTaggedUnionSchema (TyWfIn 1)} {τ : TyWf} :
    {fs : List (TyWfIn 1)} → SelfField fs → RecFields l τ fs → RecMemo l τ
  | a :: _, .here h, e => e.prodFst.2 (selfHole a.toTy h e.prodFst.1)
  | _ :: _, .there sf, e => selfFieldMemo sf e.prodSnd

/-- The nodes a deeper look has dispatched on above the one it stands at, innermost
    first: for each, its fields' shape with the memo of a subtree in each hole. -/
def RecFrames (l : LeanTaggedUnionSchema (TyWfIn 1)) (τ : TyWf) :
    List (List (TyWfIn 1)) → Type
  | [] => PUnit
  | fs :: outer => RecFields l τ fs × RecFrames l τ outer

/-- No node above: the frames at the root of the fold. -/
def RecFrames.nil {l : LeanTaggedUnionSchema (TyWfIn 1)} {τ : TyWf} : RecFrames l τ [] :=
  PUnit.unit

/-- The memo of the subtree at an occurrence among the fields of a node above, which a
    deeper look (`LeanScript.FoldKBranch.deepOuter`) descends into. -/
def outerSelfFieldMemo {l : LeanTaggedUnionSchema (TyWfIn 1)} {τ : TyWf} :
    {outer : List (List (TyWfIn 1))} → OuterSelfField outer → RecFrames l τ outer →
      RecMemo l τ
  | _ :: _, .here sf, fr => selfFieldMemo sf fr.1
  | _ :: _, .there o, fr => outerSelfFieldMemo o fr.2

/-! ## Reading a list back

`List α` is the recursive tagged union `nil | cons α self` (its `LeanScriptTyWf`
instance, `LeanScript.TyWf.list`).  `Ty.DenRec.toList` reads a value of it back as a Lean
list, so a test can compare the result of a program with a Lean list, and
`Ty.DenRec.ofList` builds one from a Lean list, which is how an extern answering with a
list (`Array.toList`, `String.toList`) gives its value. -/

/-- A value of a list of `a`, as a Lean list: Mathlib's `WType.elim`, the plain fold of a
    W-tree, since the answer at a node needs only the answer at its subtree. -/
def Ty.DenRec.toList (a : Ty) : Ty.Den (.recTaggedUnion (Ty.listSchema a)) → List (Ty.Den a) :=
  WType.elim _ fun
    | ⟨⟨⟨0, _⟩, _⟩, _⟩ => []
    | ⟨⟨⟨1, _⟩, (x, _)⟩, ih⟩ => x :: ih (.inr PUnit.unit)

/-- A Lean list, as a value of a list of `a`: `[]` is the node `nil`, which has no
    subtree, and `x :: xs` is the node `cons` holding `x`, whose one subtree is `xs`. -/
def Ty.DenRec.ofList (a : Ty) : List (Ty.Den a) → Ty.Den (.recTaggedUnion (Ty.listSchema a))
  | [] => WType.mk ⟨⟨0, Nat.zero_lt_succ 1⟩, PUnit.unit⟩ (fun h => nomatch h)
  | x :: xs =>
      WType.mk ⟨⟨1, Nat.lt_succ_self 1⟩, (x, PUnit.unit)⟩
        (fun _ => Ty.DenRec.ofList a xs)

/-- Reading back a list built from a Lean list gives that list. -/
theorem Ty.DenRec.toList_ofList (a : Ty) (xs : List (Ty.Den a)) :
    Ty.DenRec.toList a (Ty.DenRec.ofList a xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (x :: ·) ih

end LeanScript

end
